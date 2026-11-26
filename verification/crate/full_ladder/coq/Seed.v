From Coq Require Import ZArith List Bool Lia Ring.
From Curve25519.group Require Import CoordinateEncoding.
From Machine Require Import isa.Instructions isa.X86 isa.ProgramLayout execution.WordBounds.
From Curve25519 Require Import Field Radix51 Edwards.
From Curve25519.group Require Import PrimeField Affine Representation.
Import ListNotations. Local Open Scope nat_scope.

(* An aligned vector offset is expressed in 64-byte rows. RSP is the staged
   input and RBX is the output. Reads of RBX observe earlier seed stores. *)
Inductive op := Imm (wide:bool) (v:Z) | Broadcast (r:nat) | Vec (v:instruction)
 | ReadRow (d base row:nat) | AddRow (d a base row:nat) | StoreRow (base row src:nat).
Definition encode op := match op with
 | Imm w v=>op_bytes (Program [] []) (if w then MovAbsRax v else Mov32 0 v)
 | Broadcast r=>op_bytes (Program [] []) (BroadcastRax r)
 | Vec v=>Instructions.encode v
 | ReadRow r b i=>rm_memory 1 1 0x6f r 0 (Z.of_nat b) (64*Z.of_nat i)
 | AddRow r a b i=>rm_memory 1 1 0xd4 r a (Z.of_nat b) (64*Z.of_nat i)
 | StoreRow b i r=>rm_memory 1 1 0x7f r 0 (Z.of_nat b) (64*Z.of_nat i) end.

Definition bias i := (4*(radix-if Nat.eqb i 0 then 19 else 1))%Z.
Definition row i := [ReadRow 0 4 i; ReadRow 1 4 (5+i); Vec (2,Add 1 0)] ++
 (if Nat.eqb i 0 then [Vec (1,Add 1 8);ReadRow 3 4 15]
  else [Vec (1,Add 1 9);Vec (1,Add 1 4);Vec (2,Add 2 5);AddRow 3 6 4 (15+i)]) ++
 [Vec (1,Sub 1 0);Vec (4,Shr 1 51);Vec (5,Shr 2 51);Vec (6,Shr 3 51);
  Vec (1,And 1 10);Vec (2,And 2 10);Vec (3,And 3 10);
  StoreRow 3 i 1;StoreRow 3 (5+i) 2;StoreRow 3 (10+i) 3;StoreRow 3 (15+i) 7].
Definition code := [Imm true (bias 0);Broadcast 8;Imm true (bias 1);Broadcast 9;
 Imm true (radix-1);Broadcast 10;Vec (7,Xor 7 7)] ++ flat_map row (seq 0 5) ++
 [Imm false 19;Broadcast 0;Vec (4,Mul 4 0);Vec (5,Mul 5 0);Vec (6,Mul 6 0);
  AddRow 4 4 3 0;AddRow 5 5 3 5;AddRow 6 6 3 10;
  StoreRow 3 0 4;StoreRow 3 5 5;StoreRow 3 10 6].

Record lane := Lane { rax:Z; reg:nat->Z; out:nat->Z }.
Definition step (input:nat->Z) s op :=
 let set d v := Lane (rax s) (put (reg s) d v) (out s) in
 let load b := if Nat.eqb b 3 then out s else input in
 match op with
 | Imm _ v=>Lane v (reg s) (out s) | Broadcast r=>set r (rax s)
 | Vec (d,v)=>set d (bits (fun _ _=>0%Z) (reg s) d v)
 | ReadRow d b i=>set d (load b i)
 | AddRow d a b i=>set d (Arithmetic.vpaddq (reg s a) (load b i))
 | StoreRow _ i r=>Lane (rax s) (reg s) (put (out s) i (reg s r))
 end.
Definition execute input initial := fold_left (step input) code initial.

Local Open Scope Z_scope.
Definition raw (a:nat->Z) c i carry :=
 let m:=a i in let p:=a (5+i)%nat in
 match c with
 | O => Arithmetic.vpsubq (if Nat.eqb i 0 then Arithmetic.vpaddq p (bias i)
           else Arithmetic.vpaddq (Arithmetic.vpaddq p (bias i)) carry) m
 | S O => if Nat.eqb i 0 then Arithmetic.vpaddq p m else Arithmetic.vpaddq (Arithmetic.vpaddq p m) carry
 | _ => if Nat.eqb i 0 then a (15+i)%nat else Arithmetic.vpaddq carry (a (15+i)%nat) end.
Fixpoint carry a c i := match i with O=>0 | S j=>Shift.vpsrlq (raw a c j (carry a c j)) 51 end.
Definition low a c i := Logic.vpandq (raw a c i (carry a c i)) (radix-1).
Definition result a c i := if Nat.eqb i 0 then
 Arithmetic.vpaddq (Arithmetic.vpmullq (carry a c 5) 19) (low a c 0) else low a c i.
Definition bounded (a:nat->Z) := forall i,(i<20)%nat -> 0<=a i<2^52.
Definition column (a:nat->Z) c i := match c with O=> a (5+i)%nat+bias i-a i
 | S O=>a (5+i)%nat+a i | _=>a (15+i)%nat end.

Lemma routed a s c i : (c<3)%nat -> (i<5)%nat ->
 out (execute a s) (5*c+i)%nat=result a c i.
Proof. intros C I;destruct c as [|[|[|c]]];try lia;
 do 5 (destruct i as [|i];[reflexivity|]);lia. Qed.
Lemma zero_t a s i : (i<5)%nat -> out (execute a s) (15+i)%nat=0.
Proof. intro I;do 5(destruct i as [|i];[apply Z.lxor_nilpotent|]);lia. Qed.

Local Ltac input_bounds A i :=
 pose proof(A i ltac:(lia));pose proof(A (5+i)%nat ltac:(lia));
 pose proof(A (15+i)%nat ltac:(lia)).
Lemma raw_ok a c i : bounded a -> (i<5)%nat -> 0<=carry a c i<=8 ->
 raw a c i (carry a c i)=column a c i+carry a c i /\
 0<=column a c i+carry a c i<8*radix.
Proof.
 intros A I C;input_bounds A i;unfold raw,column,bias;
 destruct i as [|i];cbn [Nat.eqb carry] in *;destruct c as [|[|c]];
 unfold Arithmetic.vpaddq,Arithmetic.vpsubq,radix in *;
 repeat match goal with |- context [low64 ?x] => rewrite (low64_id x ltac:(unfold word64;lia)) end;split;lia.
Qed.
Lemma carry_bound a c i : bounded a -> (i<=5)%nat -> 0<=carry a c i<=8.
Proof.
 intros A;induction i as [|i IH];intro I;[cbn;lia|].
 destruct(raw_ok a c i A ltac:(lia) (IH ltac:(lia))) as [E B].
 cbn [carry];unfold Shift.vpsrlq;rewrite Z.shiftr_div_pow2 by lia;rewrite E.
 change (0<=(column a c i+carry a c i)/radix<=8).
 split;[apply Z.div_pos;unfold radix in *;lia|].
 assert ((column a c i+carry a c i)/radix<8) by (apply Z.div_lt_upper_bound;unfold radix in *;lia);lia.
Qed.
Lemma digit_law a c i : bounded a -> (i<5)%nat ->
 low a c i+radix*carry a c (S i)=column a c i+carry a c i /\ 0<=low a c i<radix.
Proof.
 intros A I;pose proof (raw_ok a c i A I (carry_bound a c i A ltac:(lia))) as [E _].
 unfold low,Logic.vpandq;change (radix-1) with (Z.ones 51);rewrite Z.land_ones by lia.
 cbn [carry];unfold Shift.vpsrlq;rewrite Z.shiftr_div_pow2 by lia;rewrite E.
 set (v:=column a c i+carry a c i). change (v mod radix + radix*(v/radix)=v /\ 0<=v mod radix<radix). split;[pose proof (Z.div_mod v radix ltac:(unfold radix;lia));lia|apply Z.mod_pos_bound;reflexivity].
Qed.
Lemma folded a c : bounded a -> result a c 0=19*carry a c 5+low a c 0.
Proof.
 intro A;pose proof(carry_bound a c 5 A ltac:(lia));destruct(digit_law a c 0 A ltac:(lia)) as [_ B].
 unfold result,Arithmetic.vpaddq,Arithmetic.vpmullq;cbn [Nat.eqb].
 repeat match goal with |- context [low64 ?x] => rewrite (low64_id x ltac:(unfold word64,radix in *;lia)) end;ring.
Qed.
Lemma seed_bound a c : bounded a -> loose (result a c).
Proof.
 intro A;apply ready_loose;intros i I;pose proof(carry_bound a c 5 A ltac:(lia));
 pose proof (proj2(digit_law a c i A I)) as B.
 destruct i;[rewrite folded by exact A|change (0<=low a c (S i)<=ready_bound)];
 unfold ready_bound,radix in *;lia.
Qed.
Definition seed_point (a:nat->Z) := Coordinates
 (limbs (fun i=>a (5+i)%nat)-limbs a) (limbs (fun i=>a (5+i)%nat)+limbs a)
 (limbs (fun i=>a (15+i)%nat)) 0.
Lemma seed_value a c : bounded a -> (c<3)%nat ->
 (limbs (result a c) mod prime = coordinate (seed_point a) c mod prime).
Proof.
 intros A C;pose proof (proj1(digit_law a c 0 A ltac:(lia))) as D0;
 pose proof (proj1(digit_law a c 1 A ltac:(lia))) as D1;
 pose proof (proj1(digit_law a c 2 A ltac:(lia))) as D2;
 pose proof (proj1(digit_law a c 3 A ltac:(lia))) as D3;
 pose proof (proj1(digit_law a c 4 A ltac:(lia))) as D4.
 unfold limbs at 1;rewrite folded by exact A.
 change (result a c 1) with (low a c 1);change (result a c 2) with (low a c 2);
 change (result a c 3) with (low a c 3);change (result a c 4) with (low a c 4).
 apply represents_mod.
 destruct c as [|[|[|c]]];try lia;
 [exists (4-carry a 0 5)|exists (-carry a 1 5)|exists (-carry a 2 5)];
 cbn [coordinate seed_point cx cy cz limbs column bias Nat.eqb Nat.add] in *;
 change (carry a 0 0) with 0 in *;change (carry a 1 0) with 0 in *;change (carry a 2 0) with 0 in *;
 unfold limbs,bias,radix,prime in *;cbn [Nat.eqb] in *;lia.
Qed.

Definition cache (a:nat->Z) := CachedCoordinates (limbs a)
 (limbs (fun i=>a (5+i)%nat)) (limbs (fun i=>a (10+i)%nat)) (Some (limbs (fun i=>a (15+i)%nat))).
Definition output_point a s := let f c:=limbs(fun i=>out (execute a s) (5*c+i)%nat) in
 Coordinates (f 0%nat) (f 1%nat) (f 2%nat) (f 3%nat).
Lemma seed_represents a s P : bounded a -> represents_cache (cache a) P ->
 represents_xyz (output_point a s) P.
Proof.
 intros B Cache.
 assert (E:forall c,(c<3)%nat -> residue(limbs(fun i=>out(execute a s)(5*c+i)%nat))=
   residue(coordinate(seed_point a)c)).
 { intros c C;rewrite (limbs_ext _ _ (fun i I=>routed a s c i C I));apply residue_eq,seed_value;assumption. }
 unfold represents_xyz,output_point;cbn [cx cy cz];rewrite !E by lia.
 exact (cache_seed_xyz _ _ _ _ _ Cache).
Qed.

(* Only these aligned, disjoint input/output views are projected by step.
   Reject every other base, out-of-range row, or hidden memory operand. *)
Definition valid op := match op with
 | Imm w v=>unsigned (if w then 64 else 32) v | Broadcast r=>Nat.ltb r 32
 | Vec ((_,Load _ _) as v) | Vec ((_,MaddMem _ _ _ _) as v)=>false
 | Vec v=>encodable v
 | ReadRow d b i=>Nat.ltb d 32 && Nat.eqb b 4 && Nat.ltb i 20
 | AddRow d a b i=>Nat.ltb d 32 && Nat.ltb a 32 && (Nat.eqb b 3 || Nat.eqb b 4) && Nat.ltb i 20
 | StoreRow b i r=>Nat.eqb b 3 && Nat.ltb i 20 && Nat.ltb r 32 end.
