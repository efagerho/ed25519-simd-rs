From Coq Require Import ZArith Lia Bool List Field.
From Curve25519.group Require Import CoordinateEncoding.
From Curve25519 Require DeferredCarry.
From Machine Require Import isa.X86 isa.Instructions isa.Logic isa.Arithmetic isa.Shift isa.IFMA execution.LinkedCalls memory.ByteMemory.
From Curve25519 Require Import Field Edwards Radix51.
From Curve25519.group Require Import PrimeField Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Import Operands.
From Curve25519 Require Import Radix51Digits.
From Ed25519Simd.Decode Require Import Scale Decode Kernels Program.
From Ed25519Simd.Dalek Require Import Masks.
From Ed25519Simd.DalekPostHash Require Import Caller.
Import ListNotations. Local Open Scope Z_scope.

(* Gather the three five-limb fields at positive table digit 8. The pointer
   row here is the key-table pointer row later supplied to the ladder. *)
Definition column s j c i := read_word (mem s)
 (read_word (mem s) (regs s 6%nat+8*Z.of_nat j)+table_disp c i).
Definition bias i := 1024*(radix-if Nat.eqb i 0 then 19 else 1).
Definition biased twice a b i :=
 vpsubq (vpaddq (if twice:bool then vpaddq (a i) (a i) else a i) (bias i)) (b i).
Definition equal_columns twice a b := high_test (Scale.reduced (biased twice a b)) 0.
Definition first s j := equal_columns false (column s j 1) (column s j 0).
Definition second s j := equal_columns true (column s j 0) (column s j 3).
Definition filter_keys s (eligible:nat->bool) j :=
 if reaches Filter FirstDifference (byte(first s)=?0) false KeysDone then eligible j
 else eligible j && negb (first s j && second s j).
Definition carry_code := flat_map (fun i=>[((10+i)%nat,Shr i 51);(i,And i 29)]) (seq 0 5)++
 [(0%nat,Madd false 14 28)]++map (fun i=>(i,Add i (9+i)%nat)) (seq 1 4).

Local Lemma exact_word n : 0<=n<2^64 -> low64 n=n.
Proof. intro N;unfold low64;rewrite Z.land_ones,Z.mod_small by lia;reflexivity. Qed.

Lemma equal_columns_ok twice a b : split_field a -> split_field b ->
 (equal_columns twice a b=true <->
  (if twice then (value a+value a)%fp else value a)=value b).
Proof.
 intros A B. set (k:=if twice then 2 else 1).
 set (d:=fun i=>k*a i+bias i-b i).
 assert (D:forall i,(i<5)%nat -> biased twice a b i=d i /\
   1018*radix <= d i <=1028*radix).
 { intros i I;specialize(A i I);specialize(B i I).
   unfold d,k,biased,bias;destruct twice,(Nat.eqb i 0);
   unfold vpaddq,vpsubq,radix,split in *;repeat multimatch goal with |- context[low64 ?n] => rewrite (exact_word n) by lia end;split;lia. }
 assert (C:forall i,(i<5)%nat -> 1018<=d i/radix<=1028).
 { intros i I;destruct(D i I) as [_ H];split;[apply Z.div_le_lower_bound|apply Z.div_le_upper_bound];unfold radix in *;lia. }
 assert (Step:forall i,(i<5)%nat -> Scale.reduced (biased twice a b) i=DeferredCarry.carry d i).
 { intros i I;unfold Scale.reduced,DeferredCarry.carry,vpandq,vpsrlq;
   rewrite (proj1(D _ I));change (radix-1) with (Z.ones 51).
   rewrite Z.land_ones by lia;change (2^51) with radix.
   pose proof(Z.mod_pos_bound (d i) radix ltac:(unfold radix;lia)).
   destruct i as [|i];[rewrite (proj1(D 4%nat ltac:(lia)))|rewrite (proj1(D i ltac:(lia)))];rewrite Z.shiftr_div_pow2 by lia;
     change (2^Z.of_nat 51) with radix.
   - specialize(C 4%nat ltac:(lia)). unfold madd52;rewrite !Z.land_ones by lia.
     rewrite (Z.mod_small (d 4%nat/radix)) by lia. change (19 mod 2^52) with 19.
     rewrite (Z.mod_small (_*19)) by lia. rewrite exact_word by (unfold radix in *;lia);ring.
   - specialize(C i ltac:(lia));unfold vpaddq;apply exact_word;unfold radix in *;lia. }
 set (h:=Scale.reduced (biased twice a b)).
 assert (BD:bounded h).
 { intros i I;unfold h;rewrite Step by exact I;unfold DeferredCarry.carry.
   pose proof(Z.mod_pos_bound (d i) radix ltac:(unfold radix;lia)).
   destruct i as [|i];[specialize(C 4%nat ltac:(lia))|specialize(C i ltac:(lia))];lia. }
 assert (Pos:1<pack h).
 { apply positive_from_low; [exact BD|].
   replace (h 0%nat) with (d 0%nat mod radix+19*(d 4%nat/radix)) by (apply eq_sym,Step;lia).
   pose proof(Z.mod_pos_bound (d 0%nat) radix ltac:(unfold radix;lia)).
   specialize(C 4%nat ltac:(lia));unfold radix in *;lia. }
 assert (V:pack h=pack(DeferredCarry.carry d)) by (unfold pack,limbs,h;now rewrite !Step by lia).
 assert (Pack:pack d = k*pack a+1024*prime-pack b) by (unfold pack,limbs,d,bias,prime,radix;cbn [Nat.eqb];ring).
 pose proof (proj1 (congruent_value _ _) (DeferredCarry.carry_value d)) as E.
 change (residue (pack (DeferredCarry.carry d)) = residue (pack d)) in E.
 unfold equal_columns;fold h;rewrite high_test_correct,congruent_value,V,E,Pack by (auto || lia).
 unfold value,k;destruct twice;rewrite residue_sub,residue_add,residue_mul;
 replace (residue (1024*prime)) with 0%fp by
 (symmetry;apply residue_zero;apply Z.mod_mul;unfold prime;discriminate).
 all: change (residue 0) with 0%fp;change (residue 1) with 1%fp;try rewrite residue_two.
 all: match goal with |- (?u = 0%fp <-> ?v = ?w) =>
   replace u with (v-w)%fp by ring;split;[intro H;replace v with ((v-w)+w)%fp by ring;rewrite H;ring
   |intros ->;ring] end.
Qed.

Lemma gather_row s j c i : column s j (Z.of_nat c) i=table_row s j false 8 (5*c+i)%nat.
Proof. unfold column,table_row,table_address,table_disp. f_equal;rewrite Nat2Z.inj_add,Nat2Z.inj_mul;ring. Qed.
(* The filter gathers only positive digit eight from the selected key table. *)
Lemma filter_lane_correct s P eligible j :
 (forall i,(i<20)%nat -> 0<=table_row s j false 8 i<2^52) ->
 represents_cache (scalar_cache false (table_row s j false 8)) (multiple 8 P) ->
 (j<8)%nat ->
 (filter_keys s eligible j=true <-> eligible j=true /\ multiple 8 P<>identity).
Proof.
 intros Bound Rep J.
 set (a:=table_row s j false 8) in *.
 assert (V:forall c, (c<4)%nat -> split_field(column s j (Z.of_nat c))).
 { intros c C i I;rewrite gather_row;specialize(Bound (5*c+i)%nat ltac:(cbn;lia));fold a;unfold split;lia. }
 set (Q:=multiple 8 P) in *.
 assert (Val:forall c,value(column s j (Z.of_nat c))=value(fun i=>a (5*c+i)%nat))
 by (intro c;unfold value,pack,limbs;now rewrite !gather_row).
 pose proof (Val 0%nat) as V0;pose proof (Val 1%nat) as V1;pose proof (Val 3%nat) as V3.
 cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in V0,V1,V3.
 assert (G:first s j && second s j=true <-> Q=identity).
 { unfold first,second. rewrite andb_true_iff.
   rewrite (equal_columns_ok false _ _ (V 1%nat ltac:(lia)) (V 0%nat ltac:(lia))).
   rewrite (equal_columns_ok true _ _ (V 0%nat ltac:(lia)) (V 3%nat ltac:(lia))).
   change ((value (column s j 1) = value (column s j 0) /\
     (value (column s j 0)+value (column s j 0))%fp = value (column s j 3)) <-> Q = identity).
   rewrite V0,V1,V3. exact (cache_identity_iff _ _ _ _ _ Rep). }
 assert (Flow:forall b,reaches Filter FirstDifference b false KeysDone=b) by (destruct b;reflexivity).
 unfold filter_keys;rewrite Flow;destruct (byte (first s)=?0) eqn:M.
 - apply Z.eqb_eq in M. assert (Off:first s j=false) by (rewrite <-(byte_bit _ _ J),M,Z.bits_0;reflexivity).
   rewrite Off in G;intuition discriminate.
 - rewrite andb_true_iff,negb_true_iff. destruct (first s j && second s j);cbn in G;intuition congruence.
Qed.

Lemma filter_correct s B A eligible j : valid_tables s B A -> (j<8)%nat ->
 (filter_keys s eligible j=true <-> eligible j=true /\ multiple 8 (A j)<>identity).
Proof.
 intros T J;destruct (T j false 8 J ltac:(unfold legal_index;lia)) as [Bound Rep].
 now apply filter_lane_correct.
Qed.
