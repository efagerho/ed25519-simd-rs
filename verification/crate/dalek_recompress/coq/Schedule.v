From Coq Require Import ZArith List Bool Lia.
From Machine Require Import isa.Instructions.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Import Kernels Power Unpack Decode.
From Ed25519Simd.Dalek Require Import Caller FieldOps Encoding Masks Batch.
Import ListNotations. Local Open Scope Z_scope.

Inductive field_term := Coord (chunk row:nat) | Times (a b:field_term) | Inverted (a:field_term).
Inductive vector_value := Field (f:field_term) | Parities (f:field_term).
Inductive mask_term := Zero | Scored (hi:mask_term)(a:field_term)(sign ypoint yenc callee:nat).
Inductive ptr := Point (off:Z) | Encoding (off:Z) | Stack (off:Z) | Unset.
Definition bump p d := match p with Point a=>Point(a+d) | Encoding a=>Encoding(a+d)
 | Stack a=>Stack(a+d) | Unset=>Unset end.
Definition chunk_id total stride a :=
 if (0<=?a)&&(a <? stride*Z.of_nat total)&&(a mod stride =? 0)
 then Some(Z.to_nat(a/stride)) else None.
Definition frame_field a := (0<=?a)&&(a+320<=?3200)&&(a mod 320=?0).
Definition write {T} (m:Z->T) at_ v a := if a=?at_ then v else m a.
Inductive mask_byte := Sign (encoded:nat) | MatchY (point encoded:nat) | Undefined.
Record state := St {
 regs:nat->ptr; fields:Z->option field_term; saved_bytes:Z->mask_byte;
 vector:option vector_value; probes:list(nat*nat); mask:mask_term; remaining:nat; constants_ready:bool
}.
Definition initial n := St (fun i=>match i with 7%nat=>Point 0 | 6%nat=>Encoding 0 | _=>Unset end)
 (fun _=>None) (fun _=>Undefined) None [] Zero n false.
Definition exec n st cmd : option state :=
 let r:=regs st in let m:=fields st in let b:=saved_bytes st in
 let v:=vector st in let g:=probes st in let hi:=mask st in let left:=remaining st in
 (* The SysV small-order call can destroy every ZMM register. Conservatively
    invalidate the constants on either scoring path. *)
 let ready:=constants_ready st in
 let after:=match cmd with Frame|Reload=>true | ScoreMask=>false | _=>ready end in
 let keep r m b v g hi:=Some(St r m b v g hi left after) in
 let read p:=match p with Stack a=>if frame_field a then m a else None
 | Point a=>if (0<=?a)&&(a <? 1280*Z.of_nat n)&&(a mod 320=?0)
 then Some(Coord (Z.to_nat(a/1280)) (Z.to_nat(a mod 1280/64))) else None | _=>None end in
 if (match cmd with YCheck|Mul|StartInverse|ScoreMask=>negb ready | _=>false end) then None else
 match cmd with
 | Frame=>keep (put(put(put(put(put(put r 3 (r 7%nat)) 12 (r 7%nat)) 13 (r 6%nat))
   4 (Stack 0)) 14 (Stack 640)) 10 (Stack 3200)) m b v g Zero
 | YCheck=>match r 10%nat,r 12%nat,r 13%nat with Stack a,Point p,Encoding e=>
   match chunk_id n 1280 p,chunk_id n 256 e with Some i,Some j=>
   if (3200<=?a)&&(a+2<=?3264) then
    keep r m (write (write b (a+1) (Sign j)) a (MatchY i j)) None ((i,j)::g) hi else None
   | _,_=>None end | _,_,_=>None end
 | LoadField base d=>keep r m b (option_map Field (read(bump (r base) d))) g hi
 | StoreField base d=>match bump(r base)d,v with Stack a,Some(Field f)=>
   if frame_field a then keep r (write m a (Some f)) b v g hi else None | _,_=>None end
 | Rhs base d lea=>keep (put r 8 (if lea then bump(r base)d else r base)) m b v g hi
 | Mul=>match v,read(r 8%nat) with Some(Field a),Some f=>keep r m b (Some(Field(Times a f))) g hi | _,_=>None end
 | Bump sub reg d=>keep (put r reg (bump (r reg) (if sub then -d else d))) m b v g hi
 | SaveMasks=>keep (put r 13 (r 10%nat)) m b v g hi
 | StartInverse=>match v,r 14%nat with Some(Field f),Stack root=>
   if frame_field root && (640<=?root) then
   keep (put r 8 Unset) (write (write (write m 0 None) 320 None) root None) b (Some(Field(Inverted f))) g hi
   else None | _,_=>None end
 | ScoreMask=>match r 12%nat,r 13%nat,v with Point p,Stack a,Some(Parities x)=>
   match chunk_id n 1280 p,b(a+1),b a with Some i,Sign e,MatchY u w=>
   keep (put (put r 8 Unset) 10 Unset) m b None g (Scored hi x e u w i)
   | _,_,_=>None end | _,_,_=>None end
 | Reload=>keep r m b v g hi | Epilogue=>keep r m b v g hi | ReduceParity=>None end.
Definition next l := hd_error(tl(skipn (let fix index xs:=match xs with []=>O | a::t=>
 if label_beq a l then O else S(index t) end in index order) order)).
Definition first st := match regs st 12%nat,regs st 3%nat with Point a,Point b=>a=?b | _,_=>false end.
Definition decrement st := St (regs st)(fields st)(saved_bytes st)(vector st)(probes st)(mask st)(Nat.pred(remaining st))(constants_ready st).
Fixpoint walk fuel n skip l st : option (list(nat*nat)*mask_term) := match fuel with O=>None | S gas=>
 let '(ops,e):=block l in
 match fold_left (fun s cmd=>match s with Some t=>exec n t cmd | None=>None end) ops (Some st) with
 | None=>None | Some t=>let go dst st:=match dst with Some target=>walk gas n skip target st | None=>None end in
 match e with End=>Some(probes t,mask t) | Fall=>go (next l) t | Jump dst=>walk gas n skip dst t
 | ParityBranch slow=>
   (* Merge these two paths only for the out-of-line carry/XOR block
      that immediately rejoins its fast sibling. The resulting vector
      retains the unsigned top-limb test for evaluation on all eight lanes. *)
   match next l,block slow,vector t with
   | Some fast,([ReduceParity],Jump resume),Some(Field f)=>
     if label_beq fast resume then walk gas n skip fast
       (St (regs t)(fields t)(saved_bytes t)(Some(Parities f))(probes t)(mask t)(remaining t)(constants_ready t)) else None
   | _,_,_=>None end
 | Branch c _ dst=>let st:=match c with Last=>decrement t | _=>t end in
   let taken:=match c with NoChunks|Last=>Nat.eqb (remaining st) 0 | First=>first st | NoMatch=>skip end in
   go (if taken then Some dst else next l) st end end end.
Definition run n skip := walk 160 n skip Entry (initial n).

Fixpoint pref i := match i with O=>Coord O 10 | S t=>Times (Coord i 10) (pref t) end.
Fixpoint reverse_plan n acc hi := match n with O=>hi | S i=>
 let inv:=match i with O=>acc | S t=>Times(pref t) acc end in
 reverse_plan i (Times(Coord i 10) acc) (Scored hi (Times(Coord i 0)inv) i i i i) end.
Fixpoint checked_chunks n : list(nat*nat) := match n with O=>[] | S i=>(i,i)::checked_chunks i end.
Definition plan n skip := match n with O=>Zero | S i=>if skip:bool then Zero else
 reverse_plan n (Inverted(pref i)) Zero end.
Lemma path n skip : (n<=8)%nat -> run n skip=Some(checked_chunks n,plan n skip).
Proof. intros N;do 9 (destruct n as [|n];[destruct skip;vm_compute;reflexivity|]);lia. Qed.

Section Evaluate.
Variable k:kernels.
Variable flat:Z->Z.
Variables points enc:Z.
Variable small:nat->option Z.
Fixpoint field_value f j := match f with
 | Coord i row=>coord (point_words flat points i) row j
 | Times a b=>mul k (field_value a j)(field_value b j)
 | Inverted a=>inverse k (field_value a j) end.
Definition ys i e j := y_matches k flat (Batch.ptr enc e) j (zz flat points i j)(yy flat points i j).
Fixpoint probe_word g := match g with []=>0 | (i,e)::tail=>Z.lor (probe_word tail)(byte(ys i e)) end.
Fixpoint output_value m := match m with Zero=>Some 0 | Scored hi a sign i e c=>
 match output_value hi with None=>None | Some high=>
 score_x (field_value a) (signs flat enc sign) (ys i e) (small c) high end end.
Definition execute n := match run n true with None=>None | Some(g,_)=>
 match run n (probe_word g=?0) with None=>None | Some(_,m)=>output_value m end end.
Lemma pref_value i : field_value(pref i)=prefix k flat points i.
Proof. induction i;[reflexivity|]. cbn [pref prefix field_value]. unfold vecmul;now rewrite IHi. Qed.
Lemma reverse_value n acc hi :
 output_value(reverse_plan n acc hi)=match output_value hi with None=>None | Some high=>
 backward k flat points enc small n (field_value acc) high end.
Proof.
 revert acc hi;induction n as [|i IH];intros acc hi;[cbn [reverse_plan backward];destruct(output_value hi);reflexivity|].
 cbn [reverse_plan];rewrite IH;cbn [output_value backward];destruct(output_value hi) as [h|];[|reflexivity].
 destruct i as [|t];[reflexivity|].
 cbn [field_value];rewrite pref_value;reflexivity.
Qed.
Lemma caller_returns n : (n<=8)%nat -> execute n=returned k flat points enc small n.
Proof.
 intro N;unfold execute;rewrite !path by assumption.
 assert (G:probe_word (checked_chunks n)=any_y k flat points enc n)
 by (induction n;[reflexivity|cbn [checked_chunks probe_word any_y];now rewrite IHn by lia]).
 destruct n as [|i];[reflexivity|]. unfold returned;rewrite G. destruct(any_y _ _ _ _ _=?0);[reflexivity|].
 unfold plan;rewrite reverse_value;cbn [output_value]. cbn [field_value];now rewrite pref_value.
Qed.
End Evaluate.
