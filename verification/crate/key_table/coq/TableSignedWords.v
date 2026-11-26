From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory.
From Machine Require execution.PackedStores.
From Ed25519Simd.KeyTable Require Execution Pack Rows.
From Ed25519Simd.KeyTable Require Import TablePackValues TablePackMemory.
From Ed25519Simd.KeyTable Require TablePacking.
From Ed25519Simd.KeyTable Require Import CallLayout.
Import ListNotations. Local Open Scope Z_scope.

Definition ops first:=if first:bool then Pack.first else Pack.rest.
Definition apply_block digit first:=fold_left (symbolic_step digit) (ops first).
Definition empty:table_memory:=fun _=>Pack.Unknown.
Definition result d:=snd(apply_block d false (apply_block d true (TablePackValues.initial,empty))).
Definition offset d sign j i:=TablePackMemory.index d sign (340*j+i)%nat.
Definition image d:=let after:=result d in forallb (fun sign=>forallb (fun j=>forallb (fun i=>
 if Execution.word_dec (after (offset d sign j i)) (Pack.signed_word sign i j) then true else false)
 (seq 0 20)) (seq 0 8)) [true;false].
Lemma digits:forallb (fun n=>image (Z.of_nat n)) (seq 1 8)=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque result.
Lemma layout d sign j i : 1<=d<=8 -> (j<8)%nat -> (i<20)%nat ->
 result d (offset d sign j i)=Pack.signed_word sign i j.
Proof.
 intros D J I;pose proof digits as C;apply forallb_forall with (x:=Z.to_nat d) in C;[|apply in_seq;lia].
 rewrite Z2Nat.id in C by lia;unfold image in C;apply forallb_forall with (x:=sign) in C;[|destruct sign;cbn;auto].
 apply forallb_forall with (x:=j) in C;[|apply in_seq;lia];apply forallb_forall with (x:=i) in C;[|apply in_seq;lia].
 destruct(Execution.word_dec _ _);[assumption|discriminate].
Qed.
Lemma defined sign i j:known(Pack.signed_word sign i j)=true.
Proof. destruct sign;unfold Pack.signed_word;repeat match goal with |-context[(?a<??b)%nat]=>destruct (a<?b)%nat end;reflexivity. Qed.

Lemma block_values first (root:cpu) bias e d p q ks f st : placement e -> 1<=d<=8 ->
 TableMultiple.pointers e d (machine p) -> well_formed(machine p) -> mask_ok ks -> represents_state f e st (machine p) ->
 TablePackRows.block first root bias e d p q ks -> represents_state f e (apply_block d first st) (machine q).
Proof.
 intros P D Ptr W K State B;pose proof(TablePackRows.exact_bytes _ _ _ _ _ _ _ _ B) as Run.
 destruct(PackedStores.simulate _ _ _ _ _) as [t ws] eqn:R in Run;destruct Run as [T Log];rewrite T.
 eapply (TablePackMemory.simulate e d (CallLayout.base bias) (ops first) (TablePackRows.start first) (machine p) ks f st t ws);
  [exact P|exact D|exact Ptr|exact W| |exact K|exact State|exact R].
 pose proof(proj2(proj2(TablePackRows.image first))) as Safe;apply Forall_forall;intros v V.
 apply forallb_forall with (x:=TablePackRows.lower v) in Safe;[exact Safe|apply in_map;exact V].
Qed.

Local Transparent result.
Local Opaque apply_block.
Theorem contents (root:cpu) bias e d p q ks f : placement e -> 1<=d<=8 ->
 TableMultiple.pointers e d (machine p) -> well_formed(machine p) -> mask_ok ks ->
 represents f TablePackValues.initial (machine p) -> TablePacking.packed root bias e d p q ks ->
 forall sign j i,(j<8)%nat -> (i<20)%nat ->
 read_word (mem(machine q)) (TablePackRows.row e d sign (Z.of_nat j)+8*Z.of_nat i)=Rows.eval f (Pack.signed_word sign i j).
Proof.
 intros P D Ptr W Mask Registers Q;destruct(TablePacking.blocks _ _ _ _ _ _ _ Q) as [a [b [First [B Rest]]]].
 assert (Initial:represents_state f e (TablePackValues.initial,empty) (machine p)) by (split;[exact Registers|intros x;discriminate]).
 pose proof(block_values _ _ _ _ _ _ _ _ _ _ P D Ptr W Mask Initial First) as A.
 pose proof(TablePackRows.arguments _ _ _ _ _ _ _ _ First) as PtrA.
 assert (PtrB:TableMultiple.pointers e d (machine b)) by (rewrite B;destruct PtrA;constructor;assumption).
 assert (WB:well_formed(machine b)) by (rewrite B;exact (TablePackRows.words _ _ _ _ _ _ _ _ First)).
 assert (State:represents_state f e (apply_block d true (TablePackValues.initial,empty)) (machine b)) by (rewrite B;exact A).
 destruct(block_values _ _ _ _ _ _ _ _ _ _ P D PtrB WB Mask State Rest) as [_ Words].
 change (matches f e (result d) (machine q)) in Words;intros sign j i J I.
 specialize(Words (offset d sign j i));rewrite (layout _ _ _ _ D J I) in Words.
 specialize(Words (defined sign i j));unfold location,offset,index in Words;unfold TablePackRows.row,TableMultiple.pos,TableMultiple.neg.
 rewrite Nat2Z.inj_add,Nat2Z.inj_mul in Words;change (Z.of_nat 340) with 340 in Words;destruct sign;rewrite <-Words;f_equal;ring.
Qed.

Definition signed e digit (f:nat->nat->Z) s:=forall sign j i,(j<8)%nat -> (i<20)%nat ->
 read_word (mem s) (TablePackRows.row e digit sign (Z.of_nat j)+8*Z.of_nat i)=Rows.eval f (Pack.signed_word sign i j).
