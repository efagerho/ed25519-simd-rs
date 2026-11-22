From Coq Require Import List ZArith Lia.
From Machine Require Import execution.IndexedLoads execution.LinkedCalls execution.WordSemantics
 execution.WordBounds memory.ByteMemory memory.MemoryGeometry.
From Ed25519Simd.SignatureScalar Require Import Program Audit.
Import ListNotations. Local Open Scope Z_scope.

Local Ltac lhs e := lazymatch goal with |- _ = ?r => change (e=r) end.
Definition slot j := W64 (Plus (G 6) (K (8*Z.of_nat j))).
Definition address j := W64 (Plus (Read 8 (slot j)) (K 0)).
Definition source_word j i := Read 8 (Plus (address j) (K (8*Z.of_nat i))).
Definition in_word s j i := read_word (mem s) (ptr s j+8*Z.of_nat i).
Lemma term_route j i : (j<8)%nat -> (i<4)%nat ->
 vec (summary inputs) (8+i)%nat j=source_word j i.
Proof.
 assert (H:forallb (fun l=>forallb (fun w=>term_beq (vec (summary inputs) (8+w)%nat l)
                    (source_word l w)) (seq 0 4)) (seq 0 8)=true) by (vm_compute;reflexivity).
 intros J I;apply (proj1 (forallb_forall _ _)) with (x:=j) in H;[|apply in_seq;lia].
 apply (proj1 (forallb_forall _ _)) with (x:=i) in H;[|apply in_seq;lia].
 now apply internal_term_dec_bl.
Qed.
Definition read_pair a b := [(slot a,8%nat);(slot b,8%nat);(address a,32%nat);(address b,32%nat)].
Lemma trace_inputs : rev (loads (summary inputs))=
 read_pair 0 2++read_pair 1 3++read_pair 4 6++read_pair 5 7.
Proof. vm_compute;reflexivity. Qed.

Section Input.
Context {s pc n ro} (P:placement s pc n ro).
Lemma eval_slot j : (j<8)%nat -> eval s (slot j)=regs s 6%nat+8*Z.of_nat j.
Proof.
 intro J;lhs (word (regs s 6%nat+8*Z.of_nat j)).
 apply word_fits;destruct (table_fits _ _ _ _ P) as [[A B] _];unfold WordBounds.word64;lia.
Qed.
Lemma eval_address j : (j<8)%nat -> eval s (address j)=ptr s j.
Proof.
 intro J; lhs (word (read_word (mem s) (eval s (slot j))+0)).
 rewrite (eval_slot j J),Z.add_0_r; apply word_fits.
 destruct (scalar_fits _ _ _ _ P j J) as [[A B] _];unfold word64;lia.
Qed.
Lemma loaded_word j i : (j<8)%nat -> (i<4)%nat ->
 vectors (loaded s) j (8+i)%nat=in_word s j i.
Proof.
 intros J I;lhs (eval s (vec (summary inputs) (8+i)%nat j)).
 rewrite term_route by assumption;lhs (read_word (mem s) (eval s (address j)+8*Z.of_nat i)).
 now rewrite eval_address.
Qed.
Lemma inputs_safe : reads_inputs s.
Proof.
 intros a n' H;apply -> in_rev in H;rewrite trace_inputs in H.
 cbn [read_pair app In] in H.
 repeat destruct H as [H|H];try contradiction;inversion H;subst.
 all: first [eexists;split;[|left;split;[reflexivity|apply eval_slot]];lia
            |eexists;split;[|right;split;[reflexivity|apply eval_address]];lia].
Qed.
End Input.

Definition Q := 2^64.
Definition four_words a b c d := a+Q*(b+Q*(c+Q*d)).
Lemma scalar_words s j : scalar s j =
 four_words (in_word s j 0) (in_word s j 1) (in_word s j 2) (in_word s j 3).
Proof.
 assert (Split:forall n m flat a, read_le (n+m) flat a=
   read_le n flat a + 256^Z.of_nat n * read_le m flat (a+Z.of_nat n)).
 { induction n as [|n IH];intros m flat a;[change (read_le m flat a=0+1*read_le m flat (a+0));rewrite Z.add_0_r;ring|].
   cbn [Nat.add read_le];rewrite IH,Nat2Z.inj_succ,Z.pow_succ_r by lia.
   replace (a+1+Z.of_nat n) with (a+Z.succ (Z.of_nat n)) by lia;ring. }
 unfold scalar,in_word,four_words;set (a:=ptr s j).
 change 32%nat with (8+24)%nat;rewrite (Split 8%nat 24%nat).
 change 24%nat with (8+16)%nat;rewrite (Split 8%nat 16%nat).
 change 16%nat with (8+8)%nat;rewrite (Split 8%nat 8%nat).
 change (256^Z.of_nat 8) with Q;fold read_word.
 replace (a+8*Z.of_nat 0) with a by ring.
 replace (a+8*Z.of_nat 1) with (a+Z.of_nat 8) by ring.
 replace (a+8*Z.of_nat 2) with (a+Z.of_nat 8+Z.of_nat 8) by ring.
 replace (a+8*Z.of_nat 3) with (a+Z.of_nat 8+Z.of_nat 8+Z.of_nat 8) by ring.
 reflexivity.
Qed.
