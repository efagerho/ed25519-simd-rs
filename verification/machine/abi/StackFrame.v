From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.WordBounds
 memory.ByteMemory memory.FlatMemory.
Local Open Scope Z_scope.

(* A nested call can use the half-open interval [top-depth,top). Its CALL
   writes the top eight bytes of that interval before the callee runs. *)
Definition outside top depth x := ~(top-depth<=x<top).

Lemma read_outside top depth before after a n :
 preserved (outside top depth) before after ->
 disjoint (top-depth) depth a (Z.of_nat n) ->
 read_le n after a=read_le n before a.
Proof.
 intros Keep Apart;apply (preserved_read _ _ _ _ _ Keep).
 intros k K;unfold outside,disjoint in *;lia.
Qed.

Lemma push_preserves s ret top depth :
 regs s 4%nat=top -> word64 (top-8) -> 8<=depth ->
 preserved (outside top depth) (mem s) (mem(push s ret)).
Proof.
 intros R Fit D x X;change (store_word (mem s) (word(regs s 4%nat-8)) ret x=mem s x).
 rewrite R,word_fits by exact Fit;apply write_outside;unfold outside in X;lia.
Qed.

Lemma call_frame s ret after top depth :
 regs s 4%nat=top -> word64 (top-8) -> 8<=depth ->
 preserved (outside (regs s 4%nat) depth) (mem s) after ->
 preserved (outside top depth) (mem s) (mem(push s ret)) /\
 preserved (outside top depth) (mem s) after /\ read_word after top=read_word (mem s) top.
Proof.
 intros R Fit D;rewrite R;intro Keep;split.
 - apply push_preserves;assumption.
 - split;[exact Keep|apply (read_outside _ _ _ _ _ _ Keep);unfold disjoint;lia].
Qed.
