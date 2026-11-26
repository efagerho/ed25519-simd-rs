From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.WordBounds memory.ByteMemory memory.FlatMemory.
Import ListNotations. Local Open Scope Z_scope.

Fixpoint spill rs m top (regs:list nat) := match regs with
 | []=>m | r::rest=>spill rs (store_word m (top-8) (rs r)) (top-8) rest end.

Lemma outside_spill rs m top xs x : x<top-8*Z.of_nat(length xs) \/ top<=x ->
 spill rs m top xs x=m x.
Proof.
 revert m top;induction xs as [|r xs IH];intros m top X;[reflexivity|].
 cbn [length] in X;rewrite Nat2Z.inj_succ in X. cbn [spill].
 rewrite IH by lia. apply write_outside;lia.
Qed.
Lemma spilled_word rs m top xs i r : (forall r,word64 (rs r)) ->
 nth_error xs i=Some r ->
 read_word (spill rs m top xs) (top-8*(1+Z.of_nat i))=rs r.
Proof.
 revert m top i;induction xs as [|a xs IH];intros m top [|i] W N;try discriminate.
 - injection N as ->;cbn [spill]. replace (top-8*(1+Z.of_nat 0)) with (top-8) by ring.
   apply read_word_exact;[apply W|]. intros k K;rewrite outside_spill by lia.
   unfold store_word;rewrite write_at by lia;reflexivity.
 - cbn [spill];replace (top-8*(1+Z.of_nat(S i))) with ((top-8)-8*(1+Z.of_nat i)) by lia.
   apply IH;assumption.
Qed.

Lemma spill_ext rs rs' top m xs : (forall r,In r xs -> rs r=rs' r) -> spill rs m top xs=spill rs' m top xs.
Proof.
 revert top m;induction xs as [|r xs IH];intros t m G;[reflexivity|].
 cbn [spill];rewrite (G r (or_introl eq_refl));apply IH;intros k K;apply G;now right.
Qed.
