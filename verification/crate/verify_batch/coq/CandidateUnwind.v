From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.StoreHistory abi.SysV
 memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require LadderEntry.
Import ListNotations. Local Open Scope Z_scope.
Definition path pol:list line:=let n:=LadderEntry.next pol in [(n,7%nat,Add64 4 520);(n+7,2%nat,RestoreG 12);
 (n+9,1%nat,RestoreG 3);(n+10,1%nat,Ret)].
Lemma image pol:linked (ScoreStart.candidate_code pol) (path pol).
Proof. destruct pol;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute pol bias:=segment (CandidateDigest.origin pol bias) (ScoreStart.candidate_code pol) 4.
Definition restored s top:=LinkedCalls.returning (pop (pop (with_zf (set s 4 (top-16)) false) 12) 3).
Definition slots top m rs ret:=read_word m (top-16)=rs 12%nat /\ read_word m (top-8)=rs 3%nat /\ read_word m top=ret.

Lemma transfer pol bias s top rs ret c:536<top -> top+8<2^64 -> regs s 4%nat=top-16-520 ->
 word64 ret -> slots top (mem s) rs ret ->
 let v:=restored s top in
 run 4 (ScalarBytes.fetch (CandidateDigest.origin pol bias) (ScoreStart.candidate_code pol))
  (State(Running(LadderEntry.next pol)) s c)=Some(State(Returned ret) v (Some false),[]) /\
 regs v 4%nat=top+8 /\ regs v 12%nat=rs 12%nat /\ regs v 3%nat=rs 3%nat /\
 (forall g,g<>4%nat ->g<>3%nat ->g<>12%nat -> regs v g=regs s g).
Proof.
 intros Lo Hi SP Fit [R12 [BX Back]] v.
 assert (A:word(regs s 4%nat)=top-16-520) by (rewrite SP;apply word_fits;unfold word64;lia).
 assert (B:word(top-16-520+520)=top-16) by (replace (top-16-520+520) with (top-16) by ring;apply word_fits;unfold word64;lia).
 assert (C:(top-16=?0)=false) by (apply Z.eqb_neq;lia).
 assert (CF:(2^64<=?top-16-520+520)=false) by (apply Z.leb_gt;lia).
 assert (D:word(top-16+8)=top-8) by (replace (top-16+8) with (top-8) by ring;apply word_fits;unfold word64;lia).
 assert (E:word(top-8+8)=top) by (replace (top-8+8) with top by ring;apply word_fits;unfold word64;lia).
 assert (F:word top=top) by (apply word_fits;unfold word64;lia).
 set(last:=pop (pop (with_zf (set s 4 (top-16)) false) 12) 3).
 assert (SS:regs last 4%nat=top).
 { unfold last;cbn [pop apply_stack stack_step with_words result_regs regs set set_regs with_zf put Nat.eqb];
   unfold advance_rsp;cbn [put Nat.eqb];now rewrite D,E. }
 assert (Address:word(stack_top (regs last) (mem last))=ret).
 { unfold stack_top;rewrite SS,F;change (word(read_word (mem s) top)=ret);now rewrite Back,(word_fits _ Fit). }
 split.
 - destruct pol;apply (InstructionRoute.checked _ _ _ (image _));
   cbn [path LadderEntry.next follow step loc cpu_state cf option_map app];
   change (word 520) with 520;rewrite A,B,C,CF;
   change (Some(State(Returned (word(stack_top (regs last) (mem last)))) v (Some false),([]:list store))=Some(State(Returned ret) v (Some false),([]:list store)));
   now rewrite Address.
 - unfold v,restored,LinkedCalls.returning,pop,apply_stack;cbn [stack_step with_words result_regs result_mem regs mem set set_regs with_zf put Nat.eqb];
   unfold advance_rsp,stack_top;cbn [put Nat.eqb];rewrite D,E;
   repeat rewrite word_fits by (unfold word64;lia).
   split;[reflexivity|split;[exact R12|split;[exact BX|]]].
   intros g G4 G3 G12;unfold put;repeat rewrite (proj2(Nat.eqb_neq 4 g) ltac:(congruence));
   rewrite (proj2(Nat.eqb_neq 3 g) ltac:(congruence)),(proj2(Nat.eqb_neq 12 g) ltac:(congruence));reflexivity.
Qed.
