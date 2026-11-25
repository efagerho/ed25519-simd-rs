From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics
 execution.PreservedRegister execution.WordBounds execution.ScalarBytes execution.ScalarWords execution.InstructionRoute execution.MappedFetch
 memory.ByteMemory memory.FlatMemory memory.WriteTrace abi.SysV.
From Curve25519 Require Import Scalar.
From ProofArithmetic Require Import Radix.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ReducedDigest.
Import ListNotations. Local Open Scope Z_scope.
Local Notation child := FullLadder.LinkedBytes.entry_pc.
Local Notation d := CandidateDigest.dst.
Local Notation o := CandidateDigest.origin.
Definition next pol:Z:=match pol with Zip215=>59 | Dalek=>56 end.
Definition full pol:=match pol with Zip215=>true | Dalek=>false end.
Definition enter pol bias:=segment (o pol bias) (ScoreStart.candidate_code pol) 7.
Definition mode pol:line:=match pol with Zip215=>(48,6%nat,Imm32 9 1) | Dalek=>(48,3%nat,Zero32 9) end.
Definition setup pol:list line:=[(29,3%nat,CopyG 7 3);(32,3%nat,CopyG 6 12);
 (35,5%nat,Load64 2 (Address 12 None 64));(40,5%nat,Load64 1 (Address 12 None 72));
 (45,3%nat,CopyG 8 4);mode pol;(next pol-5,5%nat,CallRelative(child-(ScoreStart.candidate pol+next pol)))].
Lemma image pol:linked (ScoreStart.candidate_code pol) (setup pol).
Proof. destruct pol;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma child_image pol:In (child,FullLadder.LinkedBytes.symbol_bytes) (children pol).
Proof. apply in_or_app;left;do 11 right;left;reflexivity. Qed.

Definition push_return pol bias e:=qword (word(o pol bias+(next pol-5))) (d e-8) (o pol bias+next pol).
Definition args pol e s:=regs s 4%nat=d e-8 /\ regs s 7%nat=ScoreFrame.buffer e /\
 regs s 6%nat=Rows.frame e+768 /\ regs s 2%nat=regs e 9%nat /\ regs s 1%nat=scratch e+512 /\
 regs s 8%nat=d e /\ regs s 9%nat=FullLadder.Native.bits (full pol).

Lemma transfer pol bias e s c:
 regs s 4%nat=d e -> regs s 3%nat=ScoreFrame.buffer e -> regs s 12%nat=Rows.frame e+768 ->
 read_word (mem s) (Rows.frame e+832)=regs e 9%nat -> read_word (mem s) (Rows.frame e+840)=scratch e+512 ->
 word64 (d e-8) -> word64 (Rows.frame e+832) -> word64 (Rows.frame e+840) -> word64(bias+child) ->
 exists u k,run 7 (ScalarBytes.fetch (o pol bias) (ScoreStart.candidate_code pol)) (State(Running 29) s c)=
 Some(State(Running(child-ScoreStart.candidate pol)) u k,[push_return pol bias e]) /\ args pol e u.
Proof.
 intros SP BX Ptr Base Sdigits Stack A B Target;destruct pol;do 2 eexists;split.
 1,3: apply (InstructionRoute.checked _ _ _ (image _));
   cbn [setup mode next follow step cpu_state cf loc option_map push push_words regs set set_regs with_words
        with_zf mem put Nat.eqb effective app];
   rewrite SP,Ptr,!Z.add_0_r,(word_fits _ Stack);
   replace (Rows.frame e+768+64) with (Rows.frame e+832) by ring;
   replace (Rows.frame e+768+72) with (Rows.frame e+840) by ring;
   rewrite (word_fits _ A),(word_fits _ B),Base,Sdigits.
 1: replace (o Zip215 bias+(59-5+Z.of_nat 5+(child-(ScoreStart.candidate Zip215+59)))) with (bias+child) by (unfold o;ring);
    rewrite (word_fits _ Target);replace (bias+child-o Zip215 bias) with (child-ScoreStart.candidate Zip215) by (unfold o;ring);reflexivity.
 1: replace (o Dalek bias+(56-5+Z.of_nat 5+(child-(ScoreStart.candidate Dalek+56)))) with (bias+child) by (unfold o;ring);
    rewrite (word_fits _ Target);replace (bias+child-o Dalek bias) with (child-ScoreStart.candidate Dalek) by (unfold o;ring);reflexivity.
 all: unfold args;cbn [regs with_words with_zf set set_regs put Nat.eqb];repeat split;
     try assumption;reflexivity.
Qed.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record entry pol bias e p t:Prop:=Entry {
 at_ladder:ip t=bias+child;
 writes:accounted e (writable e) t;
 words:well_formed(machine t);
 arguments:args pol e (machine t);
 return_word:read_word (mem(machine t)) (d e-8)=o pol bias+next pol;
 memory:mem(machine t)=commit (mem(machine p)) (push_return pol bias e);
 saved:forall g,In g sysv_saved -> regs(machine t) g=regs(machine p) g;
 store_log:log t=log p++[push_return pol bias e];
 operands:ScoreBuffers.data e (machine t);
 challenge:forall j,(j<8)%nat -> let ds:=FullLadder.Operands.digit_list (machine t) 8 j in
   Forall (fun v=> -8<=v<8) ds /\ (HashLayout.eligible pol e j -> number 16 ds =
   little_endian (SHA512.Spec.sha512 (r_bytes(HashLayout.row e j)++key_bytes(HashLayout.row e j)++message(HashLayout.row e j))) mod L)
}.

Theorem checked pol bias e score q p:placement e -> loaded pol bias (mem e) (writable e) ->
 CandidateEntry.entry pol bias e score -> CandidateDigest.entry pol bias e score q -> ReducedDigest.returned pol bias e q p ->
 exists t,enter pol bias p=Some t /\ entry pol bias e p t.
Proof.
 intros P I C Q R;destruct (ReducedDigest.frame _ P) as [Low [Gap [High _]]];destruct(stack_ok _ P) as [[Bot Top] _].
 assert (M:preserved (CandidateEntry.retained e) (mem(machine score)) (mem(machine p))).
 { intros x X;rewrite (ReducedDigest.outside _ _ _ _ _ R);[apply (CandidateDigest.parent _ _ _ _ _ Q),X|].
   unfold CandidateEntry.retained in X;unfold ReducedDigest.D.writable;lia. }
 destruct (CandidateEntry.ladder_ptrs _ _ _ _ C) as [Base Sdigits].
 destruct (transfer pol bias e (machine p) (carry p) (ReducedDigest.stack _ _ _ _ _ R)
   ltac:(rewrite (ReducedDigest.saved _ _ _ _ _ R 3) by (left;reflexivity);exact (CandidateDigest.point _ _ _ _ _ Q))
   ltac:(rewrite (ReducedDigest.saved _ _ _ _ _ R 12) by (do 2 right;left;reflexivity);exact (CandidateDigest.pointers _ _ _ _ _ Q))
   ltac:(rewrite (CandidateEntry.read_above _ _ _ _ M) by lia;exact Base)
   ltac:(rewrite (CandidateEntry.read_above _ _ _ _ M) by lia;exact Sdigits)
   ltac:(unfold word64;lia) ltac:(unfold Rows.frame,sp,word64 in *;lia) ltac:(unfold Rows.frame,sp,word64 in *;lia)
   (mapped_word _ _ _ I _ _ (child_image pol) ltac:(vm_compute;reflexivity))) as [u [k [Run Args]]].
 pose proof(ReducedDigest.writes _ _ _ _ _ R) as Acc.
 destruct(mapped_now _ _ _ I _ _ _ Acc (ScoreStart.candidate_image pol)) as [Map Sep].
 assert (Slot:forall x,touches (push_return pol bias e) x -> d e-8<=x<d e).
 { intros x X;unfold touches in X;cbn [push_return qword address size] in X;change (Z.of_nat 8) with 8 in X;lia. }
 assert (Safe:confined (writable e) [push_return pol bias e]).
 { constructor;[intros x X;left;specialize(Slot x X);unfold span;lia|constructor]. }
 destruct(at_segment _ _ _ _ _ _ 29 _ _ Acc (ReducedDigest.back _ _ _ _ _ R) Map Sep Run Safe) as [Next Paid].
 assert (Mem:mem u=commit (mem(machine p)) (push_return pol bias e)) by exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)).
 eexists;split;[exact Next|constructor].
 - cbn [LinkedRun.finish ip];unfold absolute;cbn [loc];unfold o;ring.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (ReducedDigest.words _ _ _ _ _ R) Next).
 - exact Args.
 - cbn [LinkedRun.finish machine cpu_state];rewrite Mem;apply write_read_word.
   destruct(symbols _ _ _ _ I _ _ (ScoreStart.candidate_image pol)) as [[L0 H] _].
   assert (Size:0<=next pol<Z.of_nat(length(ScoreStart.candidate_code pol))) by (destruct pol;vm_compute;split;discriminate || reflexivity).
   unfold o,word64;lia.
 - exact Mem.
 - intros g K;eapply (run_keeps_at g (o pol bias) (ScoreStart.candidate_code pol));[destruct pol;vm_compute;reflexivity| |exact Run].
   destruct K as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];destruct pol;vm_compute;reflexivity.
 - reflexivity.
 - eapply ScoreBuffers.keep;[|exact (ReducedDigest.buffers _ _ _ _ _ R)];intros x X;cbn [LinkedRun.finish machine cpu_state];rewrite Mem.
   apply write_outside;intro T;specialize(Slot x T);destruct(scratch_stack _ P);unfold ScoreBuffers.region,span,Rows.frame,sp in *;lia.
 - intros j J;pose proof(ReducedDigest.digits _ _ _ _ _ R j J) as Dg;cbv zeta in Dg|-*.
   assert (Eq:FullLadder.Operands.digit_list u 8 j=ReducedDigest.D.signed_digits (mem(machine p)) (d e) j).
   { unfold FullLadder.Operands.digit_list,FullLadder.Operands.digits,ReducedDigest.D.signed_digits;apply map_ext_in;intros a A0.
     destruct Args as [_ [_ [_ [_ [_ [K _]]]]]];rewrite K,Mem;f_equal;apply write_outside;intro T;specialize(Slot _ T);lia. }
   change (machine _) with u;now rewrite Eq.
Qed.
End Iteration.
