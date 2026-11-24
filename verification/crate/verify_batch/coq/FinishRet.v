From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderFinish DecoderProduct DecoderKernel.
Import ListNotations. Local Open Scope Z_scope.

Definition path:list line:=[(1431,3%nat,Copy32 0 10);(1434,1%nat,Ret)].
Lemma code:linked text path. Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias:=segment (base bias) text 2.
Theorem checked sig pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=base bias+1431 -> accounted e (writable e) p -> well_formed(machine p) -> regs(machine p) 4%nat=link_slot pol e ->
 read_word (mem(machine p)) (link_slot pol e)=base bias+DecoderFinish.return_offset sig ->
 exists q,execute bias p=Some q /\ ip q=base bias+DecoderFinish.return_offset sig /\ accounted e (writable e) q /\
 well_formed(machine q) /\ regs(machine q) 4%nat=link_slot pol e+8 /\ regs(machine q) 0%nat=regs(machine p) 10%nat mod 2^32 /\
 (forall r,r<>0%nat -> r<>4%nat -> regs(machine q) r=regs(machine p) r) /\
 mem(machine q)=mem(machine p) /\ vectors(machine q)=vectors(machine p) /\ log q=log p.
Proof.
 intros P I PC Acc W SP Link;set (s:=machine p) in *;set (o:=base bias) in *;set (a:=link_slot pol e) in *.
 set (dest:=o+DecoderFinish.return_offset sig) in *;pose proof(depth pol e) as Depth;fold a in Depth;destruct(Return.stack_ok _ P) as [[L H] _].
 assert (Fit:word64 dest) by (unfold dest;apply (DecoderProduct.address_fits pol bias e I DecoderKernel.Carry);destruct sig;change (0<=222<2984) || change (0<=190<2984);lia).
 set (v:=set s 0 (regs s 10%nat mod 2^32));set (out:=LinkedCalls.returning v).
 assert (R:run 2 (ScalarBytes.fetch o text) (State (Running 1431) s (LinkedRun.carry p))=
  Some(State (Returned dest) out (LinkedRun.carry p),[])).
 { apply (InstructionRoute.checked _ _ _ code);cbn [path follow step loc cf cpu_state option_map app].
   change (Some(State (Returned (word(read_word (mem s) (word(regs s 4%nat))))) out (LinkedRun.carry p),@nil WriteTrace.store)=Some(State (Returned dest) out (LinkedRun.carry p),[])).
   rewrite SP,(word_fits a ltac:(unfold word64;lia)),Link,word_fits by exact Fit;reflexivity. }
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text 2 1431 _ _ Acc PC Map Sep R (Forall_nil _)) as [Next Paid].
 eexists;split;[exact Next|split;[reflexivity|split;[exact Paid|split;[exact (segment_wf _ _ _ p _ W Next)|]]]].
 split;[change (word(regs s 4%nat+8)=a+8);rewrite SP;apply word_fits;unfold word64;lia|split;[reflexivity|split]].
 - intros r Z F;change (put (put (regs s) 0 (regs s 10%nat mod 2^32)) 4 (word(regs s 4%nat+8)) r=regs s r);unfold put.
   rewrite (proj2(Nat.eqb_neq 4 r) ltac:(lia)),(proj2(Nat.eqb_neq 0 r) ltac:(lia));reflexivity.
 - split;[reflexivity|split;[reflexivity|apply app_nil_r]].
Qed.
