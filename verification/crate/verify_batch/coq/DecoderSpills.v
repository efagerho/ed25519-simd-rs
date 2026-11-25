From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.StoreInstructions execution.InstructionRoute execution.MappedFetch
 memory.ByteMemory memory.MemoryGeometry memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderKernel DecoderProduct.
Import ListNotations. Local Open Scope Z_scope.

Definition registers: list nat:=[5;3;12;13;14]%nat.
Definition top pol e:=common_top pol e-112.
Definition area pol e x:=top pol e-40<=x<top pol e+8.
Definition saved pol e s m:=preserved (area pol e) (spill (regs s) (mem s) (top pol e) registers) m.

(* Include every caller byte outside the private stack and both output points.
   The five saved qwords have their pushed values until the decoder returns. *)
Definition caller_byte pol e x := ~(Return.sp e-16384<=x<top pol e) /\
 forall sig,~span (point e sig) 1280 x.
Definition protected pol e x:=area pol e x \/ caller_byte pol e x.
Definition retained pol e s m:=preserved (protected pol e) (spill (regs s) (mem s) (top pol e) registers) m.
Lemma saved_part pol e s m : retained pol e s m -> saved pol e s m.
Proof. intros R x X;apply R;now left. Qed.
Lemma caller_part pol e s m : retained pol e s m -> preserved (caller_byte pol e) (mem s) m.
Proof.
 intros R x X;rewrite (R x (or_intror X));apply outside_spill;destruct X as [Outside _].
 change (Z.of_nat(length registers)) with 5;unfold top,common_top,Rows.frame,Return.sp in *;destruct pol;lia.
Qed.

Lemma pushed o s c sp : regs s 4%nat=sp -> 800<=sp<2^64 ->
 exists t ws,run 6 (ScalarBytes.fetch o text) (State (Running 0) s c)=Some(State (Running 11) t c,ws) /\
 mem t=spill (regs s) (mem s) sp registers.
Proof.
 intros SP Range;eexists;eexists;split;[apply (InstructionRoute.checked _ _ _ (proj1 DecoderFrame.image));reflexivity|].
 cbn [DecoderFrame.saves follow step option_map loc cf cpu_state app push snd caller_step apply_stack stack_step result_regs result_mem
   with_words with_zf set set_regs push_words regs mem put Nat.eqb registers spill];rewrite SP.
 repeat match goal with |- context[word ?x]=>rewrite (word_fits x ltac:(unfold word64 in *;lia)) end;reflexivity.
Qed.

Theorem at_setup pol bias e p q : placement e -> loaded pol bias (mem e) (writable e) -> BatchDecode.entry pol bias e p ->
 inner bias p=Some q -> retained pol e (machine p) (mem(machine q)).
Proof.
 intros P I [PC [Acc [_ [_ [_ [SP _]]]]]] Call;set (s:=machine p) in *;set (sp:=top pol e) in *;fold sp in SP.
 set (o:=base bias) in *;set (c:=LinkedRun.carry p).
 destruct(Return.stack_ok _ P) as [[L H] _].
 assert (Stack:Return.sp e-1200<=top pol e<Return.sp e-1000) by (unfold top,common_top,Rows.frame,Return.sp;destruct pol;lia).
 assert (Bounds:800<=sp<2^64) by (fold sp in Stack;lia).
 destruct(DecoderFrame.save o s c sp SP Bounds) as [a [front [A [Front [SA [BP [DX [SI DI]]]]]]]].
 destruct(pushed o s c sp SP Bounds) as [a' [ws [A' Mem]]];change text with DecoderFrame.code in A';rewrite A in A';injection A' as <- <-.
 destruct(DecoderFrame.setup o a c s sp Bounds SA BP DX SI DI) as [b [cf [B [Args MB]]]].
 destruct(DecoderFrame.load_constants false o b cf) as [d [D [GD [MD _]]]].
 assert (Live:DecoderFrame.args s sp d) by (unfold DecoderFrame.args;rewrite GD;exact Args).
 destruct(DecoderFrame.inner_call o d cf s sp (DecoderProduct.address_fits pol bias e I DecoderKernel.Carry 244 ltac:(change (0<=244<2984);lia))
   Bounds Live) as [v [w [C [_ [_ [Where _]]]]]].
 pose proof(run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ A _ _ _ B) _ _ _ D) _ _ _ C) as All.
 assert (Last:confined (fun x=>DecoderFrame.top sp-8<=x<DecoderFrame.top sp) [w]) by (constructor;[exact Where|constructor]).
 assert (Safe:confined (writable e) (((front++[])++[])++[w])).
 { rewrite !app_nil_r;apply Forall_app;split.
   - eapply Forall_impl;[|exact Front];intros f F x X;specialize(F x X);left;unfold span,DecoderFrame.slot in *;fold sp in Stack;lia.
   - eapply Forall_impl;[|exact Last];intros f F x X;specialize(F x X);left;unfold span,DecoderFrame.top in *;
     pose proof(Z.mod_pos_bound (sp-40) 64 ltac:(lia));fold sp in Stack;lia. }
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ p o text 15 0 _ _ Acc ltac:(rewrite Z.add_0_r;exact PC) Map Sep All Safe) as [Exec _].
 change (segment o text 15 p=Some q) in Call;rewrite Call in Exec;injection Exec as ->.
 pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ C)) as V;change (mem v=WriteTrace.replay (mem d) [w]) in V.
 intros x X;change (mem v x=spill (regs s) (mem s) sp registers x);rewrite V,(WriteTrace.frame _ _ Last),MD,MB,Mem;[reflexivity|].
 unfold DecoderFrame.top;pose proof(Z.mod_pos_bound (sp-40) 64 ltac:(lia));fold sp in Stack.
 destruct X as [X|[X _]];[unfold area in X|];fold sp in X;lia.
Qed.
