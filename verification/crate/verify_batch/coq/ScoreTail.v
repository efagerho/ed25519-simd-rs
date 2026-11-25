From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.ScalarBytes
 execution.ScalarWords execution.InstructionRoute memory.ByteMemory memory.WriteTrace abi.SysV.
From Machine Require abi.FrameRestore.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ScoreSaved.
Import ListNotations. Local Open Scope Z_scope.
Definition start pol:=match pol with Zip215=>74 | Dalek=>565 end.
Local Notation scatter:=Zip215.ScatterBytes.address.
Definition jump pol:list line:=[(start pol+14,5%nat,Jump(scatter-(ScoreSetup.callee pol+(start pol+19))))].
Lemma image pol : linked (ScoreSetup.code pol) (FrameRestore.path (start pol)) /\ linked (ScoreSetup.code pol) (jump pol).
Proof. destruct pol;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute pol bias:=segment (bias+ScoreSetup.callee pol) (ScoreSetup.code pol) 8.
Definition arguments e mask s:=regs s 0%nat=mask /\ regs s 7%nat=Rows.frame e+856 /\
 regs s 6%nat=output e /\ regs s 2%nat=regs e 6%nat.
Record entry bias parent e p q mask:Prop:=Entry {
 target:ip q=bias+scatter; writes:accounted e (writable e) q; words:well_formed(machine q);
 sp:regs(machine q) 4%nat=ScoreFrame.top e;
 args:arguments e mask (machine q); ret:read_word(mem(machine q))(ScoreFrame.top e)=bias+parent+539;
 left:regs(machine q) 12%nat=Prologue.rows_left(regs e 6%nat); metadata:StageEntry.metadata e (mem(machine q));
 saved:StageEntry.saved_caller e (machine q); restart:ChunkContext.bindings e (machine q);
 memory:mem(machine q)=mem(machine p); history:log q=log p
}.
Theorem checked pol bias parent e caller p mask : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=bias+ScoreSetup.callee pol+start pol -> accounted e (writable e) p -> well_formed(machine p) ->
 ScoreSaved.frame bias parent e caller (machine p) -> arguments e mask (machine p) ->
 exists q,execute pol bias p=Some q /\ entry bias parent e p q mask.
Proof.
 intros P I PC A W F Args;set (s:=machine p) in *;set (o:=bias+ScoreSetup.callee pol) in *;set (t:=ScoreFrame.top e).
 destruct(stack_ok _ P) as [[L H] _].
 destruct(FrameRestore.execute o _ (start pol) s (carry p) t (regs(machine caller)) (proj1(image pol))
     ltac:(unfold t,ScoreFrame.top,Rows.frame,Return.sp in *;lia) (ScoreSaved.fp _ _ _ _ _ F) (ScoreSaved.slots _ _ _ _ _ F))
     as [Pop [M [SP [G Keep]]]];set (u:=FrameRestore.restored t s) in *.
 assert (Jump:run 1 (ScalarBytes.fetch o (ScoreSetup.code pol)) (State(Running(start pol+14)) u (carry p))=
     Some(State(Running(scatter-ScoreSetup.callee pol)) u (carry p),[])).
 { apply (InstructionRoute.checked _ _ _ (proj2(image pol)));cbn [jump follow step option_map loc cpu_state cf app];
   rewrite Z.eqb_refl;cbn [option_map app];f_equal;f_equal;f_equal;f_equal;ring. }
 pose proof(run_append _ _ _ _ _ Pop _ _ _ Jump) as R.
 destruct(mapped_now _ _ _ I _ _ _ A (ScoreSetup.image pol)) as [Map Sep].
 destruct(at_segment _ _ p o _ 8 (start pol) _ _ A PC Map Sep R (Forall_nil _)) as [End Paid].
 eexists;split;[exact End|constructor];cbn [LinkedRun.finish loc absolute ip machine log cpu_state];fold u.
 - unfold o;ring.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ W End).
 - exact SP.
 - unfold arguments in *;rewrite (Keep 0%nat),(Keep 7%nat),(Keep 6%nat),(Keep 2%nat) by (simpl;intuition congruence);exact Args.
 - rewrite M;exact (ScoreSaved.link _ _ _ _ _ F).
 - rewrite G by (simpl;tauto);exact (ScoreSaved.counter _ _ _ _ _ F).
 - rewrite M;exact (ScoreSaved.metadata _ _ _ _ _ F).
 - split;[rewrite M;exact (ScoreSaved.spills _ _ _ _ _ F)|rewrite G by (simpl;tauto);exact (ScoreSaved.outer_bp _ _ _ _ _ F)].
 - constructor.
   + unfold Prologue.context_registers,Prologue.output_registers;rewrite (G 15%nat),(G 13%nat),(G 14%nat) by (simpl;tauto);exact(ScoreSaved.globals _ _ _ _ _ F).
   + rewrite G by (simpl;tauto);exact(ScoreSaved.descriptor _ _ _ _ _ F).
   + rewrite M;exact(ScoreSaved.tables _ _ _ _ _ F).
 - exact M.
 - apply app_nil_r.
Qed.
