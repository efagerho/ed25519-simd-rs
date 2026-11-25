From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.MemoryGeometry memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return BatchScalar.
From Ed25519Simd.VerifyBatch Require PreparedReturn.
Local Open Scope Z_scope.

Definition region e x:=span (scratch e) 25344 x \/ span (Rows.frame e+768) 64 x.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record data e s:Prop:=Data {
 operands:PreparedInputs.operands e s;
 table:PreparedTables.table e s;
 selected:forall j,(j<8)%nat ->
   let ptr:=read_word (mem s) (Rows.frame e+768+8*Z.of_nat j) in
   (RootDecision.decodes false e j -> ptr=scratch e+PrepareChunk.Caller.table_offset j) /\
   (~RootDecision.decodes false e j -> ptr=regs e 8%nat)
}.

Lemma from_prepare pol bias o e q : PreparedReturn.result pol bias o e q -> data e (machine q).
Proof. intro Q;constructor;[exact (PreparedReturn.operands _ _ _ _ _ Q)|exact (PreparedReturn.key_tables _ _ _ _ _ Q)|exact (PreparedReturn.selected _ _ _ _ _ Q)]. Qed.

Lemma keep e s t : preserved (region e) (mem s) (mem t) -> data e s -> data e t.
Proof.
 intros M [O Tab Sel];constructor.
 - eapply PreparedInputs.keep;[|exact O];intros x X;apply M;left;
   unfold PreparedInputs.operand_bytes,PreparedInputs.prefix,BatchDecode.point,BatchDecode.point_offset,span in *;lia.
 - eapply PreparedTables.keep;[|exact Tab];intros x X;apply M;left;unfold span,TableEntry.tables in *;lia.
 - intros j J;cbv zeta;pose proof(Sel j J) as Pick;cbv zeta in Pick.
   assert (E:read_word (mem t) (Rows.frame e+768+8*Z.of_nat j)=read_word (mem s) (Rows.frame e+768+8*Z.of_nat j)).
   { apply preserved_read with (outside:=region e);[exact M|];intros k K;change (0<=k<8) in K;right;unfold span;lia. }
   now rewrite E.
Qed.
End Iteration.
