From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls abi.SysV memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Return StageEntry.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Local Open Scope Z_scope.

(* These caller values are reused when eight more descriptors enter the
   loop. R12, RSP and the outer register saves have their own exit clauses. *)
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record bindings e s:Prop:=Bindings {
 arguments:Prologue.context_registers e s;
 descriptor:BatchWindow.next_descriptor e (regs s 3%nat);
 tables:CallerSpills.table_arguments e (mem s)
}.
Lemma preserve e s t:bindings e s -> (forall g,In g sysv_saved -> regs t g=regs s g) ->
 preserved (fun x=>Rows.frame e+936<=x<Rows.frame e+952) (mem s) (mem t) -> bindings e t.
Proof.
 intros [[Scratch [N Out]] Row T] G M;constructor.
 - unfold Prologue.context_registers,Prologue.output_registers;rewrite (G 15%nat),(G 13%nat),(G 14%nat) by (simpl;tauto);auto.
 - rewrite G by (simpl;tauto);exact Row.
 - exact(CallerSpills.keep_tables _ _ _ M T).
Qed.
End Iteration.
