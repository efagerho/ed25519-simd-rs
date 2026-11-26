From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.KeyTable Require Frame.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require TableEntry.
Import ListNotations. Local Open Scope Z_scope.

Definition top pol e:=KeyTable.Frame.staging (TableEntry.frame pol e).
Definition keep pol e x:=~span (top pol e-1360) 2320 x /\ ~span (TableEntry.point e) 1280 x /\ ~span (TableEntry.tables e) 21760 x.
Definition expected pol bias e (s:cpu):=spill (regs s) (store_word (mem s) (TableEntry.frame pol e) (bias+TableEntry.site+185))
 (TableEntry.frame pol e) KeyTable.Frame.saved_regs.
Definition retained pol bias e caller s:=preserved (keep pol e) (expected pol bias e caller) (mem s).

Lemma on_entry pol bias e p a : TableEntry.entry pol bias e p a ->
 Frame.saved (TableEntry.frame pol e) a=expected pol bias e (machine p).
Proof.
 intros E;unfold Frame.saved,expected;rewrite (TableEntry.memory_after _ _ _ _ _ E).
 apply spill_ext;intros r K;apply (TableEntry.caller_regs _ _ _ _ _ E);
 destruct K as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];discriminate.
Qed.
