From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Rows Return.
From Ed25519Simd.VerifyBatch Require CallerSpills TailCopy.
Local Open Scope Z_scope.

(* The SHA call reads the message address and length straight from the
   transposed descriptor rows. Both table arguments survive in scalar slots. *)
Definition field (length:bool):=if length then 24 else 16.
Definition address e (length:bool) j:=Rows.frame e+(if length then 704 else 640)+8*Z.of_nat j.
Record layout e m:Prop:=Layout {
 tables:CallerSpills.table_arguments e m;
 message:forall kind j,(j<8)%nat -> read_word m (address e kind j)=
  descriptor (mem e) (regs e 7%nat) (TailCopy.row_index e j) (field kind)
}.
Definition needed e x:=span (Rows.frame e+640) 128 x \/ span (Rows.frame e+936) 16 x.
Lemma preserve e m m':preserved (needed e) m m' -> layout e m -> layout e m'.
Proof.
 intros Same [Tab Rows];constructor.
 - eapply CallerSpills.keep_tables;[|exact Tab];intros x X;apply Same;right;unfold span;lia.
 - intros kind j J;rewrite <-(Rows kind j J);apply preserved_read with (outside:=needed e);[exact Same|].
   intros k K;change (0<=k<8) in K;left;unfold address,span;destruct kind;lia.
Qed.
