From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.WordSemantics
 execution.MaskTrace execution.MaskTransfer execution.MappedFetch.
Import ListNotations. Local Open Scope Z_scope.

(* KORTESTW k,k reads sixteen bits. ZF means all bits clear and CF
   means all bits set. The instruction leaves the predicate bank intact. *)
Definition tested p v:=Cursor (word(ip p+4)) (with_zf (machine p) (v=?0)) (Some(v=?65535)) (log p).
Definition test k p (ks:bank):=let bs:=MaskTrace.encoding (TestMask k) in
 if (k<?8)%nat then
 if list_eq_dec Z.eq_dec (snapshot (mem(machine p)) (ip p) (length bs)) bs
 then Some(tested p (mask16(ks k))) else None else None.
Lemma mapped_test p ks k : (k<8)%nat -> mapped (mem(machine p)) (ip p) (MaskTrace.encoding (TestMask k)) ->
 test k p ks=Some(tested p (mask16(ks k))).
Proof. intros K M;unfold test;rewrite (proj2(Nat.ltb_lt _ _) K),(snapshot_mapped _ _ _ M);destruct(list_eq_dec _ _ _);congruence. Qed.
