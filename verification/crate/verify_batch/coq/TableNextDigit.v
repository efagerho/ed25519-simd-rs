From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableAddLayout TableMultiple.
Import ListNotations. Local Open Scope Z_scope.
Definition tail:list line:=[(1974,3%nat,Inc32 15);(1977,5%nat,Jump (110-1982))].
Lemma image:linked TableFrame.text tail.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias:=segment (TableFrame.base bias) TableFrame.text 4.

Theorem checked pol bias e n p : placement e -> loaded pol bias (mem e) (writable e) -> 1<=n<8 ->
 ip p=TableAddLayout.back bias -> accounted e (writable e) p -> well_formed(machine p) -> TableMultiple.pointers pol e n (machine p) ->
 exists q,execute bias p=Some q /\ TableMultiple.positioned pol bias e (n+1) p q.
Proof.
 intros P I N PC Acc W Ptr;set (s:=machine p) in *;set (o:=TableFrame.base bias).
 set (u:=with_zf (set s 15 (n+1)) false).
 assert (Loop:run 2 (ScalarBytes.fetch o TableFrame.text) (State(Running 1974) s (LinkedRun.carry p))=
    Some(State(Running 110) u (LinkedRun.carry p),[])).
 { apply (InstructionRoute.checked _ _ _ image);cbn [tail follow step cpu_state cf loc option_map app].
   rewrite (TableMultiple.multiple _ _ _ _ Ptr),Z.mod_small by lia.
   rewrite (proj2(Z.eqb_neq (n+1) 0) ltac:(lia));reflexivity. }
 set (a:=TableMultiple.pos e n) in *;set (b:=TableMultiple.neg e n) in *.
 destruct(scratch_ok _ P) as [[Lo Hi] _].
 assert (Fits:word64 a /\ word64 b /\ word64(a+160) /\ word64(b-160))
   by (unfold a,b,TableMultiple.pos,TableMultiple.neg,TableIdentity.first,TableEntry.tables,word64;lia).
 destruct Fits as [A [B [Up Down]]].
 destruct(TableMultiple.shifted o u (LinkedRun.carry p) a b A B Up Down
   (TableMultiple.positive _ _ _ _ Ptr) (TableMultiple.negative _ _ _ _ Ptr)) as [t [c [Move [G [M V]]]]].
 pose proof(run_append _ _ _ _ _ Loop _ _ _ Move) as Run.
 destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 destruct(at_segment _ _ p o TableFrame.text 4 1974 _ _ Acc PC Map Sep Run (Forall_nil _)) as [Next Paid].
 eexists;split;[exact Next|constructor].
 - reflexivity.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ W Next).
 - change (TableMultiple.pointers pol e (n+1) t);destruct Ptr;constructor;rewrite G;cbn [u with_zf set set_regs regs put Nat.eqb];try assumption.
   + unfold a,TableMultiple.pos;ring.
   + unfold b,TableMultiple.neg;ring.
   + reflexivity.
 - exact M.
 - exact V.
 - apply app_nil_r.
Qed.
