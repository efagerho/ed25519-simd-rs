From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory abi.SysV.
From Ed25519Simd.KeyTable Require TablePass TableStart.
From Ed25519Simd.KeyTable Require Import CallLayout.
Import ListNotations. Local Open Scope Z_scope.

Definition iteration bias e p ks:=bind (TableAddCall.enter bias p) (fun a=>
 bind (TableAdd.execute bias e a) (fun b=>bind (TableNextDigit.execute bias b) (fun c=>TablePass.execute bias c ks))).
Definition private e x:=CallLayout.stage e-1360<=x<CallLayout.stage e \/ span (CallLayout.point_ptr e) 1280 x.
Record at_multiple (root:cpu) bias e digit p:Prop:=At {
 pc:ip p=CallLayout.base bias+1947;
 writes:accounted root (writable e) p;
 words:well_formed(machine p);
 pointers:TableMultiple.pointers e digit (machine p)
}.
Record step (root:cpu) bias e digit p q:Prop:=Step {
 checkpoints:exists a b c,TableAddCall.entry root bias e p a /\ TableAdd.post root bias e a b /\
  TableMultiple.positioned root bias e (digit+1) b c /\ TablePass.post root bias e (digit+1) c q;
 reached:at_multiple root bias e (digit+1) q;
 outside:preserved (fun x=>~private e x /\ ~TablePackRows.area e (digit+1) x) (mem(machine p)) (mem(machine q))
}.
Theorem next (root:cpu) bias e digit p ks : placement e -> loaded root bias e ->
 (bias+DecoderBytes.address) mod 64=0 -> 1<=digit<8 -> at_multiple root bias e digit p ->
 exists q bank,iteration bias e p ks=Some(q,bank) /\ step root bias e digit p q.
Proof.
 intros P I Al N [PC Acc W Ptr].
 destruct(TableAddCall.checked _ _ _ _ _ P I N PC Acc W Ptr) as [a [Call A]].
 destruct(TableAdd.checked _ _ _ _ _ P I A) as [b [Add B]].
 assert (Saved:forall r,In r sysv_saved -> regs(machine b) r=regs(machine p) r) by
   (intros r R;rewrite (TableAdd.saved _ _ _ _ _ B r R);apply (TableAddCall.saved _ _ _ _ _ A),R).
 assert (BP:TableMultiple.pointers e digit (machine b)).
 { destruct Ptr;constructor;[exact (TableAdd.stack _ _ _ _ _ B)|..];rewrite Saved by (cbn;tauto);assumption. }
 destruct(TableNextDigit.checked root bias e digit b P I N (TableAdd.address _ _ _ _ _ B) (TableAdd.writes _ _ _ _ _ B)
   (TableAdd.words _ _ _ _ _ B) BP) as [c [Loop C]].
 destruct(TablePass.checked root bias e (digit+1) b c ks P I Al ltac:(lia) C) as [q [bank [Pass Q]]].
 exists q,bank;split;[unfold iteration;rewrite Call;cbn [bind];rewrite Add;cbn [bind];rewrite Loop;exact Pass|constructor].
 - exists a,b,c;auto.
 - constructor;[exact (TablePass.address _ _ _ _ _ _ Q)|exact (TablePass.writes _ _ _ _ _ _ Q)|exact (TablePass.words _ _ _ _ _ _ Q)|exact (TablePass.pointers _ _ _ _ _ _ Q)].
 - intros x [Priv Free];unfold private in Priv;rewrite (TablePass.outside _ _ _ _ _ _ Q).
   2:{ split;[tauto || lia|split;[exact Free|lia]]. }
   rewrite (TableMultiple.flat _ _ _ _ _ _ C),(TableAdd.outside _ _ _ _ _ B).
   2:{ change (~(CallLayout.point_ptr e<=x<CallLayout.point_ptr e+1280 \/ CallLayout.stage e-1344-16<=x<PointFrame.entry_rsp (TableAddLayout.layout bias e) TableAddLayout.pad)).
       rewrite TableAddLayout.entry_sp;unfold span in Priv;lia. }
   rewrite (TableAddCall.pushed _ _ _ _ _ A);unfold store_word;apply write_outside;lia.
Qed.

Fixpoint execute fuel bias e p ks:=match fuel with O=>Some(p,ks) | S n=>
 bind (iteration bias e p ks) (fun '(q,bank)=>execute n bias e q bank) end.
(* Each constructor records one actual cached addition, the increment, and the
   following packed rows. The exit PC is the comparison for digit eight. *)
Inductive iterations root bias e : nat->Z->cursor->cursor->Prop:=
 | finished d p:iterations root bias e O d p p
 | continued n d p q last:step root bias e d p q -> iterations root bias e n (d+1) q last ->
    iterations root bias e (S n) d p last.
Theorem complete (root:cpu) bias e n : forall digit p ks,placement e -> loaded root bias e ->
 (bias+DecoderBytes.address) mod 64=0 -> 1<=digit -> digit+Z.of_nat n<=8 -> at_multiple root bias e digit p ->
 exists q bank,execute n bias e p ks=Some(q,bank) /\ at_multiple root bias e (digit+Z.of_nat n) q /\ iterations root bias e n digit p q.
Proof.
 induction n as [|n IH];intros d p ks P I Al Low High A.
 - exists p,ks;split;[reflexivity|rewrite Z.add_0_r;split;[exact A|constructor]].
 - destruct(next _ _ _ d p ks P I Al ltac:(lia) A) as [a [k [Run Q]]].
   destruct(IH (d+1) a k P I Al ltac:(lia) ltac:(lia) (reached _ _ _ _ _ _ Q)) as [t [bank [Rest [End Path]]]].
   exists t,bank;split;[cbn [execute];rewrite Run;exact Rest|split;[replace (d+Z.of_nat(S n)) with (d+1+Z.of_nat n) by lia;exact End|econstructor;eassumption]].
Qed.
Lemma preserves_parent (root:cpu) bias e n d p q caller :
 1<=d -> d+Z.of_nat n<=8 -> iterations root bias e n d p q ->
 preserved (CallLayout.keep e) caller (mem(machine p)) -> preserved (CallLayout.keep e) caller (mem(machine q)).
Proof.
 intros Lo Hi Steps;induction Steps as [|n d p a q Q Steps IH];intro Kept;[exact Kept|].
 apply IH;[lia|lia|];intros x Keep;rewrite (outside _ _ _ _ _ _ Q).
 - exact (Kept x Keep).
 - destruct Keep as [Stack [Point Tables]];split.
   + unfold private,CallLayout.stage,span in *;tauto || lia.
   + intro X;apply Tables,(TablePackRows.in_table _ (d+1) _ ltac:(lia) X).
Qed.
Definition observe bias e p ks:=bind (TableStart.execute bias p) (fun first=>
 bind (TablePass.execute bias first ks) (fun '(a,bank)=>execute 7 bias e a bank)).
