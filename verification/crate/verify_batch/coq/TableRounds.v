From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory abi.SysV.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require TablePass.
Import ListNotations. Local Open Scope Z_scope.

Definition iteration pol bias e p ks:=bind (TableAddCall.enter bias p) (fun a=>
 bind (TableAdd.execute pol bias e a) (fun b=>bind (TableNextDigit.execute bias b) (fun c=>TablePass.execute bias c ks))).
Definition private pol e x:=TableAddLayout.stage pol e-1360<=x<TableAddLayout.stage pol e \/ span (TableEntry.point e) 1280 x.
Record at_multiple pol bias e digit p:Prop:=At {
 pc:ip p=TableFrame.base bias+1947;
 writes:accounted e (writable e) p;
 words:well_formed(machine p);
 pointers:TableMultiple.pointers pol e digit (machine p)
}.
Record step pol bias e digit p q:Prop:=Step {
 checkpoints:exists a b c,TableAddCall.entry pol bias e p a /\ TableAdd.post pol bias e a b /\
  TableMultiple.positioned pol bias e (digit+1) b c /\ TablePass.post pol bias e (digit+1) c q;
 reached:at_multiple pol bias e (digit+1) q;
 outside:preserved (fun x=>~private pol e x /\ ~TablePackRows.area e (digit+1) x) (mem(machine p)) (mem(machine q))
}.
Theorem next pol bias e digit p ks : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> 1<=digit<8 -> at_multiple pol bias e digit p ->
 exists q bank,iteration pol bias e p ks=Some(q,bank) /\ step pol bias e digit p q.
Proof.
 intros P I Al N [PC Acc W Ptr].
 destruct(TableAddCall.checked _ _ _ _ _ P I N PC Acc W Ptr) as [a [Call A]].
 destruct(TableAdd.checked _ _ _ _ _ P I A) as [b [Add B]].
 assert (Saved:forall r,In r sysv_saved -> regs(machine b) r=regs(machine p) r) by
   (intros r R;rewrite (TableAdd.saved _ _ _ _ _ B r R);apply (TableAddCall.saved _ _ _ _ _ A),R).
 assert (BP:TableMultiple.pointers pol e digit (machine b)).
 { destruct Ptr;constructor;[exact (TableAdd.stack _ _ _ _ _ B)|..];rewrite Saved by (cbn;tauto);assumption. }
 destruct(TableNextDigit.checked pol bias e digit b P I N (TableAdd.address _ _ _ _ _ B) (TableAdd.writes _ _ _ _ _ B)
   (TableAdd.words _ _ _ _ _ B) BP) as [c [Loop C]].
 destruct(TablePass.checked pol bias e (digit+1) b c ks P I Al ltac:(lia) C) as [q [bank [Pass Q]]].
 exists q,bank;split;[unfold iteration;rewrite Call;cbn [bind];rewrite Add;cbn [bind];rewrite Loop;exact Pass|constructor].
 - exists a,b,c;auto.
 - constructor;[exact (TablePass.address _ _ _ _ _ _ Q)|exact (TablePass.writes _ _ _ _ _ _ Q)|exact (TablePass.words _ _ _ _ _ _ Q)|exact (TablePass.pointers _ _ _ _ _ _ Q)].
 - intros x [Priv Free];unfold private in Priv;rewrite (TablePass.outside _ _ _ _ _ _ Q).
   2:{ split;[unfold TableAddLayout.stage in Priv;tauto || lia|exact Free]. }
   rewrite (TableMultiple.flat _ _ _ _ _ _ C),(TableAdd.outside _ _ _ _ _ B).
   2:{ change (~(TableEntry.point e<=x<TableEntry.point e+1280 \/ TableAddLayout.stage pol e-1344-16<=x<PointFrame.entry_rsp (TableAddLayout.layout pol bias e) TableAddLayout.pad)).
       rewrite TableAddLayout.entry_sp;unfold span in Priv;lia. }
   rewrite (TableAddCall.pushed _ _ _ _ _ A);unfold store_word;apply write_outside;lia.
Qed.

Fixpoint execute fuel pol bias e p ks:=match fuel with O=>Some(p,ks) | S n=>
 bind (iteration pol bias e p ks) (fun '(q,bank)=>execute n pol bias e q bank) end.
(* Each constructor records one actual cached addition, the increment, and the
   following packed rows. The exit PC is the comparison for digit eight. *)
Inductive iterations pol bias e : nat->Z->cursor->cursor->Prop:=
 | finished d p:iterations pol bias e O d p p
 | continued n d p q last:step pol bias e d p q -> iterations pol bias e n (d+1) q last ->
    iterations pol bias e (S n) d p last.
Theorem complete pol bias e n : forall digit p ks,placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> 1<=digit -> digit+Z.of_nat n<=8 -> at_multiple pol bias e digit p ->
 exists q bank,execute n pol bias e p ks=Some(q,bank) /\ at_multiple pol bias e (digit+Z.of_nat n) q /\ iterations pol bias e n digit p q.
Proof.
 induction n as [|n IH];intros d p ks P I Al Low High A.
 - exists p,ks;split;[reflexivity|rewrite Z.add_0_r;split;[exact A|constructor]].
 - destruct(next _ _ _ d p ks P I Al ltac:(lia) A) as [a [k [Run Q]]].
   destruct(IH (d+1) a k P I Al ltac:(lia) ltac:(lia) (reached _ _ _ _ _ _ Q)) as [t [bank [Rest [End Path]]]].
   exists t,bank;split;[cbn [execute];rewrite Run;exact Rest|split;[replace (d+Z.of_nat(S n)) with (d+1+Z.of_nat n) by lia;exact End|econstructor;eassumption]].
Qed.
Lemma preserves_parent pol bias e n d p q caller :
 1<=d -> d+Z.of_nat n<=8 -> iterations pol bias e n d p q ->
 TableParentFrame.retained pol bias e caller (machine p) -> TableParentFrame.retained pol bias e caller (machine q).
Proof.
 intros Lo Hi Steps;induction Steps as [|n d p a q Q Steps IH];intro Kept;[exact Kept|].
 apply IH;[lia|lia|];intros x Keep;rewrite (outside _ _ _ _ _ _ Q).
 - exact (Kept x Keep).
 - destruct Keep as [Stack [Point Tables]];split.
   + unfold private,TableAddLayout.stage,TableProduct.frame,TableParentFrame.top,span in *;tauto || lia.
   + intro X;apply Tables,(TablePackRows.in_table _ (d+1) _ ltac:(lia) X).
Qed.
Definition observe pol bias e p ks:=bind (TablePacking.observe bias p ks) (fun '(a,bank)=>execute 7 pol bias e a bank).
Theorem from_eligible pol bias e before p ks:placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> EligibleLanes.post pol bias e before p -> regs(machine p) 14%nat<>0 ->
 exists q bank a,observe pol bias e p ks=Some(q,bank) /\ at_multiple pol bias e 8 q /\
   TableSignedWords.signed e 1 (TablePackedInputs.column e (machine p)) (machine a) /\ iterations pol bias e 7 1 a q /\
   TableParentFrame.retained pol bias e (machine p) (machine q).
Proof.
 intros P I Al E Live;destruct(TableSignedWords.first _ _ _ _ _ ks P I Al E Live) as [a [k [m [Run [Mask [Pack Rows]]]]]].
 assert (A:at_multiple pol bias e 1 a) by (constructor;[exact (TablePacking.address _ _ _ _ _ _ _ Pack)|exact (TablePacking.writes _ _ _ _ _ _ _ Pack)|
  exact (TablePacking.words _ _ _ _ _ _ _ Pack)|exact (TablePacking.arguments _ _ _ _ _ _ _ Pack)]).
 destruct(complete pol bias e 7 1 a k P I Al ltac:(lia) ltac:(lia) A) as [q [bank [R [At Steps]]]].
 exists q,bank,a;split;[unfold observe;rewrite Run;exact R|split;[exact At|split;[exact Rows|split;[exact Steps|]]]].
 apply (preserves_parent pol bias e 7 1 a q (machine p) ltac:(lia) ltac:(lia) Steps);intros x Keep.
 destruct(TablePacking.trace _ _ _ _ _ _ _ Pack) as [ws [_ [_ [Safe Replay]]]];rewrite Replay,(WriteTrace.frame _ _ Safe).
 - exact (TableMask.parent _ _ _ _ _ _ Mask x Keep).
 - destruct Keep as [_ [_ T]];intro X;apply T,(TablePackRows.in_table _ 1 _ ltac:(lia) X).
Qed.
