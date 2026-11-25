From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require TableFrame TableIdentity.
Import ListNotations. Local Open Scope Z_scope.

Definition top pol e:=KeyTable.Frame.staging (TableEntry.frame pol e).
Definition keep pol e x:=~span (top pol e-1360) 2320 x /\ ~span (TableEntry.point e) 1280 x /\ ~span (TableEntry.tables e) 21760 x.
Definition expected pol bias e (s:cpu):=spill (regs s) (store_word (mem s) (TableEntry.frame pol e) (bias+TableEntry.site+185))
 (TableEntry.frame pol e) TableFrame.saved_regs.
Definition retained pol bias e caller s:=preserved (keep pol e) (expected pol bias e caller) (mem s).

Lemma spill_ext rs rs' top m xs : (forall r,In r xs -> rs r=rs' r) -> spill rs m top xs=spill rs' m top xs.
Proof.
 revert top m;induction xs as [|r xs IH];intros t m G;[reflexivity|].
 cbn [spill];rewrite (G r (or_introl eq_refl));apply IH;intros k K;apply G;now right.
Qed.
Lemma prologue pol bias e p a b : TableEntry.entry pol bias e p a -> TableFrame.initialized pol bias e a b ->
 mem(machine b)=expected pol bias e (machine p).
Proof.
 intros E B;unfold expected;rewrite (TableFrame.memory_after _ _ _ _ _ B),(TableEntry.memory_after _ _ _ _ _ E).
 apply spill_ext;intros r K;apply (TableEntry.caller_regs _ _ _ _ _ E);destruct K as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];discriminate.
Qed.
Lemma identities pol e x : keep pol e x -> ~TableIdentity.occupied (TableIdentity.first e) 8 x.
Proof. intros [_ [_ T]] [j [J R]];apply T;unfold span,TableIdentity.center,TableIdentity.first in *;lia. Qed.

Lemma slots pol e x : placement e -> TableEntry.frame pol e-48<=x<TableEntry.frame pol e+8 -> keep pol e x.
Proof.
 intros P X;pose proof(scratch_stack _ P) as Apart;unfold keep,top,KeyTable.Frame.staging,KeyTable.Frame.allocation,KeyTable.Frame.align64.
 change KeyTable.Frame.saved_size with 48;pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia)).
 unfold TableEntry.frame,BatchScalar.common_top,Rows.frame,sp,TableEntry.point,TableEntry.tables,span,disjoint in *;destruct pol;intuition lia.
Qed.
Lemma saved pol bias e caller s i r : placement e -> retained pol bias e caller s ->
 well_formed caller -> nth_error TableFrame.saved_regs i=Some r ->
 read_word (mem s) (TableEntry.frame pol e-8*(1+Z.of_nat i))=regs caller r.
Proof.
 intros P M W At;assert ((i<6)%nat) by (change 6%nat with (length TableFrame.saved_regs);apply nth_error_Some;rewrite At;discriminate).
 rewrite <- (spilled_word _ (store_word (mem caller) (TableEntry.frame pol e) (bias+TableEntry.site+185))
   (TableEntry.frame pol e) _ _ _ (proj1 W) At).
 apply preserved_read with (outside:=keep pol e);[exact M|intros k K;change (0<=k<8) in K;apply slots;[exact P|lia]].
Qed.
Lemma link pol bias e caller s : placement e -> retained pol bias e caller s -> WordBounds.word64(bias+TableEntry.site+185) ->
 read_word (mem s) (TableEntry.frame pol e)=bias+TableEntry.site+185.
Proof.
 intros P M W;set (t:=TableEntry.frame pol e) in *.
 transitivity (read_word (expected pol bias e caller) t).
 - apply preserved_read with (outside:=keep pol e);[exact M|intros k K;change (0<=k<8) in K;apply slots;[exact P|unfold t;lia]].
 - unfold expected;fold t;apply read_word_exact;[exact W|intros k K;rewrite outside_spill by lia;unfold store_word;apply write_at,K].
Qed.
