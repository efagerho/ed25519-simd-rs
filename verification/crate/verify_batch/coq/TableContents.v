From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.KeyTable Require Rows Image.
From Ed25519Simd.VerifyBatch Require Import Return TableRowMeaning TableRoundMeaning.
From Ed25519Simd.VerifyBatch Require TableRounds.
Local Open Scope Z_scope.

Definition center e s:=forall j i,(j<8)%nat -> (i<20)%nat ->
 stored e 0 true s j i=KeyTable.Image.identity_word (Z.of_nat i).
Definition contents e w s:=center e s /\ (cache_bounds false w -> prior_rows e 8 s w).

Lemma slot_same e d sign j x : (j<8)%nat -> 0<=d<=8 ->
 TablePackRows.row e d sign (Z.of_nat j)<=x<TablePackRows.row e d sign (Z.of_nat j)+160 ->
 span (TableEntry.tables e) 21760 x.
Proof. intros J D;unfold TablePackRows.row,TableMultiple.pos,TableMultiple.neg,TableIdentity.first,span;destruct sign;lia. Qed.
Lemma center_through pol bias e n d p q : placement e -> 1<=d -> d+Z.of_nat n<=8 ->
 TableRounds.iterations pol bias e n d p q -> center e (machine p) -> center e (machine q).
Proof.
 intros P L H Run;induction Run as [d p|n d p a q Step Tail IH];intros C;[exact C|apply IH;[lia|lia|]].
 intros j i J N;rewrite <-(C j i J N);unfold stored.
 apply preserved_read with (outside:=fun x=>~TableRounds.private pol e x /\ ~TablePackRows.area e (d+1) x).
 - exact (TableRounds.outside _ _ _ _ _ _ Step).
 - intros k K;change (0<=k<8) in K;set (t:=TablePackRows.row e 0 true (Z.of_nat j)).
   assert (R:t<=t+8*Z.of_nat i+k<t+160) by lia.
   split;[|exact (disjoint_rows _ (d+1) 0 true j _ ltac:(lia) ltac:(lia) J R)].
   pose proof(slot_same e 0 true j _ J ltac:(lia) R);pose proof(TableAddLayout.stack pol e);destruct(scratch_stack _ P).
   all: unfold TableRounds.private,TableEntry.tables,TableEntry.point,span in *;lia.
Qed.
Lemma scale_one P : scale 1 P=P.
Proof. change (plus P identity=P);now rewrite plus_comm,plus_identity. Qed.

Lemma start pol bias e p m a bank : placement e -> TableMask.ready pol bias e p m bank ->
 TablePacking.packed pol bias e 1 m a bank ->
 TableSignedWords.signed e 1 (TablePackedInputs.column e (machine p)) (machine a) ->
 let w:=point e (machine p) in center e (machine a) /\ staged w pol e (machine a) /\
 (cache_bounds false w -> multiple w 1 (point e (machine a)) /\ prior_rows e 1 (machine a) w).
Proof.
 intros P Mask Pack Signed w;destruct(TablePacking.trace _ _ _ _ _ _ _ Pack) as [ws [_ [_ [Safe Replay]]]].
 assert (Keep:preserved (fun x=>~TablePackRows.area e 1 x) (mem(machine m)) (mem(machine a))) by
   (intros x X;rewrite Replay;apply (WriteTrace.frame _ _ Safe),X).
 split.
 - intros j i J N;rewrite <-(TableMask.center _ _ _ _ _ _ Mask j (Z.of_nat i) J ltac:(lia));unfold stored.
   replace (TableIdentity.center (TableIdentity.first e) j) with (TablePackRows.row e 0 true (Z.of_nat j))
     by (unfold TablePackRows.row,TableMultiple.pos,TableIdentity.center;ring).
   apply preserved_read with (outside:=fun x=>~TablePackRows.area e 1 x);[exact Keep|].
   intros k K;change (0<=k<8) in K;apply (disjoint_rows e 1 0 true j _ ltac:(lia) ltac:(lia) J);lia.
 - split.
   + intros n N;set (j:=(n mod 8)%nat);set (i:=(n/8)%nat);assert (J:(j<8)%nat) by (apply Nat.mod_upper_bound;lia).
     assert (Idx:n=(i*8+j)%nat) by (unfold i,j;pose proof(Nat.div_mod n 8 ltac:(lia));lia).
     assert (I:(i<15)%nat) by lia.
     change (cache pol e (machine a) n=Rows.staged DecoderProduct.kernel w n).
     rewrite Idx;change (cell (cache pol e (machine a)) i j=cell (Rows.staged DecoderProduct.kernel w) i j).
     rewrite Rows.stage_cell by assumption.
     unfold cell,cache,buffer_words;rewrite Nat2Z.inj_add,Nat2Z.inj_mul;change (Z.of_nat 8) with 8.
     replace (TableAddLayout.stage pol e+8*(Z.of_nat i*8+Z.of_nat j)) with
       (TableProduct.frame pol e+64*Z.of_nat i+8*Z.of_nat j) by (unfold TableAddLayout.stage;ring).
     unfold w;rewrite <-(TableRowMeaning.column e (machine p) j i ltac:(lia));rewrite <-(TableMask.staged _ _ _ _ _ _ Mask j i J I).
     apply preserved_read with (outside:=fun x=>~TablePackRows.area e 1 x);[exact Keep|].
     intros k K;change (0<=k<8) in K;apply (stack_outside pol e 1 _ P ltac:(lia));unfold span,TableAddLayout.stage;lia.
   + intros B;split.
     * apply (keep_multiple w 1 w);[|split;[exact B|intros j G J [R _];now rewrite scale_one]].
       intros k K;apply (words_preserved _ 160 _ _ _ K);intros x X;rewrite Keep;[apply (TableMask.point_after _ _ _ _ _ _ Mask),X|apply point_outside;[lia|exact X]].
     * intros d sign j D J;replace d with 1 by lia;destruct(TableRowMeaning.represents _ _ sign _ _ j Signed B J) as [Bound Rep].
       split;[exact Bound|intros G [R _];rewrite scale_one;apply Rep,R].
Qed.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked pol bias e before p ks:placement e -> LoadedImage.loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> EligibleLanes.post pol bias e before p -> regs(machine p) 14%nat<>0 ->
 exists q bank,TableRounds.observe pol bias e p ks=Some(q,bank) /\ TableRounds.at_multiple pol bias e 8 q /\
 TableParentFrame.retained pol bias e (machine p) (machine q) /\ contents e (point e (machine p)) (machine q).
Proof.
 intros P I Al E Live;destruct(TableSignedWords.first _ _ _ _ _ ks P I Al E Live) as [a [k [m [Begin [Mask [Pack Signed]]]]]].
 assert (A:TableRounds.at_multiple pol bias e 1 a) by (constructor;[exact (TablePacking.address _ _ _ _ _ _ _ Pack)|exact (TablePacking.writes _ _ _ _ _ _ _ Pack)|
  exact (TablePacking.words _ _ _ _ _ _ _ Pack)|exact (TablePacking.arguments _ _ _ _ _ _ _ Pack)]).
 destruct(TableRounds.complete pol bias e 7 1 a k P I Al ltac:(lia) ltac:(lia) A) as [q [bank [Run [At Steps]]]].
 destruct(start _ _ _ _ _ _ _ P Mask Pack Signed) as [Center [Stage Base]].
 exists q,bank;split;[unfold TableRounds.observe;rewrite Begin;exact Run|split;[exact At|split]].
 - apply (TableRounds.preserves_parent pol bias e 7 1 a q (machine p) ltac:(lia) ltac:(lia) Steps);intros x Keep.
   destruct(TablePacking.trace _ _ _ _ _ _ _ Pack) as [ws [_ [_ [Safe Replay]]]];rewrite Replay,(WriteTrace.frame _ _ Safe).
   + exact (TableMask.parent _ _ _ _ _ _ Mask x Keep).
   + destruct Keep as [_ [_ T]];intro X;apply T,(TablePackRows.in_table _ 1 _ ltac:(lia) X).
 - split;[exact (center_through _ _ _ 7 1 _ _ P ltac:(lia) ltac:(lia) Steps Center)|].
   intros B;destruct(Base B) as [One Rows];exact (retained _ _ _ 7 1 _ _ _ P B ltac:(lia) ltac:(lia) Steps One Stage Rows).
Qed.

Lemma preserve e w s t : preserved (span (TableEntry.tables e) 21760) (mem s) (mem t) ->
 contents e w s -> contents e w t.
Proof.
 intros Keep [Center Rows];assert (Slot:forall d sign j i,0<=d<=8 -> (j<8)%nat -> (i<20)%nat ->
    stored e d sign t j i=stored e d sign s j i).
 { intros d sign j i D J N;apply preserved_read with (outside:=span (TableEntry.tables e) 21760);[exact Keep|].
   intros k K;change (0<=k<8) in K;apply (slot_same e d sign j _ J D);lia. }
 split;[intros j i J N;rewrite Slot by lia;apply Center;assumption|].
 intros B d sign j D J;eapply keep_row;[intros i N;apply Slot;lia|apply Rows;assumption].
Qed.
End Iteration.
