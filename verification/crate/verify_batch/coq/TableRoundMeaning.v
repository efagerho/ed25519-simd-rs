From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Curve25519.group Require Import PrimeField Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.CachedAdd Require Import CachedAddSpec.
From Ed25519Simd.KeyTable Require Rows.
From Ed25519Simd.VerifyBatch Require Import Policy Return TableRowMeaning.
From Ed25519Simd.VerifyBatch Require TableRounds.
Local Open Scope Z_scope.

Definition seed w j P:=represents_point true (point_values w j) P /\ Decode.value (Rows.coord w j 2)=1%fp.
Definition multiple w digit v:=cache_bounds false v /\ forall j P,(j<8)%nat -> seed w j P ->
 represents_point true (point_values v j) (scale digit P).
Definition cache pol e s:=buffer_words (mem s) (TableAddLayout.stage pol e).
Definition staged w pol e s:=forall n,(n<120)%nat -> cache pol e s n=Rows.staged DecoderProduct.kernel w n.
Definition row_value e d sign s w j:=let v:=stored e d sign s j in
 (forall i,(i<20)%nat -> 0<=v i<2^52) /\ forall P,seed w j P ->
 represents_cache (scalar_cache false v) (if sign then scale d P else negative (scale d P)).
Definition prior_rows e d s w:=forall k sign j,1<=k<=d -> (j<8)%nat -> row_value e k sign s w j.

Lemma disjoint_rows e d k sign j x : 0<=k<d -> d<=8 -> (j<8)%nat ->
 TablePackRows.row e k sign (Z.of_nat j)<=x<TablePackRows.row e k sign (Z.of_nat j)+160 -> ~TablePackRows.area e d x.
Proof.
 intros K D J R [b [lane [L Hit]]];unfold TablePackRows.row,TableMultiple.pos,TableMultiple.neg in *.
 destruct (Z.lt_trichotomy lane (Z.of_nat j)) as [Sm|[Eq|Big]];destruct b,sign;lia.
Qed.
Lemma point_outside e d x : 1<=d<=8 -> span (TableEntry.point e) 1280 x -> ~TablePackRows.area e d x.
Proof. intros D X Hit;apply (TablePackRows.in_table _ _ _ D) in Hit;unfold span,TableEntry.point,TableEntry.tables in *;lia. Qed.
Lemma stack_outside pol e d x : placement e -> 1<=d<=8 -> span (TableAddLayout.stage pol e) 960 x -> ~TablePackRows.area e d x.
Proof. intros P D X Hit;apply (TablePackRows.in_table _ _ _ D) in Hit;pose proof(TableAddLayout.stack pol e);
 destruct(scratch_stack _ P);unfold span,TableEntry.tables in *;lia. Qed.
Lemma point_stack pol e x : placement e -> span (TableEntry.point e) 1280 x ->
 ~(TableAddLayout.stage pol e-1360<=x<TableAddLayout.stage pol e+960).
Proof. intros P X;pose proof(TableAddLayout.stack pol e);destruct(scratch_stack _ P);unfold span,TableEntry.point in *;lia. Qed.

Lemma words_preserved a n k s t : (k<n)%nat -> preserved (span a (8*Z.of_nat n)) (mem s) (mem t) ->
 buffer_words (mem t) a k=buffer_words (mem s) a k.
Proof. intros K Keep;apply preserved_read with (outside:=span a (8*Z.of_nat n));[exact Keep|].
 intros i I;change (0<=i<8) in I;unfold span;lia. Qed.
Lemma keep_row e d sign s t w j : (forall i,(i<20)%nat -> stored e d sign t j i=stored e d sign s j i) ->
 row_value e d sign s w j -> row_value e d sign t w j.
Proof.
 intros E [B R];split;[intros i N;rewrite E by exact N;apply B,N|].
 intros P Valid;replace (scalar_cache false (stored e d sign t j)) with (scalar_cache false (stored e d sign s j));
 [apply R,Valid|unfold scalar_cache,cache_from_fields;f_equal;try match goal with |-Some _=Some _=>f_equal end;
 apply limbs_ext;intros;symmetry;apply E;lia].
Qed.
Lemma keep_multiple w d s t : (forall n,(n<160)%nat -> t n=s n) -> multiple w d s -> multiple w d t.
Proof.
 intros E [B R];split.
 - intros i j N J;unfold cell;rewrite E by (change (i<20)%nat in N;lia);apply B;assumption.
 - intros j P J Input;rewrite (point_values_ext _ _ _ E J);apply R;assumption.
Qed.

Lemma advance w d before after : cache_bounds false w -> multiple w d before ->
 CachedAddSpec.cached_add_spec true true before (Rows.staged DecoderProduct.kernel w) after ->
 multiple w (d+1) after.
Proof.
 intros W [B Rep] [_ Spec];specialize(Spec (conj (split_cached_point _ B) (Rows.stage_bounds _ _ kernels W))).
 split;[apply strict_split;intros c j C J;apply Spec;assumption|].
 intros j P J [Input Z1];replace (d+1) with (Z.succ d) by lia;rewrite scale_succ,plus_comm.
 eapply represents_equivalent;[intros c C;rewrite coord_value by exact C;apply Spec;assumption|].
 apply add_represents;[apply Rep;[exact J|split;assumption]|apply Rows.staged_rep;auto using kernels].
Qed.

Theorem next pol bias e d p q w : placement e -> 1<=d<8 -> cache_bounds false w ->
 TableRounds.step pol bias e d p q ->
 multiple w d (point e (machine p)) -> staged w pol e (machine p) -> prior_rows e d (machine p) w ->
 multiple w (d+1) (point e (machine q)) /\ staged w pol e (machine q) /\ prior_rows e (d+1) (machine q) w.
Proof.
 intros P D W Step Prev Stage Older;destruct(TableRounds.checkpoints _ _ _ _ _ _ Step) as [a [b [c [A [B [C Pack]]]]]].
 assert (Outside:=TableRounds.outside _ _ _ _ _ _ Step).
 assert (Push:preserved (fun x=>~span (TableAddLayout.stage pol e-8) 8 x) (mem(machine p)) (mem(machine a))).
 { intros x X;rewrite (TableAddCall.pushed _ _ _ _ _ A);apply write_outside,X. }
 assert (Added:multiple w (d+1) (point e (machine c))).
 { apply (advance _ _ _ _ W Prev).
   eapply (CachedAddSpec.spec_ext true true);[| | |exact (TableAdd.point_result _ _ _ _ _ B)].
   - intros k K;symmetry;apply (words_preserved _ 160 _ _ _ K);intros x X;apply Push;
       pose proof(point_stack pol e x P X);unfold span in *;lia.
   - intros k K;rewrite <- (Stage k K);symmetry;apply (words_preserved _ 120 _ _ _ K).
     intros x X;apply Push;change (span (TableAddLayout.stage pol e) 960 x) in X;unfold span in *;lia.
   - intros k K;unfold point,buffer_words;now rewrite (TableMultiple.flat _ _ _ _ _ _ C). }
 assert (Point:forall k,(k<160)%nat ->point e (machine q) k=point e (machine c) k).
 { intros k K;apply (words_preserved _ 160 _ _ _ K);intros x X;apply (TablePass.outside _ _ _ _ _ _ Pack).
   split;[intros H;apply (point_stack pol e x P X);unfold TableAddLayout.stage;lia|apply point_outside;[lia|exact X]]. }
 split;[exact (keep_multiple _ _ _ _ Point Added)|split].
 - intros k K;rewrite <-(Stage k K);apply (words_preserved _ 120 _ _ _ K).
   intros x X;change (span (TableAddLayout.stage pol e) 960 x) in X;apply Outside.
   split;[unfold TableRounds.private;pose proof(point_stack pol e x P);unfold span in *;lia|eapply stack_outside;eauto;lia].
 - intros digit sign j Range J;destruct (Z.eq_dec digit (d+1)) as [->|Lower].
   + destruct Added as [Bounds Rep];destruct(TableRowMeaning.represents _ _ sign _ _ j (TablePass.rows _ _ _ _ _ _ Pack) Bounds J) as [Limbs Cache].
     split;[exact Limbs|intros G Good;apply Cache,Rep;assumption].
   + eapply keep_row;[|apply Older;[lia|exact J]];intros i I;unfold stored;apply preserved_read with
       (outside:=fun x=>~TableRounds.private pol e x /\ ~TablePackRows.area e (d+1) x);[exact Outside|].
     intros k K;change (0<=k<8) in K;set (a0:=TablePackRows.row e digit sign (Z.of_nat j)).
     assert (R:a0<=a0+8*Z.of_nat i+k<a0+160) by lia.
     split;[|apply (disjoint_rows e (d+1) digit sign j _ ltac:(lia) ltac:(lia) J R)].
     assert (InTable:span (TableEntry.tables e) 21760 (a0+8*Z.of_nat i+k)).
     { apply (TablePackRows.in_table e digit _ ltac:(lia));exists sign,(Z.of_nat j);split;[lia|exact R]. }
     pose proof(TableAddLayout.stack pol e);destruct(scratch_stack _ P).
     all: unfold TableRounds.private,TableEntry.tables,TableEntry.point,span in *;lia.
Qed.

Theorem retained pol bias e n d p q w: placement e -> cache_bounds false w -> 1<=d -> d+Z.of_nat n<=8 ->
 TableRounds.iterations pol bias e n d p q ->
 multiple w d (point e (machine p)) -> staged w pol e (machine p) -> prior_rows e d (machine p) w ->
 prior_rows e (d+Z.of_nat n) (machine q) w.
Proof.
 intros P W L H R;induction R as [d p|n d p a q Step Path IH];intros B Init Rows.
 - now rewrite Z.add_0_r.
 - destruct(next pol bias e d p a w P ltac:(lia) W Step B Init Rows) as [A [K More]].
   replace (d+Z.of_nat(S n)) with ((d+1)+Z.of_nat n) by lia;apply IH;try assumption;lia.
Qed.
