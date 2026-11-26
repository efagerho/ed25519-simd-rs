From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Curve25519.group Require Import PrimeField Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.CachedAdd Require Import CachedAddSpec.
From Ed25519Simd.KeyTable Require Rows NativeTable.
From Ed25519Simd.KeyTable Require Import TableRowMeaning.
From Ed25519Simd.KeyTable Require TableRounds.
From Ed25519Simd.KeyTable Require Import CallLayout.
From Ed25519Simd.Decode Require NativeProduct.
Local Open Scope Z_scope.

Definition seed:=NativeTable.seed.
Definition multiple w digit v:=cache_bounds false v /\ forall j P,(j<8)%nat -> seed w j P ->
 represents_point true (point_values v j) (scale digit P).
Definition cache e s:=buffer_words (mem s) (CallLayout.stage e).
Definition staged w e s:=forall n,(n<120)%nat -> cache e s n=Rows.staged NativeProduct.kernel w n.
Definition row_value e d sign s w j:=NativeTable.row_value (CallLayout.table_ptr e) d sign (mem s) w j.
Definition prior_rows e d s w:=NativeTable.prior_rows (CallLayout.table_ptr e) d (mem s) w.

Lemma disjoint_rows e d k sign j x : 0<=k<d -> d<=8 -> (j<8)%nat ->
 TablePackRows.row e k sign (Z.of_nat j)<=x<TablePackRows.row e k sign (Z.of_nat j)+160 -> ~TablePackRows.area e d x.
Proof.
 intros K D J R [b [lane [L Hit]]];unfold TablePackRows.row,TableMultiple.pos,TableMultiple.neg in *.
 destruct (Z.lt_trichotomy lane (Z.of_nat j)) as [Sm|[Eq|Big]];destruct b,sign;lia.
Qed.
Lemma point_outside e d x : placement e -> 1<=d<=8 -> span (CallLayout.point_ptr e) 1280 x -> ~TablePackRows.area e d x.
Proof. intros P D X Hit;apply (TablePackRows.in_table _ _ _ D) in Hit;pose proof(buffers_disjoint _ P);unfold span,disjoint in *;lia. Qed.
Lemma point_stack e x : placement e -> span (CallLayout.point_ptr e) 1280 x ->
 ~(CallLayout.stage e-1360<=x<CallLayout.stage e+960).
Proof. intros P X;pose proof(CallLayout.depth e P);pose proof(CallLayout.point_stack _ P);unfold span,disjoint in *;lia. Qed.

Lemma words_preserved a n k s t : (k<n)%nat -> preserved (span a (8*Z.of_nat n)) (mem s) (mem t) ->
 buffer_words (mem t) a k=buffer_words (mem s) a k.
Proof. intros K Keep;apply preserved_read with (outside:=span a (8*Z.of_nat n));[exact Keep|].
 intros i I;change (0<=i<8) in I;unfold span;lia. Qed.
Lemma keep_row e d sign s t w j : (forall i,(i<20)%nat -> stored e d sign t j i=stored e d sign s j i) ->
 row_value e d sign s w j -> row_value e d sign t w j.
Proof.
 intros E [B R];change (forall i,(i<20)%nat -> NativeTable.stored (CallLayout.table_ptr e) d sign (mem t) j i=
   NativeTable.stored (CallLayout.table_ptr e) d sign (mem s) j i) in E.
 split;[intros i N;rewrite E by exact N;apply B,N|].
 intros P Valid;rewrite (NativeTable.cache_ext _ _ E);apply R,Valid.
Qed.
Lemma keep_multiple w d s t : (forall n,(n<160)%nat -> t n=s n) -> multiple w d s -> multiple w d t.
Proof.
 intros E [B R];split.
 - intros i j N J;unfold cell;rewrite E by (change (i<20)%nat in N;lia);apply B;assumption.
 - intros j P J Input;rewrite (point_values_ext _ _ _ E J);apply R;assumption.
Qed.

Lemma advance w d before after : cache_bounds false w -> multiple w d before ->
 CachedAddSpec.cached_add_spec true true before (Rows.staged NativeProduct.kernel w) after ->
 multiple w (d+1) after.
Proof.
 intros W [B Rep] [_ Spec];specialize(Spec (conj (split_cached_point _ B) (Rows.stage_bounds _ _ kernels W))).
 split;[apply strict_split;intros c j C J;apply Spec;assumption|].
 intros j P J [Input Z1];replace (d+1) with (Z.succ d) by lia;rewrite scale_succ,plus_comm.
 eapply represents_equivalent;[intros c C;rewrite coord_value by exact C;apply Spec;assumption|].
 apply add_represents;[apply Rep;[exact J|split;assumption]|apply Rows.staged_rep;auto using kernels].
Qed.

Theorem next (root:cpu) bias e d p q w : placement e -> 1<=d<8 -> cache_bounds false w ->
 TableRounds.step root bias e d p q ->
 multiple w d (point e (machine p)) -> staged w e (machine p) -> prior_rows e d (machine p) w ->
 multiple w (d+1) (point e (machine q)) /\ staged w e (machine q) /\ prior_rows e (d+1) (machine q) w.
Proof.
 intros P D W Step Prev Stage Older;destruct(TableRounds.checkpoints _ _ _ _ _ _ Step) as [a [b [c [A [B [C Pack]]]]]].
 assert (Outside:=TableRounds.outside _ _ _ _ _ _ Step).
 assert (Push:preserved (fun x=>~span (CallLayout.stage e-8) 8 x) (mem(machine p)) (mem(machine a))).
 { intros x X;rewrite (TableAddCall.pushed _ _ _ _ _ A);apply write_outside,X. }
 assert (Added:multiple w (d+1) (point e (machine c))).
 { apply (advance _ _ _ _ W Prev).
   eapply (CachedAddSpec.spec_ext true true);[| | |exact (TableAdd.point_result _ _ _ _ _ B)].
   - intros k K;symmetry;apply (words_preserved _ 160 _ _ _ K);intros x X;apply Push;
       pose proof(point_stack e x P X);unfold span in *;lia.
   - intros k K;rewrite <- (Stage k K);symmetry;apply (words_preserved _ 120 _ _ _ K).
     intros x X;apply Push;change (span (CallLayout.stage e) 960 x) in X;unfold span in *;lia.
   - intros k K;unfold point,buffer_words;now rewrite (TableMultiple.flat _ _ _ _ _ _ C). }
 assert (Point:forall k,(k<160)%nat ->point e (machine q) k=point e (machine c) k).
 { intros k K;apply (words_preserved _ 160 _ _ _ K);intros x X;apply (TablePass.outside _ _ _ _ _ _ Pack).
   split;[intros H;apply (point_stack e x P X);lia|split;[apply point_outside;[exact P|lia|exact X]|lia]]. }
 split;[exact (keep_multiple _ _ _ _ Point Added)|split].
 - intros k K;rewrite <-(Stage k K);apply (words_preserved _ 120 _ _ _ K).
   intros x X;change (span (CallLayout.stage e) 960 x) in X;apply Outside.
   split;[unfold TableRounds.private;pose proof(point_stack e x P);unfold span in *;lia|eapply TablePass.stack_outside;eauto;lia].
 - intros digit sign j Range J;destruct (Z.eq_dec digit (d+1)) as [->|Lower].
   + destruct Added as [Bounds Rep];destruct(TableRowMeaning.represents _ _ sign _ _ j (TablePass.rows _ _ _ _ _ _ Pack) Bounds J) as [Limbs Cache].
     split;[exact Limbs|intros G Good;apply Cache,Rep;assumption].
   + eapply keep_row;[|apply Older;[lia|exact J]];intros i I;unfold stored;apply preserved_read with
       (outside:=fun x=>~TableRounds.private e x /\ ~TablePackRows.area e (d+1) x);[exact Outside|].
     intros k K;change (0<=k<8) in K;set (a0:=TablePackRows.row e digit sign (Z.of_nat j)).
     assert (R:a0<=a0+8*Z.of_nat i+k<a0+160) by lia.
     split;[|apply (disjoint_rows e (d+1) digit sign j _ ltac:(lia) ltac:(lia) J R)].
     assert (InTable:span (CallLayout.table_ptr e) 21760 (a0+8*Z.of_nat i+k)).
     { apply (TablePackRows.in_table e digit _ ltac:(lia));exists sign,(Z.of_nat j);split;[lia|exact R]. }
     pose proof(CallLayout.depth e P);pose proof(table_stack _ P);pose proof(buffers_disjoint _ P).
     all: unfold TableRounds.private,disjoint,span in *;lia.
Qed.

Theorem retained (root:cpu) bias e n d p q w: placement e -> cache_bounds false w -> 1<=d -> d+Z.of_nat n<=8 ->
 TableRounds.iterations root bias e n d p q ->
 multiple w d (point e (machine p)) -> staged w e (machine p) -> prior_rows e d (machine p) w ->
 prior_rows e (d+Z.of_nat n) (machine q) w.
Proof.
 intros P W L H R;induction R as [d p|n d p a q Step Path IH];intros B Init Rows.
 - now rewrite Z.add_0_r.
 - destruct(next root bias e d p a w P ltac:(lia) W Step B Init Rows) as [A [K More]].
   replace (d+Z.of_nat(S n)) with ((d+1)+Z.of_nat n) by lia;apply IH;try assumption;lia.
Qed.
