From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.KeyTable Require Rows Image NativeTable.
From Ed25519Simd.KeyTable Require Import TableRowMeaning TableRoundMeaning.
From Ed25519Simd.KeyTable Require TableRounds.
From Ed25519Simd.KeyTable Require Import CallLayout.
From Ed25519Simd.KeyTable Require NativeEntry.
From Ed25519Simd.Decode Require NativeProduct.
Local Open Scope Z_scope.

Definition center e s:=NativeTable.center (CallLayout.table_ptr e) (mem s).
Definition contents e w s:=NativeTable.contents (CallLayout.table_ptr e) w (mem s).

Lemma slot_same e d sign j x : (j<8)%nat -> 0<=d<=8 ->
 TablePackRows.row e d sign (Z.of_nat j)<=x<TablePackRows.row e d sign (Z.of_nat j)+160 ->
 span (CallLayout.table_ptr e) 21760 x.
Proof. intros J D;unfold TablePackRows.row,TableMultiple.pos,TableMultiple.neg,TableIdentity.first,span;destruct sign;lia. Qed.
Lemma center_through (root:cpu) bias e n d p q : placement e -> 1<=d -> d+Z.of_nat n<=8 ->
 TableRounds.iterations root bias e n d p q -> center e (machine p) -> center e (machine q).
Proof.
 intros P L H Run;induction Run as [d p|n d p a q Step Tail IH];intros C;[exact C|apply IH;[lia|lia|]].
 intros j i J N;rewrite <-(C j i J N);unfold stored.
 apply preserved_read with (outside:=fun x=>~TableRounds.private e x /\ ~TablePackRows.area e (d+1) x).
 - exact (TableRounds.outside _ _ _ _ _ _ Step).
 - intros k K;change (0<=k<8) in K;set (t:=TablePackRows.row e 0 true (Z.of_nat j)).
   assert (R:t<=t+8*Z.of_nat i+k<t+160) by lia.
   split;[|exact (disjoint_rows _ (d+1) 0 true j _ ltac:(lia) ltac:(lia) J R)].
   change (~TableRounds.private e (t+8*Z.of_nat i+k));pose proof(buffers_disjoint _ P).
   pose proof(slot_same e 0 true j _ J ltac:(lia) R);pose proof(CallLayout.depth e P);pose proof(table_stack _ P).
   all: unfold TableRounds.private,disjoint,span in *;lia.
Qed.
Lemma scale_one P : scale 1 P=P.
Proof. change (plus P identity=P);now rewrite plus_comm,plus_identity. Qed.

Lemma start (root:cpu) bias e p a : placement e -> TablePass.post root bias e 1 p a ->
 center e (machine p) -> let w:=point e (machine p) in center e (machine a) /\ staged w e (machine a) /\
 (cache_bounds false w -> multiple w 1 (point e (machine a)) /\ prior_rows e 1 (machine a) w).
Proof.
 intros P Pass Center w.
 assert (Outside:forall x,span (CallLayout.point_ptr e) 1280 x -> TablePass.preserved_byte e 1 x).
 { intros x X;pose proof (TableRoundMeaning.point_stack e x P X);split;[unfold CallLayout.stage in *;lia|split].
   - apply point_outside;[exact P|lia|exact X].
   - unfold TableStage.buffer,CallLayout.stage in *;lia. }
 split.
 - intros j i J N;rewrite <-(Center j i J N);unfold stored.
   apply preserved_read with (outside:=TablePass.preserved_byte e 1);[exact (TablePass.outside _ _ _ _ _ _ Pass)|].
   intros k K;change (0<=k<8) in K;set (a0:=TablePackRows.row e 0 true (Z.of_nat j)).
   assert (R:a0<=a0+8*Z.of_nat i+k<a0+160) by lia.
   change (TablePass.preserved_byte e 1 (a0+8*Z.of_nat i+k)).
   pose proof (slot_same e 0 true j _ J ltac:(lia) R);pose proof (CallLayout.depth e P);pose proof(table_stack _ P) as Apart.
   split;[|split;[exact(disjoint_rows e 1 0 true j _ ltac:(lia) ltac:(lia) J R)|]].
   all: unfold TableStage.buffer,CallLayout.stage,span,disjoint in *;lia.
 - split.
   + intros n N;set (j:=(n mod 8)%nat);set (i:=(n/8)%nat);assert (J:(j<8)%nat) by (apply Nat.mod_upper_bound;lia).
     assert (Idx:n=(i*8+j)%nat) by (unfold i,j;pose proof(Nat.div_mod n 8 ltac:(lia));lia).
     assert (I:(i<15)%nat) by lia.
     change (cache e (machine a) n=Rows.staged NativeProduct.kernel w n).
     rewrite Idx;change (cell (cache e (machine a)) i j=cell (Rows.staged NativeProduct.kernel w) i j).
     rewrite Rows.stage_cell by assumption.
     unfold cell,cache,buffer_words;rewrite Nat2Z.inj_add,Nat2Z.inj_mul;change (Z.of_nat 8) with 8.
     replace (CallLayout.stage e+8*(Z.of_nat i*8+Z.of_nat j)) with
       (CallLayout.stage e+64*Z.of_nat i+8*Z.of_nat j) by (ring).
     unfold w;rewrite <-(TableRowMeaning.column e (machine p) j i ltac:(lia)).
     exact (TablePass.first_staged _ _ _ _ _ _ Pass eq_refl i j I J).
   + intros B;split.
     * apply (keep_multiple w 1 w);[|split;[exact B|intros j G J [R _];now rewrite scale_one]].
       intros k K;apply (words_preserved _ 160 _ _ _ K);intros x X;apply (TablePass.outside _ _ _ _ _ _ Pass),Outside,X.
     * intros d sign j D J;replace d with 1 by lia;destruct(TableRowMeaning.represents _ _ sign _ _ j (TablePass.rows _ _ _ _ _ _ Pass) B J) as [Bound Rep].
       split;[exact Bound|intros G [R _];rewrite scale_one;apply Rep,R].
Qed.

Theorem checked (root:cpu) bias e p init ks:placement e -> loaded root bias e ->
 (bias+DecoderBytes.address) mod 64=0 -> NativeEntry.entered root (writable e) (CallLayout.base bias) (sp e) (point_ptr e) (table_ptr e) p init ->
 exists q bank,TableRounds.observe bias e init ks=Some(q,bank) /\ TableRounds.at_multiple root bias e 8 q /\
 preserved (CallLayout.keep e) (Frame.saved (sp e) p) (mem(machine q)) /\
 contents e (point e (machine p)) (machine q).
Proof.
 intros P I Al Init;destruct(TableStart.checked _ _ _ _ _ P I Init) as [d [Begin [[c Pos] Point C Parent]]].
 destruct(TablePass.checked root bias e 1 c d ks P I Al ltac:(lia) Pos) as [a [k [First Pass]]].
 assert (A:TableRounds.at_multiple root bias e 1 a) by (constructor;[exact (TablePass.address _ _ _ _ _ _ Pass)|
   exact (TablePass.writes _ _ _ _ _ _ Pass)|exact (TablePass.words _ _ _ _ _ _ Pass)|exact (TablePass.pointers _ _ _ _ _ _ Pass)]).
 destruct(TableRounds.complete root bias e 7 1 a k P I Al ltac:(lia) ltac:(lia) A) as [q [bank [Run [At Steps]]]].
 assert (AtCenter:center e (machine d)).
 { intros j i J N;change (stored e 0 true (machine d) j i=Image.identity_word (Z.of_nat i));unfold stored;rewrite <- (C j (Z.of_nat i) J ltac:(lia));f_equal;
   unfold TablePackRows.row,TableMultiple.pos,TableIdentity.center;ring. }
 destruct(start _ _ _ _ _ P Pass AtCenter) as [Center [Stage Base]].
 exists q,bank;split;[unfold TableRounds.observe;rewrite Begin;cbn [bind];rewrite First;exact Run|split;[exact At|split]].
 - apply (TableRounds.preserves_parent root bias e 7 1 a q _ ltac:(lia) ltac:(lia) Steps);intros x Keep.
   rewrite (TablePass.outside _ _ _ _ _ _ Pass);[apply Parent,Keep|].
   destruct Keep as [Stack [_ T]]. split;[|split].
   + unfold CallLayout.stage,span in *;lia.
   + intro Hit;apply T,(TablePackRows.in_table _ 1 _ ltac:(lia) Hit).
   + unfold TableStage.buffer,CallLayout.stage,span in *;lia.
 - apply (NativeTable.input_ext _ (point e (machine d))).
   + intros n N;exact (words_preserved _ 160 _ _ _ N Point).
   + split;[exact (center_through _ _ _ 7 1 _ _ P ltac:(lia) ltac:(lia) Steps Center)|].
     intros Bd;destruct (Base Bd) as [One Rows].
     exact (retained _ _ _ 7 1 _ _ _ P Bd ltac:(lia) ltac:(lia) Steps One Stage Rows).
Qed.
