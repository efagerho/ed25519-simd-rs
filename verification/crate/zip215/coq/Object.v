From Coq Require Import List Bool ZArith Lia.
From Machine Require Import memory.ByteMemory.
From Curve25519.group Require Import PrimeField Affine Representation.
From Ed25519Simd.Dalek Require Import Batch.
From Ed25519Simd.PostHash Require Import Staging Product.
From Ed25519Simd.Zip215 Require Import Caller Equation Binding Calls Schedule Audit.
Import ListNotations. Local Open Scope Z_scope.

Lemma image_ok : linked_image.
Proof.
 split.
 - intros s H; destruct s; try (simpl in H;intuition discriminate); vm_compute;split;reflexivity.
 - vm_compute;split;reflexivity.
Qed.

Lemma direct_ok : direct_correct.
Proof.
 intros q r Q raw valid meta len out pad init P M Bound Inputs.
 destruct(Torsion.Audit.run_correct _ Torsion.Object.assembled_torsion_correct _ _ _ init P Bound)
 as [m [Run [_ Bits]]]. set (v:=fun j=>Z.testbit (Z.land m valid)(Z.of_nat j)).
 exists m,(place (active meta) 0 meta v out);split;[exact Run|]. split.
 - apply scatter_lanes;auto.
 - exists v;split;[|reflexivity]. intros j J;destruct(Inputs j J) as [Qrep R].
   unfold v,input_R in *. rewrite Z.land_spec. destruct (Z.testbit valid (Z.of_nat j)).
   + destruct R as [Pnt [Enc [Rep [Affine Unique]]]]. rewrite Bool.andb_true_r.
     rewrite (proj2(Bits j J) (Q j) Pnt Qrep Rep Affine). split.
     * intro H;exists Pnt;auto.
     * intros [A [E H]];now rewrite (Unique A E) in H.
   + rewrite Bool.andb_false_r;split;[discriminate|]. intros [A [E _]];contradiction (R A).
Qed.

Lemma nth_pattern {T:Type} (f:nat->T) n i d : (i<n)%nat -> nth i (map f (seq 0 n)) d=f i.
Proof.
 intro I. rewrite (nth_indep _ _ (f O)) by (rewrite map_length,seq_length;assumption).
 rewrite map_nth,seq_nth by lia. reflexivity.
Qed.

Lemma source_ok n pattern fast slow i s verdict :
 length pattern=n -> origin n (fun i=>nth i pattern false) i s=true ->
 (forall j,(j<n)%nat -> nth j pattern false=true ->
   forall k,(k<8)%nat -> Z.testbit(octet fast j)(Z.of_nat k)=verdict j k) ->
 (forall start paired,(start+(if paired:bool then 2 else 1)<=n)%nat ->
   exists m,slow start paired=Some m /\ forall high k,(k<8)%nat -> (high=true -> paired=true) ->
   Z.testbit m (Z.of_nat(if high then (8+k)%nat else k))=verdict (if high then S start else start) k) ->
 (i<n)%nat -> exists m,resolve_byte fast slow s=Some m /\
 forall k,(k<8)%nat -> Z.testbit m (Z.of_nat k)=verdict i k.
Proof.
 intros N O' F S' I;destruct s as [j|j paired high];cbn [origin] in O'.
 - apply andb_true_iff in O' as [E G];apply Nat.eqb_eq in E;subst j;eexists;split;[reflexivity|auto].
 - apply andb_true_iff in O' as [A J]. apply andb_true_iff in A as [E H].
   apply Nat.eqb_eq in E. apply Nat.leb_le in J. destruct(S' j paired J) as [m [R B]].
   unfold resolve_byte;rewrite R;eexists;split;[reflexivity|]. intros k K.
   cbn [option_map]. rewrite octet_bit by exact K.
   destruct high;cbn in E,H;subst i;rewrite ?Nat.add_0_r,?Nat.add_1_r.
   + replace (8*Z.of_nat 1+Z.of_nat k) with (Z.of_nat(8+k)) by lia.
     apply (B true k);auto.
   + change (Z.testbit m (Z.of_nat k)=verdict j k). apply (B false k);auto;discriminate.
Qed.

Lemma score_ok todo n exact slow meta len verdict out :
 (forall i,(i<n)%nat -> positions(meta i) len) ->
 (forall i s,In (i,s) todo -> (i<n)%nat /\ exists m,resolve_byte exact slow s=Some m /\
    forall j,(j<8)%nat -> Z.testbit m (Z.of_nat j)=verdict i j) ->
 score todo exact slow meta len out=Some(fold_left (fun o i=>
  place (active(meta i)) 0 (meta i) (verdict i) o) (map fst todo) out).
Proof.
 intros M. revert out;induction todo as [|[i s] rest IH];intros out H;[reflexivity|].
 destruct(H i s (or_introl eq_refl)) as [I [m [E V]]].
 cbn [score map fst fold_left]. rewrite E, (scatter_lanes _ _ _ _ (verdict i) (M i I)).
 - apply IH;intros;apply H;now right.
 - intros j J;apply V;destruct(M i I);lia.
Qed.

Lemma deferred_ok : exists fast decode,
 Dalek.Audit.shared_image fast Decode.DecoderBytes.address Decode.DecoderBytes.symbol_bytes
 Decode.HelperBytes.address Decode.HelperBytes.symbol_bytes /\
 Decode.Image.kernel_image decode Decode.DecoderBytes.address Decode.DecoderBytes.symbol_bytes
 Decode.HelperBytes.address Decode.HelperBytes.symbol_bytes /\ flush_correct fast decode.
Proof.
 destruct fast_masks as [fast [FI F]]. destruct slow_masks as [decode [D DI]].
 exists fast,decode;split;[exact FI|split;[exact DI|]].
 intros flat pts enc n Q pad ix ic matches meta len out N B L P Input.
 assert (C:forall i,(i<n)%nat -> candidate_chunk(point_words flat pts i)(Q i)) by (intros;apply Input;auto).
 set (slow:=fun start paired=>checked_mask decode flat pts enc start paired pad ic).
 set (v:=fun i j=>match slow i false with Some m=>Z.testbit m (Z.of_nat j) | None=>false end).
 assert (V:forall i j,(i<n)%nat -> (j<8)%nat -> (v i j=true <-> accepts(encoded_at flat enc i j)(Q i j))).
 { intros i j I J;destruct(D flat pts enc Q n i false pad ic B P ltac:(change (i+1<=n)%nat;lia) C) as [m [E H]].
   unfold v,slow;rewrite E;exact (proj2(H false j J ltac:(discriminate))). }
 exists (expected n meta v out);split;[|exists v;auto].
 unfold execute. set (ps:=map matches (seq 0 n)).
 assert (PL:length ps=n) by (unfold ps;rewrite map_length,seq_length;reflexivity).
 destruct(probe_total ps ltac:(lia)) as [use_exact Pr]. rewrite PL in Pr;rewrite Pr.
 destruct(F flat pts enc Q n pad ix N L B P C) as [fm [FR FB]].
 set (m:=if use_exact then fm else 0).
 assert (E:(if use_exact then exact_run fast flat pts enc pad ix n else Some 0)=Some m)
 by (unfold m;destruct use_exact;auto). rewrite E.
 set (pat:=map (fun i=>octet m i=?255) (seq 0 n)).
 assert (Len:length pat=n) by (unfold pat;rewrite map_length,seq_length;reflexivity).
 pose proof(all_checked pat ltac:(lia)) as Path;unfold checked in Path.
 destruct(run pat) as [todo|] eqn:Run;[|discriminate]. apply andb_true_iff in Path as [Order Origins].
 destruct(list_eq_dec _ _ _) as [Seq|];[|discriminate]. rewrite Len in Seq,Origins.
 unfold expected;rewrite <-Seq. apply score_ok with (n:=n);[intros;apply Input;auto|].
 intros i s InW. assert (I:(i<n)%nat).
 { assert (In i (map (@fst nat source) todo)) by (apply in_map_iff;exists (i,s);auto).
   rewrite Seq in H;apply in_seq in H;lia. }
 split;[exact I|]. apply forallb_forall with (x:=(i,s)) in Origins;auto.
 apply (source_ok _ _ _ slow _ _ v Len Origins);auto.
 - intros j J H k K. unfold pat in H;rewrite nth_pattern in H by assumption.
   apply Z.eqb_eq in H. assert (On:Z.testbit (octet m j)(Z.of_nat k)=true).
   { rewrite H;change 255 with (Z.ones 8);apply Z.ones_spec_low;lia. }
   rewrite On;symmetry;apply V;auto. destruct use_exact;[apply FB;assumption|].
   change (octet 0 j=255) in H. unfold octet in H;rewrite Z.shiftr_0_l in H;discriminate.
 - intros t paired T;destruct(D flat pts enc Q n t paired pad ic B P T C) as [word [Ew H]].
   exists word;split;[exact Ew|]. intros high k K Side.
   destruct(H high k K Side) as [I' Meaning]. specialize(V _ _ I' K).
   destruct(v _ _), (Z.testbit word _);intuition congruence.
Qed.

Theorem assembled_zip215_correct : zip215_contract.
Proof. constructor;[exact image_ok|exact (conj (candidate_abi_ok true) (conj push_abi_ok (conj eq_refl (conj eq_refl eq_refl))))|exact queue_lifecycle_ok|exact (product_ok true)|exact direct_ok|exact deferred_ok]. Qed.
