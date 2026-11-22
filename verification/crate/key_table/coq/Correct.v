From Coq Require Import List ZArith Bool Lia.
From Machine Require Import memory.ByteMemory memory.FlatMemory execution.WordBounds.
From Curve25519.group Require Import PrimeField Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.CachedAdd Require Audit.
From Ed25519Simd.Decode Require Import Kernels Image Decode.
From Ed25519Simd.KeyTable Require Import Frame Image Rows Advance Execution Audit.
Import ListNotations. Local Open Scope Z_scope.

Lemma points_correct incoming k w n : (forall t,data_words(incoming t)) -> kernels_ok k -> cache_bounds false w ->
 cache_bounds false (points incoming k w n) /\ forall j P,(j<8)%nat ->
 represents_point true (point_values w j) P -> value (coord w j 2)=1%fp ->
 represents_point true (point_values (points incoming k w n) j) (scale (1+Z.of_nat n) P).
Proof.
 intros Scratch K W;induction n as [|n [B IH]].
 - cbn [points];split;auto;intros. change (represents_point true (point_values w j) (plus P identity)).
   rewrite plus_comm,plus_identity;assumption.
 - destruct (advance_correct _ _ _ (Scratch n) B (stage_bounds k w K W)) as [Next Add].
   split;[exact Next|]. intros j P J R Z1.
   rewrite Nat2Z.inj_succ. replace (1+Z.succ (Z.of_nat n)) with (Z.succ(1+Z.of_nat n)) by lia.
   rewrite scale_succ,plus_comm. apply Add;auto using staged_rep.
Qed.
Lemma negative_scale z P : negative(scale z P)=scale (-z) P.
Proof.
 apply(cancel_left(scale z P));rewrite plus_negative,<-scale_add.
 replace (z+ -z) with 0 by lia;reflexivity.
Qed.
Lemma identity_rep : represents_cache (scalar_cache false (fun i=>identity_word (Z.of_nat i))) identity.
Proof.
 exists 1%fp;split;[discriminate|].
 change ((1=(1-0)*1) /\ (1=(1+0)*1) /\ (0=(1+1)*d*0*1*1) /\ residue 2=(1+1)*1)%fp.
 rewrite residue_two;repeat split;ring.
Qed.
Definition expected_row incoming k w j d i := resolve incoming k w (expected j d i).
Lemma entry_correct incoming k w j digit : (forall t,data_words(incoming t)) -> kernels_ok k -> cache_bounds false w -> (j<8)%nat ->
 let a:=expected_row incoming k w j digit in
 (forall i,(i<20)%nat -> 0<=a i<2^52) /\
 (forall P,represents_point true (point_values w j) P -> value (coord w j 2)=1%fp ->
 represents_cache (scalar_cache false a) (scale digit P)).
Proof.
 intros Scratch K W J a;unfold a,expected_row,expected;destruct (Z.eqb_spec digit 0) as [->|D].
 - split;[intros i I;do 20 (destruct i as [|i];[vm_compute;easy|]);lia|intros;exact identity_rep].
 - set (n:=Nat.pred(Z.to_nat(Z.abs digit))).
   change (fun i=>resolve incoming k w (n, Pack.signed_word (0<?digit) i j)) with
     (row k (points incoming k w n) (0<?digit) j).
   destruct(points_correct incoming k w n Scratch K W) as [B R];split;[intros;apply row_bounds;auto|].
   intros P H Z1. pose proof(row_rep k _ j (0<?digit) _ K B J (R j P J H Z1)) as Rep.
   assert (E:1+Z.of_nat n=Z.abs digit) by (unfold n;lia).
   rewrite E in Rep;destruct (Z.ltb_spec 0 digit);[rewrite Z.abs_eq in Rep by lia;exact Rep|].
   rewrite negative_scale,Z.abs_neq in Rep by lia;now rewrite Z.opp_involutive in Rep.
Qed.

Lemma result_correct incoming k count w base : (forall t,data_words(incoming t)) -> kernels_ok k -> cache_bounds false w ->
 count=1%nat \/ count=8%nat -> signed_table_result incoming k count w base.
Proof.
 intros Scratch K W N;destruct(returns _ N) as [ws [R [Span Complete]]].
 exists ws;split;[exact R|];split.
 - intros off words H;apply forallb_forall with (x:=(off,words)) in Span;auto.
   apply andb_true_iff in Span as [A B];split;apply Z.leb_le;assumption.
 - split.
   { intros a Bound;unfold output_byte;rewrite (outside count _ _ Span);[reflexivity|].
     destruct Bound as [B|B];[left;apply Z.div_lt_upper_bound;lia|right;apply Z.div_le_lower_bound;lia]. }
   intros j digit J D. assert (J8:(j<8)%nat) by (destruct N;lia).
   destruct(entry_correct incoming k w j digit Scratch K W J8) as [B Rep].
   assert (Byte:forall i b,(i<20)%nat->0<=b<8 ->
     output_byte incoming k w ws base (slot base j digit i+b)=Some (word_byte(expected_row incoming k w j digit i) b)).
   { intros i b I Br;unfold output_byte.
     replace (slot base j digit i+b-base) with (b+address j digit i*8) by (unfold slot,address;ring).
     rewrite Z.div_add,Z.mod_add,Z.div_small,Z.mod_small by lia.
     rewrite Z.add_0_l,Complete by assumption;reflexivity. }
   split;[intros;eexists;apply Byte;assumption|]. intros prior entry.
   assert (E:forall i,(i<20)%nat->entry i=expected_row incoming k w j digit i).
   { intros i I;apply read_word_exact;[specialize(B i I);unfold word64;lia|].
     intros b H;unfold table_view;now rewrite Byte. }
   split;[intros;rewrite E by assumption;apply B;assumption|].
   intros P H Z1;replace (scalar_cache false entry) with (scalar_cache false (expected_row incoming k w j digit)).
   + apply Rep;assumption.
   + unfold scalar_cache,cache_from_fields;f_equal;try match goal with |- Some _=Some _ => f_equal end;apply Radix51.limbs_ext;intros;symmetry;apply E;lia.
Qed.
