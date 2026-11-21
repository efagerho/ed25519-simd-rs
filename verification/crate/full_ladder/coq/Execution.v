From Coq Require Import List ZArith Lia.
From ProofArithmetic Require Import Radix.
From Machine Require Import execution.LinkedCalls memory.ByteMemory.
From Curve25519 Require Import Radix51 Edwards group.Affine group.Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.LadderStep Require Import Schedule.
From Ed25519Simd.CachedAdd Require CachedAddSpec.
From Ed25519Simd.FullLadder Require Import Program Operands ScalarAction Seed.
Import ListNotations. Local Open Scope Z_scope.

Definition buffer := nat->Z.
Definition zero_t (w:buffer) := forall i j,(i<5)%nat -> (j<8)%nat -> cell w (15+i)%nat j=0.
Definition ladder_post full (w t out:buffer) := strict out /\
 has_value out (fun j=>ladder_formula full (point_values w j)
  (cache_values false (slice t 0) j) (cache_values true (slice t 20) j)
  (cache_values false (slice t 35) j)) /\ (full=false -> zero_t out).

(* A call can return any limb representation allowed by the linked callee.
   The seed executes the actual qword instructions with arbitrary incoming
   temporaries. Staging executes its linked register/load and transpose blocks. *)
Definition seed_buffer (t:buffer) (initial:nat->Seed.lane) k :=
 let j:=(k mod 8)%nat in Seed.out (Seed.execute (fun i=>cell t i j) (initial j)) (k/8)%nat.
Definition buffers := (buffer*buffer)%type. (* accumulator and staged round *)
Inductive action pc pad s : event -> buffers -> buffers -> Prop :=
| stage n w t : action pc pad s (Stage n) (w,t) (w,staged pc pad s n)
| seed w t initial : action pc pad s SeedXYZ (w,t) (seed_buffer t initial,t)
| double w t v : Double4Spec.double4_spec w v -> action pc pad s DoubleFour (w,t) (v,t)
| cached f a off w t v : CachedAddSpec.cached_add_spec f a w (slice t off) v ->
 action pc pad s (Cached f a off) (w,t) (v,t)
| ladder f w t v : ladder_post f w t v -> action pc pad s (Ladder f) (w,t) (v,t).
Fixpoint executes pc pad s ops b z : Prop := match ops with
 | []=>b=z | e::rest=>exists m,action pc pad s e b m /\ executes pc pad s rest m z end.
Definition seeded_xyz (w:buffer) (q:nat->point) :=
 forall j,(j<8)%nat -> represents_xyz (point_values w j) (q j).
Definition extended full (w:buffer) (q:nat->point) :=
 forall j,(j<8)%nat -> represents_point full (point_values w j) (q j).
Lemma self_value w : has_value w (point_values w).
Proof. intros j J c C;reflexivity. Qed.
Lemma seed_cell t r i j : (j<8)%nat -> cell (seed_buffer t r) i j =
 Seed.out (Seed.execute (fun k=>cell t k j) (r j)) i.
Proof.
 intro J;unfold cell,seed_buffer.
 replace ((i*8+j)/8)%nat with i by (apply Nat.div_unique with (r:=j);lia).
 replace ((i*8+j) mod 8)%nat with j by (apply Nat.mod_unique with (q:=i);lia).
 reflexivity.
Qed.
Lemma seeded t r q : cache_bounds false (slice t 0) ->
 (forall j,(j<8)%nat -> represents_cache (cache_values false (slice t 0) j) (q j)) ->
 loose_xyz (seed_buffer t r) /\ seeded_xyz (seed_buffer t r) q.
Proof.
 intros B Q;split.
 - intros c j C J;eapply loose_ext;[|apply (seed_bound (fun k=>cell t k j) c);unfold bounded;intros;apply B;assumption].
   intros i I;symmetry;rewrite seed_cell by exact J;apply routed;assumption.
 - intros j J;replace (point_values (seed_buffer t r) j) with (output_point (fun k=>cell t k j) (r j)).
   + apply seed_represents;[unfold bounded;intros;apply B;assumption|apply Q;assumption].
   + unfold point_values,point_from_fields,word_coordinate,field_at,output_point;f_equal;apply limbs_ext;intros;symmetry;apply seed_cell;assumption.
Qed.
Lemma first_double w v q : Double4Spec.double4_spec w v -> loose_xyz w -> seeded_xyz w q ->
 strict v /\ extended true v (fun j=>multiple 16 (q j)).
Proof.
 intros D W Q;destruct(double_result _ _ _ (self_value w) W D) as [B V].
 split;[exact B|intros j J;eapply represents_equivalent;[exact(V j J)|apply double_four_represents,Q,J]].
Qed.
Lemma point_add f a w t v q u :
 CachedAddSpec.cached_add_spec f a w t v -> strict w -> cache_bounds a t ->
 extended true w q -> (forall j,(j<8)%nat -> represents_cache (cache_values a t j) (u j)) ->
 strict v /\ extended f v (fun j=>plus (q j) (u j)).
Proof.
 intros Add W B Q U;destruct(add_result f a _ _ _ _ (self_value w) W B Add) as [R V];split;[exact R|].
 intros j J;eapply represents_equivalent;[exact(V j J)|apply add_represents;auto].
Qed.

Fixpoint remaining_digits (d:nat->Z) n := match n with
 | O=>0 | S m=>let i:=(31-m)%nat in d (2*i)%nat+16*(d (S (2*i))+16*remaining_digits d m) end.
Lemma digits_number d n : (n<=32)%nat ->
 remaining_digits d n=number 16 (map d (seq (2*(32-n)) (2*n))).
Proof.
 induction n as [|n IH];intro N;[reflexivity|].
 replace (2*S n)%nat with (S(S(2*n))) by lia.
 cbn [seq map number remaining_digits];rewrite IH by lia.
 replace (32-S n)%nat with (31-n)%nat by lia.
 replace (S (S (2*(31-n)))) with (2*(32-n))%nat by lia;reflexivity.
Qed.
Definition accumulated s B A n j := combination (remaining_digits (digits s 1 j) n)
 (remaining_digits (digits s 8 j) n) B (A j).
Definition tail count full := flat_map (fun n=>[Stage n;Ladder (full && Nat.eqb n 0)]) (rev(seq 0 count)).
Lemma tail_cons n full : tail (S n) full=[Stage n;Ladder (full && Nat.eqb n 0)]++tail n full.
Proof. unfold tail;rewrite seq_S,rev_app_distr,flat_map_app;cbn [rev app Nat.add];reflexivity. Qed.
Section Correct.
Variables (pc pad:Z) (s:cpu) (B:point) (A:nat->point).
Hypotheses (Inputs:valid_inputs pc pad s) (Tables:valid_tables s B A).
Local Notation operand := (operand_correct pc pad s B A).
Lemma rounds count full w t out cache : (count<=31)%nat ->
 strict w -> seeded_xyz w (accumulated s B A (32-count)) ->
 executes pc pad s (tail count full) (w,t) (out,cache) ->
 (0<count)%nat -> strict out /\ extended full out (accumulated s B A 32) /\ (full=false -> zero_t out).
Proof.
 revert w t;induction count as [|n IH];intros w t N W Q Run Nonempty;[lia|].
 rewrite tail_cons in Run;destruct Run as [a [StageCall [b [Step Rest]]]].
 inversion StageCall;subst;inversion Step;subst.
 match goal with H:ladder_post _ _ _ _ |- _=>destruct H as [Strict [Values T]] end.
 assert (N32:(n<32)%nat) by lia.
 pose proof(operand n S.Odd Inputs Tables N32) as [_ Odd].
 pose proof(operand n S.Base Inputs Tables N32) as [_ Base].
 pose proof(operand n S.Even Inputs Tables N32) as [_ Even].
 assert (Result:extended (full && Nat.eqb n 0) v (accumulated s B A (32-n))).
 { intros j J;eapply represents_equivalent;[apply Values;exact J|].
   pose proof(ladder_represents (full && Nat.eqb n 0) _ _ _ _ _ _ _ _ (Q j J) (Odd j J) (Base j J) (Even j J)) as R.
   unfold operand_point,weight,affine in R;cbn iota in R.
   unfold accumulated in *;rewrite radix_step in R.
   replace (32-n)%nat with (S (32-S n)) by lia;cbn [remaining_digits].
   replace (31-(32-S n))%nat with n by lia;exact R. }
 destruct n as [|n].
 - change ((v,staged pc pad s 0)=(out,cache)) in Rest;injection Rest as E _;subst out.
   rewrite Bool.andb_true_r in Result,T;auto.
 - eapply IH;[lia|exact Strict| |exact Rest|lia].
   intros j J;exact(proj1(Result j J)).
Qed.
Theorem schedule_correct full w t out cache :
 executes pc pad s (schedule full) (w,t) (out,cache) ->
 strict out /\ extended full out (fun j=>combination (number 16 (digit_list s 1 j))
     (number 16 (digit_list s 8 j)) B (A j)) /\ (full=false -> zero_t out).
Proof.
 intros [b0 [S0 [b1 [Seed [b2 [D [b3 [Base [b4 [Even Rest]]]]]]]]]].
 inversion S0;subst;inversion Seed;subst;inversion D;subst;inversion Base;subst;inversion Even;subst.
 pose proof (operand 31%nat S.Odd Inputs Tables ltac:(lia)) as [OB OR].
 pose proof (operand 31%nat S.Base Inputs Tables ltac:(lia)) as [BB BR].
 pose proof (operand 31%nat S.Even Inputs Tables ltac:(lia)) as [EB ER].
 destruct(seeded _ initial _ OB OR) as [SeedB SeedQ].
 match goal with H:Double4Spec.double4_spec _ _ |- _=>destruct(first_double _ _ _ H SeedB SeedQ) as [DB DQ] end.
 match goal with H:CachedAddSpec.cached_add_spec true true _ _ _ |- _=>
 destruct(point_add _ _ _ _ _ _ _ H DB BB DQ BR) as [AB AQ] end.
 match goal with H:CachedAddSpec.cached_add_spec false false _ _ _ |- _=>
 destruct(point_add _ _ _ _ _ _ _ H AB EB AQ ER) as [FB FQ] end.
 eassert (R:strict out /\ extended full out (accumulated s B A 32) /\ (full=false -> zero_t out)).
 { eapply (rounds 31 full);[lia|exact FB| |exact Rest|lia].
   intros j J;specialize(FQ j J);apply proj1 in FQ.
   unfold operand_point,affine,weight in FQ;cbn iota in FQ.
   rewrite top_pair in FQ.
   unfold accumulated;change (32-31)%nat with 1%nat;cbn [remaining_digits].
   rewrite !Z.mul_0_r,!Z.add_0_r;exact FQ. }
 destruct R as [Bounds [R T]];split;[exact Bounds|split;[|exact T]].
 intros j J;specialize(R j J);unfold accumulated in R;rewrite !digits_number in R by lia;exact R.
Qed.
End Correct.
