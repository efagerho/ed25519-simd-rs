From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import execution.Blocks isa.Instructions execution.WordBounds.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.CachedAdd Require Import Program CachedAddABI Kernels Lane Control Bounds.
Import ListNotations. Open Scope Z_scope.
Definition R j full affine n s start := rfield(prefix_state j full affine n s)start.
Definition M j full affine n s region coord := field(prefix_state j full affine n s)region coord.
Ltac five := intros i I;do 5(destruct i as[|i];[reflexivity|]);lia.
Lemma ab_x j full affine s : forall i,(i<5)%nat ->(M j full affine 4 s point 0)i=(field s point 0)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 0 4 s ltac:(destruct full || idtac;destruct affine || idtac;lia));destruct full;destruct affine;five. Qed.
Lemma ab_y j full affine s : forall i,(i<5)%nat ->(M j full affine 4 s point 5)i=(field s point 5)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 0 4 s ltac:(destruct full || idtac;destruct affine || idtac;lia));destruct full;destruct affine;five. Qed.
Lemma ab_right0 j full affine s : forall i,(i<5)%nat ->(M j full affine 5 s cached 0)i=(field s cached 0)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 0 5 s ltac:(destruct full || idtac;destruct affine || idtac;lia));destruct full;destruct affine;five. Qed.
Lemma ab_right5 j full affine s : forall i,(i<5)%nat ->(M j full affine 5 s cached 5)i=(field s cached 5)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 0 5 s ltac:(destruct full || idtac;destruct affine || idtac;lia));destruct full;destruct affine;five. Qed.
Lemma cd_t j full affine s : forall i,(i<5)%nat ->(R j full affine (if affine then 17 else 18) s 0)i=(field s point 15)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 0 (if affine then 17 else 18) s ltac:(destruct full || idtac;destruct affine || idtac;lia));destruct full;destruct affine;five. Qed.
Lemma cd_z j full s : forall i,(i<5)%nat ->(R j full false 18 s 5)i=(field s point 10)i.
Proof. unfold R,M;rewrite(prefix_segment j full false 0 18 s ltac:(destruct full || idtac;destruct affine || idtac;lia));destruct full;five. Qed.
Lemma cd_right10 j full affine s : forall i,(i<5)%nat ->(M j full affine (if affine then 17 else 18) s cached 10)i=(field s cached 10)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 0 (if affine then 17 else 18) s ltac:(destruct full || idtac;destruct affine || idtac;lia));destruct full;destruct affine;five. Qed.
Lemma cd_right15 j full s : forall i,(i<5)%nat ->(M j full false 18 s cached 15)i=(field s cached 15)i.
Proof. unfold R,M;rewrite(prefix_segment j full false 0 18 s ltac:(destruct full || idtac;destruct affine || idtac;lia));destruct full;five. Qed.
Lemma cd_affine_c j full s : forall i,(i<5)%nat ->(R j full true 19 s 5)i=(R j full true 18 s 0)i.
Proof. unfold R,M;rewrite(prefix_segment j full true 18 19 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full true 18 s);intro snapshot;destruct full;five. Qed.
Lemma eh_a j full affine s : forall i,(i<5)%nat ->(M j full affine 30 s scratch 0)i=(R j full affine 6 s 5)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 6 30 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full affine 6 s);intro snapshot;destruct full;destruct affine;five. Qed.
Lemma eh_b j full affine s : forall i,(i<5)%nat ->(M j full affine 30 s scratch 5)i=(R j full affine 6 s 0)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 6 30 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full affine 6 s);intro snapshot;destruct full;destruct affine;five. Qed.
Lemma xz_e j full affine s : forall i,(i<5)%nat ->(R j full affine 42 s 0)i=(R j full affine 31 s 0)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 31 42 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full affine 31 s);intro snapshot;destruct full;destruct affine;five. Qed.
Lemma xz_g j full affine s : forall i,(i<5)%nat ->(R j full affine 42 s 5)i=(R j full affine 20 s 10)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 20 42 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full affine 20 s);intro snapshot;destruct full;destruct affine;five. Qed.
Lemma xz_f j full affine s : forall i,(i<5)%nat ->(M j full affine 42 s scratch 10)i=(R j full affine 20 s 0)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 20 42 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full affine 20 s);intro snapshot;destruct full;destruct affine;five. Qed.
Lemma yt_g j full affine s : forall i,(i<5)%nat ->(R j full affine (if full then 55 else 54) s 0)i=(R j full affine 20 s 10)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 20 (if full then 55 else 54) s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full affine 20 s);intro snapshot;destruct full;destruct affine;five. Qed.
Lemma yt_e j affine s : forall i,(i<5)%nat ->(R j true affine 55 s 5)i=(R j true affine 31 s 0)i.
Proof. unfold R,M;rewrite(prefix_segment j true affine 31 55 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j true affine 31 s);intro snapshot;destruct affine;five. Qed.
Lemma yt_h j full affine s : forall i,(i<5)%nat ->(M j full affine (if full then 55 else 54) s scratch 5)i=(R j full affine 31 s 10)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 31 (if full then 55 else 54) s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full affine 31 s);intro snapshot;destruct full;destruct affine;five. Qed.
Lemma out_x j full affine s : forall i,(i<5)%nat ->(M j full affine 67 s point 0)i=(R j full affine 43 s 0)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 43 67 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full affine 43 s);intro snapshot;destruct full;destruct affine;five. Qed.
Lemma out_y j full affine s : forall i,(i<5)%nat ->(M j full affine 67 s point 5)i=(R j full affine 56 s 0)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 56 67 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full affine 56 s);intro snapshot;destruct full;destruct affine;five. Qed.
Lemma out_z j full affine s : forall i,(i<5)%nat ->(M j full affine 67 s point 10)i=(R j full affine 43 s 5)i.
Proof. unfold R,M;rewrite(prefix_segment j full affine 43 67 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j full affine 43 s);intro snapshot;destruct full;destruct affine;five. Qed.
Lemma out_t j affine s : forall i,(i<5)%nat ->(M j true affine 67 s point 15)i=(R j true affine 56 s 5)i.
Proof. unfold R,M;rewrite(prefix_segment j true affine 56 67 s ltac:(destruct full || idtac;destruct affine || idtac;lia));generalize(prefix_state j true affine 56 s);intro snapshot;destruct affine;five. Qed.
Lemma out_zero j affine s : forall i,(i<5)%nat -> M j false affine 67 s point 15 i=0.
Proof.
 intros i I.
 assert (Stored : M j false affine 67 s point 15 i=R j false affine 56 s 5 i).
 { unfold R,M; rewrite (prefix_segment j false affine 56 67 s ltac:(lia)).
   generalize (prefix_state j false affine 56 s); intro snapshot; destruct affine;
   do 5 (destruct i as [|i]; [reflexivity|]); lia. }
 rewrite Stored. unfold R.
 rewrite (prefix_segment j false affine 55 56 s ltac:(lia)).
 generalize (prefix_state j false affine 55 s); intro snapshot.
 destruct affine; change (run (lane_load snapshot []) (fragment_code add_cached_program 9)
   (registers snapshot) (5+i)%nat=0);
 rewrite <- (firstn_skipn 15 (fragment_code add_cached_program 9)), run_app;
 generalize (run (lane_load snapshot []) (firstn 15 (fragment_code add_cached_program 9))
   (registers snapshot)); intro regs;
 do 5 (destruct i as [|i]; [apply Z.lxor_nilpotent|]); lia.
Qed.
