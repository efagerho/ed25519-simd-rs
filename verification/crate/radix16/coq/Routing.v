From Curve25519 Require Import SignedRadix16.
From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Packed execution.LinkedCalls memory.FlatMemory isa.Shift.
From Ed25519Simd Require Import Radix16Output.
From Ed25519Simd.Scalar Require Import ScalarSpec.
From Ed25519Simd.Radix16 Require Import Program Packing.
Import ListNotations. Local Open Scope Z_scope.

Definition result_state := fold_left step tail initial.
Definition expected := digit_expr packed.
Definition check lane k := match stores result_state lane with
 | Some v=>expr_beq (byte v k) (expected lane k) | None=>false end.
Local Lemma checked : forallb (fun j=>forallb (check j) (seq 0 64)) (seq 0 8)=true.
Proof. vm_compute; reflexivity. Qed.
Lemma routed lane k : (lane<8)%nat -> (k<64)%nat ->
 exists v,stores result_state lane=Some v /\ byte v k=expected lane k.
Proof.
 intros L K; pose proof checked as C.
 apply (proj1 (forallb_forall _ _)) with (x:=lane) in C; [|apply in_seq;lia].
 apply (proj1 (forallb_forall _ _)) with (x:=k) in C; [|apply in_seq;lia].
 unfold check in C;destruct(stores result_state lane)as[v|];[|discriminate].
 exists v;split;[reflexivity|now apply internal_expr_dec_bl].
Qed.

Lemma expected_digit s j k :
 (k<64)%nat -> (forall i,(i<5)%nat -> 0<=limb_words s (8*i+j)%nat<B) ->
 value s (expected j k) = (digit (lane_output (limb_words s) j) k) mod 256.
Proof. intros K Bnd; apply routed_digit; auto using packed_word. Qed.
