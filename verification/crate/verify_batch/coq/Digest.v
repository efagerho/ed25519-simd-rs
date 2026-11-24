From Coq Require Import List ZArith Strings.Byte Lia Ring.
From Machine Require Import execution.LinkedCalls memory.ByteMemory memory.FlatMemory.
From ProofArithmetic Require Import Radix.
From SHA512 Require Facts Spec.
From Ed25519Simd.Scalar Require ScalarSpec.
From Ed25519Simd.Sha512Challenge Require Output.
From Ed25519Simd.VerifyBatch Require Import Policy.
Import ListNotations. Local Open Scope Z_scope.

Lemma read_octets m a n : byte_memory m -> little_endian (octets m a n) = read_le n m a.
Proof.
  intro B. unfold octets, little_endian. rewrite map_map.
  assert (H: forall k i, byte_value (Spec.low_byte (Z.to_N (m (k + Z.of_nat i)))) =
                          m (k + Z.of_nat i)).
  { intros. unfold byte_value. rewrite Facts.low_byte_value, N.mod_small; specialize (B (k+Z.of_nat i)); lia. }
  rewrite (map_ext _ _ (H a)).
  assert (R:forall base off, number 256 (map (fun i => m (base + Z.of_nat i)) (seq off n)) =
                               read_le n m (base + Z.of_nat off)).
  { induction n as [|n IH]; intros; [reflexivity|]. cbn [map seq number read_le].
    rewrite IH, Nat2Z.inj_succ. replace (base+Z.succ (Z.of_nat off)) with (base+Z.of_nat off+1) by lia.
    reflexivity. }
  rewrite R, Z.add_0_r. reflexivity.
Qed.

Definition digest_cell out j i := out + 64*Z.of_nat (i/8) + 8*Z.of_nat j + Z.of_nat (i mod 8).

Lemma word_at m out j i :
  read_word m (out + 8 * Z.of_nat (8*i+j)) =
  number 256 (map (fun b=>m (digest_cell out j b)) (seq (8*i) 8)).
Proof.
  assert (H:forall k, (k<8)%nat ->
     digest_cell out j (8*i+k) = out + 8*Z.of_nat(8*i+j) + Z.of_nat k).
  { intros k K. unfold digest_cell.
    replace (8*i+k)%nat with (k+i*8)%nat by lia.
    rewrite Nat.div_add, Nat.mod_add, Nat.div_small, Nat.mod_small by lia. lia. }
  set (a:=out+8*Z.of_nat(8*i+j)) in *.
  assert (R:forall n k, (k+n<=8)%nat ->
    read_le n m (a+Z.of_nat k) =
    number 256 (map (fun b=>m(digest_cell out j b)) (seq (8*i+k) n))).
  { induction n as [|n IH]; intros k K; [reflexivity|].
    cbn [seq map number read_le]. rewrite H by lia.
    replace (a+Z.of_nat k+1) with (a+Z.of_nat(S k)) by lia.
    replace (S (8*i+k)) with (8*i+S k)%nat by lia. rewrite IH by lia. reflexivity. }
  specialize (R 8%nat 0%nat ltac:(lia)). now rewrite Nat.add_0_r,Z.add_0_r in R.
Qed.

Lemma scalar_digest m out j :
 ScalarSpec.lane_input (buffer_words m out) j =
 number 256 (map (fun i=>m(digest_cell out j i)) (seq 0 64)).
Proof.
  unfold ScalarSpec.lane_input,buffer_words.
  change (number ScalarSpec.W (map (fun i=>read_word m (out+8*Z.of_nat(8*i+j))) (seq 0 8)) = number 256 (map (fun i=>m(digest_cell out j i)) (seq 0 64))).
  rewrite (map_ext _ _ (word_at m out j)).
  generalize (fun i=>m(digest_cell out j i)); intro b.
  change ScalarSpec.W with 18446744073709551616. cbv [seq map number Nat.mul Nat.add]. ring.
Qed.

(* The reducer consumes the very same 64 bytes in little-endian scalar order. *)
Lemma sha_to_scalar s after j : (j<8)%nat -> Output.challenge_digests s after ->
 ScalarSpec.lane_input (buffer_words after (regs s 7%nat)) j =
 little_endian (Spec.sha512 (Output.challenge_input s j)).
Proof.
  intros J Digests. rewrite scalar_digest. unfold little_endian, digest_cell.
  now rewrite (Digests j J).
Qed.
