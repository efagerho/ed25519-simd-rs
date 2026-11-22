From Coq Require Import ZArith Lia List.
From Machine Require Import memory.ByteMemory execution.LinkedCalls execution.MaskTrace.
From ProofArithmetic Require Import Radix.
From Curve25519 Require Import Field Scalar Edwards Radix51.
From Curve25519.group Require Import PrimeField Affine Representation Decompression SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Scalar Require Import ScalarSpec.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.FullLadder Require Audit Object LinkedBytes.
From Ed25519Simd.Radix16 Require Audit Object LinkedBytes.
Local Open Scope Z_scope.

(* Combine the reducer's actual return memory and the full ladder execution.
   The call boundary passes the same 512 digit bytes to R8. *)
Module D := Ed25519Simd.Radix16.Audit.
Module F := Ed25519Simd.FullLadder.Audit.
Definition challenge s j := lane_input (buffer_words (LinkedCalls.mem s) (LinkedCalls.regs s 6%nat)) j mod L.
Definition candidate s l B A j :=
 plus (scale (number 16 (digit_list l 1 j)) B) (scale (-challenge s j) (A j)).

(* The two callee models meet at the reducer's 512 output bytes. *)
Definition reduce_call slide s ip mid :=
  D.run slide Radix16.LinkedBytes.wrapper_pc Radix16.LinkedBytes.reducer_pc
        (D.size Radix16.LinkedBytes.symbol_bytes) s ip mid.
Definition passes_digits s l mid := forall j, (j < 8)%nat ->
  digit_list l 8 j = D.signed_digits (LinkedCalls.mem mid) (LinkedCalls.regs s 7%nat) j.

Record call_inputs (full:bool) slide s l B A : Prop := {
  digest_layout : D.placement (LinkedCalls.regs s 4%nat) (LinkedCalls.regs s 7%nat) (LinkedCalls.regs s 6%nat)
    (slide + Radix16.LinkedBytes.wrapper_pc) (D.size Radix16.LinkedBytes.symbol_bytes)
    (slide + Radix16.LinkedBytes.reducer_pc) (D.size Ed25519Simd.Scalar.ObjectBytes.symbol_bytes);
  digest_entry_valid : LinkedCalls.well_formed s;
  ladder_layout : F.placement slide l;
  ladder_mode : LinkedCalls.regs l 9%nat = Ed25519Simd.FullLadder.Native.bits full;
  ladder_inputs : valid_inputs (slide + FullLadder.LinkedBytes.stage_pc) (F.pad_of l) l;
  ladder_tables : valid_tables l B A
}.
Record observation (full:bool) slide s l mid out B A ip : Prop := {
  entry_inputs : call_inputs full slide s l B A;
  digest_call : reduce_call slide s ip mid;
  digit_handoff : passes_digits s l mid;
  ladder_call : F.execution slide l full out
}.

Lemma product_returns full slide s l B A :
  call_inputs full slide s l B A ->
  (forall ip mid, reduce_call slide s ip mid -> passes_digits s l mid) ->
  exists mid out ip, observation full slide s l mid out B A ip.
Proof.
  intros Inputs Handoff. destruct Inputs as [P W PL T I V].
  destruct (D.run_correct _ _ _ _ Ed25519Simd.Radix16.Object.assembled_digest_to_radix16_correct
    slide s P W) as [mid [Run _]].
  destruct (F.full_product Ed25519Simd.FullLadder.Object.assembled_full_ladder_correct
    slide l full B A PL T I V) as [[out Exec] _].
  exists mid, out, (read_word (LinkedCalls.mem s) (LinkedCalls.regs s 4%nat)).
  constructor; [constructor; assumption | exact Run | eapply Handoff; exact Run | exact Exec].
Qed.

Definition product_correct (full:bool) := forall slide s l mid out B A ip,
 observation full slide s l mid out B A ip ->
 strict out /\ forall j,(j<8)%nat -> represents_point full (point_values out j) (candidate s l B A j).
Lemma product_ok full : product_correct full.
Proof.
 intros slide s l mid out B A ip [[P W PL T I V] Run Dig LRun].
 destruct (D.run_correct _ _ _ _ Ed25519Simd.Radix16.Object.assembled_digest_to_radix16_correct
    slide s P W) as [v [_ [Unique [_ [_ [_ [_ Digits]]]]]]].
 destruct (Unique _ _ Run) as [_ ->].
 destruct (F.full_product Ed25519Simd.FullLadder.Object.assembled_full_ladder_correct
  slide l full B A PL T I V) as [_ Result].
 destruct (Result out LRun) as [Bound [Reps _]]. split;[exact Bound|].
 intros j J. specialize (Reps j J). rewrite Dig in Reps by exact J.
  rewrite (proj2 (Digits j J)) in Reps. exact Reps.
Qed.
