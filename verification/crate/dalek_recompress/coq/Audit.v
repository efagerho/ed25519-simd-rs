From Coq Require Import ZArith List Bool.
From Machine Require Import memory.ByteMemory execution.MaskTrace.
From Curve25519 Require Import Radix51.
From Curve25519.group Require Import Affine Representation.
From Ed25519Simd.SmallOrder Require Audit.
From Ed25519Simd.Decode Require Import Kernels Image Unpack.
From Ed25519Simd.Dalek Require Import Caller FieldOps Encoding Batch Schedule.
Import ListNotations. Local Open Scope Z_scope.

Definition shared_image k d ds h hs :=
 field_image k d ds h hs /\
 at_bytes hs 0xbae (vectors(skipn 5 (seed_columns k))++call 0xbfc 0xcb0++vectors(fold_columns k)++[0xc3]) /\
 at_bytes ds 0xa7e (vectors(Kernels.carry k)++[0xc3]) /\
 at_bytes ds 0xb00 (flat_map word_bytes
   (map (fun i=>2*Z.of_nat i) (seq 0 8)++map (fun i=>2*Z.of_nat i+1) (seq 0 8)++[1;radix-19])).
Definition span a (bs:list Z) := (a,a+Z.of_nat(length bs)).
Fixpoint disjoint_images (images:list(Z*Z)) := match images with
 | []=>true | (a,b)::tail=>forallb (fun cd=>let '(c,d):=cd in (b<=?c)||(d<=?a)) tail &&
   disjoint_images tail end.
Definition linked images := disjoint_images images &&
 forallb (fun ab=>let '(a,b):=ab in (0<=?a)&&(b <? 2^64) &&
 forallb (fun cd=>b-fst cd <? 2^31) images) images.
Definition input_layout (n:nat) pts enc := n=O \/
 pts mod 64=0 /\ 0<=pts /\ pts+1280*Z.of_nat n<=2^64 /\
 0<=enc /\ enc+256*Z.of_nat n<=2^64.
Definition small_call s h flat pts pad (initial:nat->nat->nat->Z) i :=
 MaskTrace.result (Audit.run_at s h pad) (Audit.inputs (point_words flat pts i)) (initial i).

(* The integer read by encoded is little endian. compress is the canonical
   y residue with bit 255 equal to the parity of canonical x. *)
Record recompress_contract
    (entry_pc : Z) (entry_bytes : list Z) (decoder_pc : Z) (decoder_bytes : list Z)
    (helper_pc : Z) (helper_bytes : list Z) (small_pc : Z) (small_bytes : list Z) : Prop := {
  caller_image :
    entry_bytes = caller_bytes (decoder_pc-entry_pc) (helper_pc-entry_pc) (small_pc-entry_pc);
  linked_layout :
    decoder_pc mod 64 = 0 /\
    linked [span entry_pc entry_bytes; span decoder_pc decoder_bytes;
            span helper_pc helper_bytes; span small_pc small_bytes] = true /\
    placement (decoder_pc-entry_pc) (helper_pc-entry_pc) (small_pc-entry_pc) 0 order = true;
  small_order_object : Audit.small_order_contract small_pc small_bytes helper_pc helper_bytes;
  recompress_result : exists k,
    shared_image k decoder_pc decoder_bytes helper_pc helper_bytes /\
    (forall op, kernel_frame k op) /\ field_frame (fused k) fused_live /\
    forall n flat pts enc P pad initial,
      (n <= 8)%nat -> input_layout n pts enc -> byte_memory flat -> (pad < 4)%nat ->
      (forall i, (i < n)%nat -> valid_chunk (point_words flat pts i) (P i)) ->
      exists rax,
        execute k flat pts enc (small_call small_pc helper_pc flat pts pad initial) n = Some rax /\
        0 <= rax < 2^(8*Z.of_nat n) /\
        forall i j, (i < n)%nat -> (j < 8)%nat ->
          (Z.testbit rax (8*Z.of_nat i + Z.of_nat j) = true <->
           encoded flat (Batch.ptr enc i) j = compress (P i j) /\ multiple 8 (P i j) <> identity)
}.
