From Ed25519Simd.Decode Require PowAddress.
From Coq Require Import ZArith Lia.
From Ed25519Simd.Pow2 Require Object ObjectBytes.
From Ed25519Simd.Decode Require Import Kernels Chunks Caller Image Glue Program Audit.
From Ed25519Simd.Decode Require DecoderBytes HelperBytes.

Theorem assembled_decode_correct : decode_contract
 DecoderBytes.address DecoderBytes.symbol_bytes HelperBytes.address HelperBytes.symbol_bytes
 PowAddress.address ObjectBytes.symbol_bytes.
Proof.
 constructor.
 - exact Object.assembled_symbol_correct.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - exists code. split;[vm_compute;repeat split;reflexivity|].
   split;[vm_compute;repeat split;reflexivity|].
   assert (K:forall op, verified code op=true) by (destruct op;vm_compute;reflexivity).
   split;[intro op;split;[apply frame_ok;destruct op;vm_compute;reflexivity|apply verified_result,K]|].
   split;[apply incoming_words_unused|]. intros flat ptr pair pad B Pad h p eax.
   assert (Caller:caller_result h p pair pad).
   { destruct pad as [|[|[|[|pad]]]];try lia;destruct pair;vm_compute;repeat split;reflexivity. }
   pose proof(returned_by_caller h p code flat ptr pair pad Caller) as E.
   split;[exact Caller|]. unfold eax;rewrite E;split;[reflexivity|]. exact (decode_chunks code (K Multiply) (K ChainMultiply) (K Square) flat ptr pair B).
Qed.
