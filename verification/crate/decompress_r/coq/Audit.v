From Coq Require Import ZArith List.
From Machine Require Import isa.Instructions memory.ByteMemory.
From Ed25519Simd.Pow2 Require Audit.
From Ed25519Simd.Decode Require Import Kernels Caller Chunks Image Glue.
Local Open Scope Z_scope.

(* Both calls and RIP-relative data operands use signed rel32 displacements.
   A bound on all three complete images prevents modular target aliases. *)
Definition rel32_range d (ds:list Z) h (hs:list Z) p (ps:list Z) :=
 Z.max (d+Z.of_nat(length ds)) (Z.max (h+Z.of_nat(length hs)) (p+Z.of_nat(length ps)))
 - Z.min d (Z.min h p) < 2^31.

Record decode_contract decoder_pc decoder helper_pc helper pow_pc pow_bytes : Prop := {
 linked_pow2 : Audit.pow2_contract pow_bytes;
 aligned_permutation_tables : decoder_pc mod 64=0;
 relative_addresses : rel32_range decoder_pc decoder helper_pc helper pow_pc pow_bytes;
 caller_binding : caller_image decoder_pc decoder helper_pc pow_pc;
 decoder_projection : exists k,
   kernel_image k decoder_pc decoder helper_pc helper /\
   glue_image decoder_pc decoder helper_pc helper /\
   (forall op, kernel_frame k op /\ forall r load, input op r -> result op r (Instructions.run load (body k op) r)) /\
   (forall y sign t initial,
     slots(prepared_from k y sign initial) 3%nat=slots(prepared k y sign) 3%nat /\
     scheduled_from k y sign t initial=scheduled k y sign t) /\
   forall flat ptr pair pad, byte_memory flat -> (pad<4)%nat ->
   let h:=helper_pc-decoder_pc in let p:=pow_pc-decoder_pc in
   let eax:=return_value h p pair pad (chunk_mask k flat ptr pair) in
   caller_result h p pair pad /\ eax=returned k flat ptr pair /\
   0<=eax<2^Z.of_nat(count pair) /\
   forall j,(j<count pair)%nat -> lane_claim k flat ptr pair j
}.
