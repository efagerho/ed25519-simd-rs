From Coq Require Import List ZArith Lia.
From Ed25519Simd Require Import Radix16Output.
From Ed25519Simd.SignatureScalar Require Import Program Audit Execution ObjectBytes OrderBytes.

Theorem assembled_signature_scalar_correct :
 signature_scalar_contract ObjectBytes.address ObjectBytes.symbol_bytes OrderBytes.address OrderBytes.symbol_bytes.
Proof.
 constructor.
 - vm_compute;repeat split;reflexivity.
 - vm_compute;split;reflexivity.
 - vm_compute;split;reflexivity.
 - intros j J;destruct (output_routed j 0 J ltac:(lia)) as [v [Store _]];now exists v.
 - intros slide entry ks P W M.
   apply (verified_call ObjectBytes.address (Z.of_nat (length ObjectBytes.symbol_bytes))
     OrderBytes.address slide OrderBytes.symbol_bytes entry ks);try assumption.
   vm_compute;repeat split;reflexivity.
Qed.
