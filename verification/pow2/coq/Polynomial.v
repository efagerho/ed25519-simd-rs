From Coq Require Import ZArith.
From ProofArithmetic Require Export Polynomial.
Require Import FieldSpec.
Open Scope Z_scope.

(* Field-specific convenience interface to the common integer checker. *)
Definition zero_test := ProofArithmetic.Polynomial.zero_test prime.
Lemma zero_ok env p : zero_test p=true -> represents (polyval env p) 0.
Proof. apply ProofArithmetic.Polynomial.zero_ok;vm_compute;discriminate. Qed.
Definition congruent := ProofArithmetic.Polynomial.congruent prime.
Lemma congruent_ok env a b : congruent a b=true -> represents (val env a) (val env b).
Proof. apply ProofArithmetic.Polynomial.congruent_ok;vm_compute;discriminate. Qed.
