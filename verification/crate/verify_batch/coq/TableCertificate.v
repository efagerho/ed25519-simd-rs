From Ed25519Simd.VerifyBatch Require Tables.

Lemma static_tables_correct : Tables.verified.
Proof. vm_compute;repeat split;reflexivity. Qed.
