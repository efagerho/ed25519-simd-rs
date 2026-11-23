From Ed25519Simd.Point Require Import DoublePath Audit.
Theorem assembled_deferred_point_correct : deferred_point_contract.
Proof. constructor; [apply double_image|apply double_path|apply four_round_dispatch]. Qed.
