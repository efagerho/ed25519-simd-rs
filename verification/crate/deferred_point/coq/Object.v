From Ed25519Simd.Point Require Import DoublePath AddPath Concrete Audit.
Theorem assembled_deferred_point_correct : deferred_point_contract.
Proof. constructor; [apply double_image|apply add_image|apply concrete_correct]. Qed.
