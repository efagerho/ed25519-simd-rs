From Ed25519Simd.Point Require Import DoublePath AddPath Outputs Audit.
Theorem assembled_deferred_point_correct : deferred_point_contract.
Proof. constructor; [apply double_image|apply double_path|apply four_round_dispatch|
  apply add_image|apply add_path|apply add_dispatch_correct|apply double_rows|apply add_rows]. Qed.
