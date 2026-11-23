From Coq Require Import ZArith.
From Ed25519Simd.Point Require AddBytes.
Definition defer_double := true.
Definition public_add_offset := (AddBytes.public_pc-AddBytes.private_pc)%Z.
