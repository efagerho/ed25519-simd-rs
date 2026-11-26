# Ed25519 signature verification

Start with `signature_accepts`. It is the predicate on the original input bytes used by both production entry-point theorems. Its input type requires a 32-byte public key and 32 bytes each for R and S. The message can have any length. Both policies require the little-endian scalar `s < L` and decode the public key to an Edwards point A. The challenge is `k = LE(SHA512(R_bytes || key_bytes || message)) mod L`. Hashing uses the supplied encodings, including when a noncanonical encoding is accepted. [Signature predicate and challenge](Signature.v) · [Production contract](../crate/verify_batch/coq/Audit.v)

| Policy | Requirements on R and A | Group equation |
| --- | --- | --- |
| ZIP-215 | The supplied bytes decode to R. Decoding reduces y modulo p and admits either sign when x is zero. | `[8]([s]B) = [8](R + [k]A)` |
| Dalek strict | The supplied R equals the canonical compression of R. Both `[8]A` and `[8]R` differ from the identity. | `[s]B = R + [k]A` |

Audit the base point B, the placement of the cofactor, the encoding rules for each policy, the scalar cutoff, and the hash input and byte order. The equations use the full Edwards group. The equivalence proofs do not assume that the decoded points belong to its prime-order subgroup. [Group equations and base point](Equations.v) · [Point encoding](../curve25519/group/PointEncoding.v) · [SHA-512 definition](../sha512/README.md)

## Equivalence to the assembly checks

`signature_scoring` proves, in both directions for both policies, that the byte-level predicate agrees with scoring the ladder result `Q = [s]B − [k]A`. ZIP-215 tests `[8](Q − R) = identity` for the decoded R. Dalek checks that R is the canonical compression of Q and rejects small-order keys and results. [Equivalence theorem](Optimized.v)

For the predecoded path, `zip215_decoded` binds the cofactor test to the actual decoded A and R. `dalek_coordinates` proves that comparing the two affine coordinates suffices after the scalar, decoding, canonical-y, and small-order checks. A canonical recompression match also suffices to accept a ZIP-215 lane on the deferred path, as proved by `canonical_zip215`. The curve library separately proves that the projective torsion formulas and their determinant shortcut have the stated group meaning. [Decoded signature checks](Optimized.v) · [Canonical fast path](Equations.v) · [Projective torsion formulas](../curve25519/group/Cofactor.v)

The links to instruction execution, register and memory layouts, and the bytes in the linked executable are in the crate proofs. [Production entry points](../crate/verify_batch/README.md)
