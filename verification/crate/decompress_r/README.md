# Deferred ZIP-215 R decoding

Start with `Ed25519Simd.Decode.Object.assembled_decode_correct`. Its public
type is `decode_contract`. Given one or two chunks of eight arbitrary
32-byte strings, returned bit *j* is set exactly when the low 255 bits of
encoding *j*, interpreted little-endian and reduced modulo *p*, are the
y-coordinate of an Edwards point. In an accepted lane, X is the unique root
with the encoded sign. Either sign is valid for X = 0. Every lane has
Z = 1, T = XY and all twenty coordinate limbs below 2⁵². The five Y limbs
are each below 2⁵¹ and pack to the original low 255 bits, including encodings
from *p* through *p* + 18. Dalek uses these limbs to check canonicality. The high byte of the two-chunk mask belongs to the second
chunk. [Public theorem](coq/Object.v) · [Contract](coq/Audit.v) · [Lane result](coq/Chunks.v)

## What to audit

1. **The mathematical claim.** Check the Edwards equation, the parity of the
   canonical field representative, and the zero exception. The proof derives
   both directions of the root test and uniqueness from the checked prime
   field. The scaled numerator is 121666(y² − 1) and the denominator is y²
   minus that numerator. The single and paired paths use exponent (p − 5)/8.
   [Root and sign specification](../../curve25519/group/Decompression.v) · [Limb tests](coq/Limbs.v)
2. **The release bytes.** The certificate checks the caller, both local paths,
   the arithmetic fragments in the decoder and torsion symbols, their relative
   transfers, constants, and the paired pow2 certificate from the same ELF.
   The kernel checker runs the lifted IFMA instructions and proves their result
   and bounds for arbitrary incoming registers satisfying the kernel inputs.
   It also checks that scratch registers cannot affect the result and that the
   constant registers survive. The single-chunk interpreter checks the exponent
   and tight-limb requirements across the saved fields and square loops.
   [Image binding](coq/Image.v) · [Arithmetic kernels](coq/Kernels.v) · [Single power](coq/Power.v) · [Paired power](../pow2/README.md)
3. **The instruction groups.** Compare each group’s byte expansion with its
   evaluator. Check the qword shuffle indices, masked compare and merge
   behavior, direction of each load and store, sign and validity registers,
   and the mapping of field slots to five consecutive 64-byte rows. The same
   operation lists drive encoding and field-slot execution. The proof follows
   arbitrary input bytes through the transpose and proves the carries,
   conditional negation and parity against the word operations.
   [Schedule and encodings](coq/Glue.v) · [Byte unpacking](coq/Unpack.v) · [IFMA scaling and parity](coq/Scale.v)
4. **The ABI and memory boundary.** The caller supplies RDI pointing to
   one or two 1,280-byte output points aligned to 64 bytes, RSI to the
   corresponding unaligned 256-byte input chunks, and RDX equal to 1 or 2.
   Input, output and private stack storage must be disjoint. The output
   coordinate order is X, Y, Z, T. Check the 2,672 bytes of available stack
   space required by the longest path. The caller interpreter tracks tagged
   input, output and stack addresses, saved registers, the return slot, and
   the pointers and signs passed to each callee. The decoder uses a projection
   to aligned field slots and per-lane masks. Correspondence of these grouped
   operations to native memory effects, including the stores behind Rust’s
   `assume_init_ref`, is part of the human audit. A single flat-memory
   read/write and preservation theorem for the entire decoder is still open.
   [Caller interpreter](coq/Caller.v) · [Paired preparation call](../../../src/wide/avx512ifma/prepare_chunk.S) · [Rust scratch allocation](../../../src/wide/avx512ifma/prepare.rs) · [Shared machine and memory assumptions](../../README.md#shared-audit-surface)

## Replay

Use a linked release ELF that contains the deferred decoder. CI builds
`cold_profile_zip215` with the `asm` feature and retains the symbol images,
Coq sources, manifest, assumption report and kernel replay log.

```sh
python3 -B verification/crate/decompress_r/audit.py "$ZIP_ELF" --output /tmp/decode-audit
python3 -B verification/crate/decompress_r/mutations.py "$ZIP_ELF" --audit /tmp/decode-audit
```

The mutation run changes seven linked operands covering the stack allocation,
mask placement, transpose, single-chain count, carry, parity and denominator.
For the changed carry, Coq also checks the new instruction encoding and proves
that multiplying two zero fields produces a nonzero residue.
