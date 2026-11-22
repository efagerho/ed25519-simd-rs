# Signature scalar preparation

The theorem `assembled_signature_scalar_correct` covers one pre-hash call to
`ed25519_simd_prepare_signature_scalars`. For each of eight lanes, bit *j*
of RAX is set exactly when the unsigned little-endian input S is below the
Ed25519 group order L. An accepted row contains 64 signed bytes in **[−8, 7]**
whose radix-16 value equals **S** as an integer. A rejected row contains 64
zero bytes. All higher bits of RAX are zero. [Public contract](coq/Audit.v) · [Theorem](coq/Object.v)

## What to audit

1. Compare the call in `prepare_chunk.S` with the contract. RSI points to eight pointers to
   32-byte scalars. Inputs may be unaligned and pointers may repeat. RDI
   designates 512 disjoint writable bytes. Digit zero is least significant.
   Check that the caller takes S from the second half of each signature and
   uses the returned bit for the corresponding lane. A Coq entry witness
   admits every 256-bit S with all eight pointers sharing one unaligned
   scalar. [Entry witness](coq/EntryTests.v) · [Caller](../../../src/wide/avx512ifma/prepare_chunk.S) · [Rust input layout](../../../src/wide/avx512ifma/prepare.rs)
2. Check the ELF evidence for the entire function and the 32 read-only bytes
   containing L. Coq re-encodes the listing, including the signed displacements
   from the ends of the RIP-relative loads, and checks the literal as a
   little-endian integer against the curve order. Runtime placement assumes
   the loader maps those bytes at the same load bias as the code. [Extraction](audit.py) · [Listing](coq/Program.v) · [Order](../../curve25519/Scalar.v)
3. Check the shared x86 and flat-memory semantics, including zeroed upper
   comparison bits, mask-gated compares, merge-masked addition, and which
   blend source a set bit selects. The theorem covers all initial mask bits.
   The pointer and scalar reads are bounded, each of the eight rows is
   initialized, and every byte outside the output is preserved. RET reads
   the incoming return address, advances RSP by eight, and preserves the
   SysV callee-saved registers. The trust boundary includes the modeled
   instruction encodings and semantics, valid mapped buffers, and execution
   on the supported CPU. [Shared audit surface](../../README.md#shared-audit-surface) · [Mask semantics](../../machine/execution/MaskedWords.v) · [Shared digit packing](../Radix16Output.v)

## Replay

Use a release verifier ELF built with assembly enabled and a fresh output directory.

```sh
python3 -B verification/crate/signature_scalar/audit.py "$ELF" --output ./signature-scalar-audit
python3 -B verification/crate/signature_scalar/mutations.py "$ELF" --audit ./signature-scalar-audit
```

The audit checks the public theorem type, its assumptions and its dependencies
with `coqchk`. The mutations raise the linked order by one, drop the carry
from the low word, and expose a digit in a rejected lane. Each mutation has
a re-encoded listing and a concrete Coq counterexample. [Counterexamples](coq/Counterexample.v)
