# Deferred Dalek recompression

Start with `assembled_dalek_recompress_correct`. For zero to eight chunks of
eight valid projective Edwards points, bit `8*i+j` of RAX is set exactly when
the 32 original bytes for lane `j` of chunk `i` equal the canonical compressed
point **and** `[8]P ≠ identity`. All unused bits are zero, including the entire
return word for an empty batch. The theorem binds the recompressor and its
three linked dependency symbols to one ELF. [Public theorem](coq/Object.v) · [Contract](coq/Audit.v)

## What to audit

1. **Inputs and acceptance.** RDI addresses 64-byte-aligned, 1,280-byte
   points. RSI addresses consecutive 256-byte chunks of eight little-endian
   encodings. RDX is the chunk count. The caller must supply readable spans.
   The X, Y and Z limbs must be below 2⁵² and represent a curve point with
   nonzero Z. T can be arbitrary. Check that `compress` uses canonical affine
   y and the low bit of canonical affine x as bit 255. Compare the direction
   of the cofactor test and the mapping from chunk and lane to the result bit
   with both queue flush routines. [Dalek caller](../../../src/wide/avx512ifma/dalek.S) · [ZIP-215 caller](../../../src/wide/avx512ifma/zip215.S) · [Encoding](coq/Encoding.v) · [Small-order theorem](../small_order/README.md)
2. **Arithmetic and shortcuts.** The field checker evaluates the lifted IFMA
   instructions for the fused comparison, multiplication and squaring. It
   proves that the biased difference lies in the range where the digit test
   for p recognizes zero modulo p. The chain interpreter checks every
   multiply, square count and saved operand, including the overwrite of the
   last prefix with z¹¹. The backward pass recovers each reciprocal from the
   saved prefixes. The proof covers the all-y-mismatch exit, both parity
   paths and the per-chunk skip of the small-order call. [Fused kernel and inversion](coq/FieldOps.v) · [Batch arithmetic](coq/Batch.v) · [Mask packing](coq/Masks.v)
3. **Instruction groups and memory.** Compare the groups in `Caller.v`
   and their interpretation in `Schedule.v` with the disassembly. In
   particular, check the five Y memory operands forwarded to the subtraction
   kernel, the two mask bytes per chunk, the out-of-line parity carry/XOR,
   mask zero-extension and the prologue and epilogue. The symbolic caller
   invalidates the vector constants across scoring and checks that they are
   reloaded before another field operation. Coq checks
   the group encodings, relative targets and constants against the release
   bytes, and checks the symbolic caller's paths for every supported count.
   The model reads point words and encodings from byte memory, and represents
   the private stack as field and mask slots. Native correspondence for
   these groups, register save/restore, and isolation of the aligned stack
   from input and code are part of the audit. Whole-function flat-memory
   preservation and timing behavior are outside the theorem.
   [Caller and encodings](coq/Caller.v) · [Symbolic execution](coq/Schedule.v) · [Shared machine and memory assumptions](../../README.md#shared-audit-surface)

## Replay

Use the all-assembly Dalek hot-profile ELF, which retains the recompression
entry and the shared code reached through local labels. Both commands use
the same release artifact.

```sh
export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma"
cargo build --locked --release --target x86_64-unknown-linux-gnu --features asm \
  --bench hot_profile_dalek --message-format=json > /tmp/dalek-build.json
elf=$(jq -r 'select(.target.name=="hot_profile_dalek" and .executable != null) | .executable' /tmp/dalek-build.json)
python3 -B verification/crate/dalek_recompress/audit.py "$elf" --output /tmp/dalek-audit
python3 -B verification/crate/dalek_recompress/mutations.py "$elf" --audit /tmp/dalek-audit
```

The audit emits the pinned theorem, assumption report, kernel replay log and
symbol bytes. The mutation suite changes the stack size, canonical comparison,
preceding-prefix address, inversion exponent, mask placement, small-order
exclusion, parity carry and shared field carry. For
the last edit Coq also proves a concrete counterexample in the rebound ELF.
