# Projective small-order check

The public theorem `assembled_small_order_correct` proves that
`ed25519_simd_small_order_ifma` returns an eight-bit mask. For each valid
projective point P, bit j is set exactly when **[8]P is the identity**.
This requires a valid XYZ representation with nonzero Z. The routine can
be called after the ladder omits T. For arbitrary bounded X and Y the
theorem also specifies the exact four-root field predicate, independently
of point validity. [Public contract](coq/Audit.v) · [Theorem](coq/Object.v) · [Group interpretation](../../curve25519/group/Cofactor.v)

## What to audit

1. Check the SysV argument and result against the Rust caller. RDI points
   to a read-only `WidePoint`. Only its first ten 64-byte rows are readable
   in the model. Rows 0–4 hold X and rows 5–9 hold Y in radix 2^51. Each
   input limb is unsigned and below 2^52. Bit zero corresponds to lane
   zero. The execution permits 24 bytes of private stack below the incoming
   RSP for saved RBP and two nested return addresses. It must return through
   the caller's slot with RBP restored for every incoming SysV alignment.
   [Rust caller](../../../src/wide/avx512ifma/point.rs) · [Shared representation](../Wide51.v) · [Machine and memory trust boundary](../../README.md#shared-audit-surface)
2. Read `lane_result` and `run_correct`. Each lane tests whether any of
   iY, X, iY+X or iY−X is zero modulo p, where i² = −1. The 64-bit filter can
   return zero only when all eight lanes miss every window. If any lane falls
   inside a window, all eight output bits come from the exact computation.
   The group theorem uses the common nonzero projective scale to relate
   the four roots to [8]P. [Filter arithmetic](../../curve25519/SmallOrderFilter.v) · [Linked filter](coq/Filter.v) · [Exact computation](coq/Exact.v)
3. Check **both** symbol addresses, sizes and byte strings against the
   intended release ELF. The entry calls the field multiplier and jumps
   into the root tests inside `ed25519_simd_check_8_torsion_ifma`. Its
   RIP-relative loads also read qwords from both symbols. Coq re-encodes
   the reachable instructions, checks the complete byte strings and runs
   one execution across the two disjoint address ranges. A transfer into
   a gap or a literal cannot return a result. [Audit driver](audit.py) · [Linked execution](../../machine/execution/MaskTrace.v)

## Replay

Build the all-assembly Dalek benchmark so the linker retains the entry
and its helpers. Use the shared Coq toolchain, including Coqprime.

```sh
export RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma"
cargo build --locked --release --features asm --bench cold_profile_dalek \
  --target x86_64-unknown-linux-gnu --message-format=json > /tmp/small-order-build.json
elf=$(jq -r 'select(.target.name == "cold_profile_dalek" and .executable != null) | .executable' /tmp/small-order-build.json)
python3 -B verification/crate/small_order/audit.py "$elf" --output ./small-order-audit
python3 -B verification/crate/small_order/mutations.py "$elf" --audit ./small-order-audit
```

The audit checks the public type, prints its assumptions, runs `coqchk`,
and retains both byte strings and the ELF digest. The mutation tests change
a filter weight, skip the frame-pointer push, corrupt the top carry, and
discard a root in the shared symbol. Each changed ELF must bind to its own
listing. For each mutant, Coq then proves the **negation of the public
contract** using a bounded input with Y = 2^52 − 1 and X = iY modulo p.
The contract requires bit zero to be set. The modeled execution either
clears it or fails to return. [Counterexample](coq/Counterexample.v)
