# Scalar reduction assembly

On x86-64 Linux, `asm` enables all assembly backends, including `reduce.S`
for eight-lane 512-bit challenge reduction. The Rust reducer remains the default
and the test reference. Radix-16 recoding stays in Rust.
The [Coq certificate](../../verification/scalar/README.md)
proves canonical reduction, ABI preservation, and concrete byte-memory safety
for the linked assembly. `verify-asm-scalar` checks that proof during the build
and embeds the certified bytes for this routine. It also enables `asm`.

The assembly takes disjoint input/output buffers of 512/320 bytes, without
vector alignment requirements. Each input row contains one 64-bit word from
each lane; each output row contains one radix-2^52 limb. The output is the
canonical residue modulo L, with all five limbs below 2^52. The routine has
no calls, stack scratch, opmask operations, or data-dependent control flow.

## Arithmetic and optimization

Let `B=2^52`, `R=B^5`, and `H=a+2^256*b`, where both halves are below 2^256.
The two constant multipliers are `R mod L` and `(2^256*R) mod L`. Accumulating
both products before Montgomery reduction gives a product `T < R*L/8`.
Consequently `(T+n*L)/R < 9*L/8` for the Montgomery correction `0 <= n < R`,
so one conditional subtraction suffices. This removes one Montgomery
reduction and two canonicalization steps from the Rust algorithm.

Each eliminated low column `x` has correction `q=-x*L0^-1 mod B`. Its low
product satisfies `(q*L0) mod B = (-x) mod B`, so the carry from adding it is
`ceil(x/B)`. Computing this as `(x+B-1) >> 52` removes five dependent low-half
IFMAs. The high-half products remain necessary. The assembly comments record
the intermediate bounds that prevent overflow.

On an AMD EPYC 9555P, pinned to CPU 4, seven alternating release runs of
15 million calls gave these medians. Every build used assembly for paired
field exponentiation, four point doublings, and cached point addition;
one call reduces eight scalars.

| Implementation | ns/call |
|---|---:|
| Rust reference | 61.82 |
| Fused Montgomery assembly | 30.66 |
| Assembly with shortened carry chain | 28.81 |

A variant using only the upper-half Montgomery product followed by a fold
using `2^252 = -(L-2^252) mod L` measured 29.17 ns/call. It used fewer IFMAs
but lengthened the correction chain, so it was not retained. These isolated
measurements do not establish a comparable whole-verifier speedup.

## Validation and reproduction

The tests compare exact limbs against the Rust reducer, canonical bytes
against an independent scalar implementation, and SIMD recoding against the
scalar Rust recoder. Inputs
include every single-bit boundary, shifted multiples of L and their
neighbors, full-width random values, zero, and the maximum 512-bit integer.
Native probes check callee-saved registers, stack restoration, all 64 buffer
alignments, canaries, read-only input, and guard pages.

```sh
export RUSTFLAGS='-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma'
features=asm
cargo test --release --features "$features"
taskset -c 4 cargo test --release --features "$features" --lib \
  scalar::wide::tests::profile_scalar_reduce -- --exact --ignored --nocapture
ED25519_SCALAR_PATH=rust taskset -c 4 cargo test --release \
  --features "$features" --lib scalar::wide::tests::profile_scalar_reduce \
  -- --exact --ignored --nocapture
```

Set `ED25519_SCALAR_ITERS` to change the profiling duration. The ignored
benchmark requires release mode and `asm`, including assembly pow2.
