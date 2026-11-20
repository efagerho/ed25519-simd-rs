# Scalar reduction and signed radix-16 assembly

On x86-64 Linux, `asm` routes eight 512-bit challenge digests through
`ed25519_simd_digest_to_radix16`. It calls the scalar reducer and returns
eight arrays of 64 signed radix-16 digits. The Rust implementation serves
as the default and the test reference. [Assembly entry point](radix16.S)

The [Coq certificate](../../verification/crate/scalar/README.md)
proves canonical reduction, ABI preservation, and concrete byte-memory safety
for `ed25519_simd_scalar_reduce_ifma`. `verify-asm-scalar` enables `asm`,
checks that proof during the build, and embeds the certified reducer bytes.
The digit conversion and lane placement currently have differential and ABI tests.

The reducer takes disjoint input/output buffers of 512/320 bytes, without
vector alignment requirements. Each input row contains one 64-bit word from
each lane; each output row contains one radix-2^52 limb. The output is the
canonical residue modulo L, with all five limbs below 2^52. The routine has
no calls, stack scratch, opmask operations, or data-dependent control flow.

The digest entry point takes disjoint, possibly unaligned 512-byte buffers.
It uses the first 320 output bytes for the reducer and loads all five limbs
before overwriting them. Adding a repeated nibble 8 with carries biases the
canonical residue. Subtracting 8 from each of the low 64 nibbles gives a
digit in `-8..=7`. The final shuffle places digit `j` of lane `i` at byte
`64*i+j`, with the least significant digit first.

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

The digit conversion packs biased limb pairs with addition. A carry bit
above bit 51 contributes directly to its output word. This removes four
limb masks and one carry propagation step. On the same EPYC 9555P core,
nine alternating runs of five million eight-digest calls with `asm` enabled
gave medians of 43.77 ns before the change and 41.56 ns after it.

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

Set `ED25519_SCALAR_ITERS` to change the profiling duration. Set
`ED25519_SCALAR_PATH=digits` to time the complete digest-to-digits call.
For instruction samples, use the release test executable Cargo prints
when running `cargo test --release --features asm --lib --no-run`.

```sh
ED25519_SCALAR_PATH=digits ED25519_SCALAR_ITERS=20000000 \
  perf record -e cycles:u -c 29989 -- taskset -c 4 "$test_executable" \
  scalar::wide::tests::profile_scalar_reduce --exact --ignored --nocapture
perf annotate --stdio -M intel ed25519_simd_digest_to_radix16
```
