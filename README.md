# ed25519-simd

`ed25519-simd` is a verification-only Ed25519 crate focused on high-throughput
batch verification. It verifies signatures and reports the result for each input
element; it does not provide signing APIs or handle private key material.

The implementation is designed to be acceptance-compatible with
[`solana-ed25519`]. The tests include differential checks against
`solana-ed25519` for both supported verification policies and for edge cases
such as small-order points, non-canonical encodings, and scalar-boundary
signatures.

## Requirements

**This crate requires `x86_64` with AVX-512 (F, DQ, IFMA) and has no scalar
fallback.** All verification — including single-signature checks and partial
batches — runs through the AVX-512 IFMA SIMD path. The crate fails at compile
time unless the required target features are enabled.
Build with the target CPU enabled, e.g.:

```sh
RUSTFLAGS="-C target-cpu=native" cargo build --release
```

For the throughput reported below, enable whole-program LTO and one codegen
unit in the consuming workspace. Cargo does not apply release-profile settings
from dependency manifests:

```toml
[profile.release]
lto = true
codegen-units = 1
```

Without those settings, verification remains correct but leaves more large
SIMD helpers across call boundaries and is typically a few percent slower.

Doc tests compile through `rustdoc`, so pass the same CPU target there too:

```sh
RUSTFLAGS="-C target-cpu=native" RUSTDOCFLAGS="-C target-cpu=native" cargo test --doc
```

AVX-512 IFMA is available on Intel Ice Lake and later, and on AMD Zen 4 and later.

Because the SIMD path is selected at compile time, **AVX-512 F, DQ, and IFMA
support, including OS support for AVX-512 register state, is a deployment
prerequisite.** A binary built with `-C target-cpu=native` must run on the same
CPU it was built for, or one that is at least as capable. Alternatively, use
explicit `-C target-feature=+avx512f,+avx512dq,+avx512ifma` flags that match
every deployment host.

The crate performs no runtime CPU-feature detection and has no fallback path.
The target-feature flags apply to the entire binary, not just this crate, so
the compiler may emit AVX-512 instructions in application, dependency, or
standard-library code before any `ed25519-simd` API is called. Running the
binary on a host without the required CPU and OS support may therefore
terminate with an illegal-instruction fault (`SIGILL`) at any point.

## Scope

This crate only verifies signatures. Signing is intentionally out of scope:
private key material raises a much stricter implementation bar, especially
around side channels that can leak secret scalar bits through timing, memory
access, or microarchitectural behavior. Verification only handles public inputs,
which makes the crate a narrower and more auditable component.

## Verification Policies

The verifier supports two policy modes:

- `VerifyPolicy::Zip215` is the default. It performs the ZIP-215 cofactored
  check and accepts non-canonical point encodings according to the
  `verify_zebra` / batch verifier behavior.
- `VerifyPolicy::Dalek` performs a stricter Dalek-style canonical-`R` check and
  applies `solana-ed25519`'s legacy excluded-encoding filters.

Both policies reject non-canonical `S` scalars (`S >= L`).

The `Dalek` policy name means "match `solana-ed25519`'s `verify_dalek` entry
point", not "match the `Dalek` row in ed25519-speccheck". Speccheck's Dalek row
describes the acceptance set of the Dalek implementation it tested, which
accepts some small-order and non-canonical edge cases. `solana-ed25519`'s
`verify_dalek` behavior is stricter for this crate's compatibility target: it
requires canonical `R` and applies legacy excluded-encoding filters. The
speccheck fixtures in this repository therefore use speccheck's fixed
expectations for `Zip215`, but use `solana-ed25519` itself as the oracle for
`VerifyPolicy::Dalek`.

## Batch Verification

All verification goes through a `Verifier`, which is constructed once and reused.
It holds the precomputed base-point table and a pluggable, statically-selected
key cache, so construction is not free — build it once and call `verify_batch`
repeatedly:

```rust,no_run
use ed25519_simd::{Verifier, VerifyInput};
# let public_key = [0u8; 32];
# let signature = [0u8; 64];
# let message: &[u8] = b"hello";

let mut verifier = Verifier::new();

let inputs = [VerifyInput {
    public_key,
    signature,
    message,
}];

let mut out = vec![false; inputs.len()];
verifier.verify_batch(&inputs, &mut out);
// out[0] is true iff `signature` is valid for (public_key, message).
```

Each output entry corresponds to the input at the same index, so callers can see
which signatures passed or failed. `out` must be the same length as `inputs`;
`verify_batch` panics otherwise. `Verifier::new()` uses the default
`VerifyPolicy::Zip215` policy and no retained-key cache; see
[Verification Policies](#verification-policies) and [Key
Caching](#key-caching) for the other constructors.

## Key Caching

Verification repeatedly needs a decoded public key and a precomputed
variable-base multiplication table. `Verifier::new()` and
`Verifier::with_policy(...)` use `NullKeyCache`, so decoded keys are not retained
across batches. **`NullKeyCache` is the recommended default** for most
workloads: it keeps cold or mostly-distinct-key workloads from paying for
cache bookkeeping they do not use, and it needs no assumptions about the
shape of the workload to be safe.

Only reach for `HotKeyCache` if you have actual knowledge of your key
distribution — specifically, that a small set of keys repeats often enough
across batches to be worth retaining. Caching a hot set you don't actually
have wastes memory and bookkeeping for no benefit. The [Hot Key
Repeats](#hot-key-repeats) benchmark below quantifies the win on a workload
that does repeat a small key set; measure your own workload before relying on
it, since the win shrinks or disappears as the hot set gets larger or less
repetitive:

- `HotKeyCache::with_capacity(n)` is the only constructor: the bound is
  mandatory. Public keys are attacker-supplied and each retained one costs a
  few kilobytes, so an unbounded cache would be a memory-exhaustion vector.
  Requiring a bound also forces the question that decides whether this cache
  helps at all — how many keys actually repeat. If you can't answer it, use
  `NullKeyCache`.
- Eviction is exact least-recently-used, and both lookup and eviction are
  O(1), so a caller feeding the verifier nothing but distinct keys cannot
  amplify eviction cost.
- `HotKeyCache::set_capacity(n)` re-bounds an existing cache, evicting
  immediately down to the new bound. `n` is clamped to at least one.
- Successful key decodes are retained after verification, so reuse the same
  verifier across batches when the key distribution is hot.

The verifier keeps any per-chunk decoded tables in local scratch while a chunk
is being verified, even with `NullKeyCache`:

```rust,no_run
use ed25519_simd::{HotKeyCache, Verifier, VerifyPolicy};

let mut verifier = Verifier::with_cache(
    VerifyPolicy::Zip215,
    HotKeyCache::with_capacity(256),
);
```

## SIMD Path

The crate batches eight signatures per AVX-512 IFMA chunk. There is no scalar
fallback: single verifications and ragged batch tails are processed as padded
SIMD chunks, and required target features are enforced by the root compile-time
gate (see [Requirements](#requirements)).

## Benchmark Snapshot

The following numbers are Criterion estimates in microseconds per signature for
distinct-key batches. The `ed25519-simd` rows use `NullKeyCache`, so decoded keys
are not retained across batches.

The `ed25519-simd` rows were refreshed independently on an AMD EPYC 9555P with
rustc 1.95.0, pinned to CPU 4. Only benchmark IDs containing `ed25519_simd` ran;
the comparison rows are retained from the previous full comparison run and are
therefore not from the same execution. Criterion used its default 3-second
warm-up, 5-second measurement, and 100 samples. The widest displayed 95%
confidence interval among the refreshed rows was about 0.08% of the estimate.

The comparison bench lives in the `benches-compare` workspace member. These
commands refresh only this crate's rows used below:

```sh
cd benches-compare
for filter in \
  'distinct_keys/msg_len_1/ed25519_simd' \
  'distinct_keys/msg_len_1024/ed25519_simd' \
  'distinct_keys/msg_len_mixed/ed25519_simd' \
  'hot_keys/distinct_4/ed25519_simd'
do
  taskset -c 4 env \
    RUSTFLAGS="-C target-cpu=native -C target-feature=+avx512f,+avx512dq,+avx512ifma" \
    cargo bench --bench solana_ed25519_compare -- \
      "$filter" --noplot --discard-baseline
done
```

Message length 1:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 4.65 | 4.65 | 4.65 | 4.65 |
| ed25519-simd Dalek null-cache | 4.61 | 4.61 | 4.61 | 4.61 |
| solana-ed25519 Zip215 batch[^batch-api] | 13.86 | 12.85 | 12.40 | 12.17 |
| solana-ed25519 Dalek loop | 22.45 | 22.39 | 22.38 | 22.45 |
| ed25519-dalek batch[^batch-api] | 14.30 | 13.21 | 12.68 | 12.44 |
| ed25519-dalek loop | 20.24 | 20.21 | 20.20 | 20.22 |
| aws-lc-rs parsed loop | 22.59 | 22.61 | 22.62 | 22.59 |
| ring loop | 30.67 | 30.60 | 30.59 | 31.58 |
| sodiumoxide loop | 35.56 | 35.49 | 35.48 | 35.61 |
| openssl loop | 59.35 | 59.34 | 59.17 | 59.38 |

Message length 1024:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 4.92 | 4.92 | 4.92 | 4.92 |
| ed25519-simd Dalek null-cache | 4.88 | 4.89 | 4.89 | 4.89 |
| solana-ed25519 Zip215 batch[^batch-api] | 14.84 | 13.84 | 13.38 | 13.17 |
| solana-ed25519 Dalek loop | 23.47 | 23.48 | 23.46 | 23.48 |
| ed25519-dalek batch[^batch-api] | 15.33 | 14.26 | 13.67 | 13.40 |
| ed25519-dalek loop | 21.25 | 21.23 | 21.21 | 21.22 |
| aws-lc-rs parsed loop | 23.73 | 23.72 | 23.73 | 23.72 |
| ring loop | 31.76 | 31.75 | 31.71 | 32.67 |
| sodiumoxide loop | 36.80 | 36.78 | 36.81 | 36.82 |
| openssl loop | 60.02 | 60.21 | 60.00 | 60.02 |

Mixed message lengths:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 4.79 | 4.75 | 4.75 | 4.72 |
| ed25519-simd Dalek null-cache | 4.74 | 4.70 | 4.71 | 4.68 |
| solana-ed25519 Zip215 batch[^batch-api] | 14.03 | 12.99 | 12.56 | 12.32 |
| solana-ed25519 Dalek loop | 22.57 | 22.55 | 22.59 | 22.63 |
| ed25519-dalek batch[^batch-api] | 14.39 | 13.40 | 12.84 | 12.60 |
| ed25519-dalek loop | 20.36 | 20.35 | 20.37 | 20.38 |
| aws-lc-rs parsed loop | 22.79 | 22.80 | 22.77 | 22.78 |
| ring loop | 30.80 | 30.79 | 30.75 | 31.73 |
| sodiumoxide loop | 35.68 | 35.66 | 35.71 | 35.77 |
| openssl loop | 59.52 | 59.28 | 59.56 | 59.56 |

[^batch-api]: The batch APIs for `solana-ed25519` and `ed25519-dalek` return a
    single pass/fail result for the whole batch. They do not identify exactly
    which signatures in the batch were invalid.

### Hot Key Repeats

To rerun only this crate's hot-key cases:

```sh
cd benches-compare
taskset -c 4 env \
  RUSTFLAGS="-C target-cpu=native -C target-feature=+avx512f,+avx512dq,+avx512ifma" \
  cargo bench --bench solana_ed25519_compare -- \
    'hot_keys/distinct_4/ed25519_simd' --noplot --discard-baseline
```

This scenario cycles through 4 distinct keys to fill each batch and reuses
the same `Verifier` across benchmark iterations, so `HotKeyCache` is warm
(all hits) after the first iteration. It quantifies the `HotKeyCache` win
referenced in [Key Caching](#key-caching) for a workload that actually
repeats a small key set:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 4.64 | 4.64 | 4.64 | 4.64 |
| ed25519-simd Zip215 hot-key cache (warm) | 4.22 | 4.22 | 4.22 | 4.22 |

## Compatibility Target

Compatibility with [`solana-ed25519`] is a design constraint, not just a
benchmark target. The benchmark compares throughput against `solana-ed25519`,
while the tests compare accept/reject decisions against the matching verifier
entry points.

[`solana-ed25519`]: https://crates.io/crates/solana-ed25519
