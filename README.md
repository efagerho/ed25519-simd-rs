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

Doc tests compile through `rustdoc`, so pass the same CPU target there too:

```sh
RUSTFLAGS="-C target-cpu=native" RUSTDOCFLAGS="-C target-cpu=native" cargo test --doc
```

AVX-512 IFMA is available on Intel Ice Lake and later, and on AMD Zen 4 and later.

Because the SIMD path is selected at compile time (there is no runtime feature
gate on the hot path), **a binary built with `-C target-cpu=native` must run on
the same CPU it was built for, or one that is at least as capable.** Running it on
a CPU that lacks the required features would otherwise fault with an illegal
instruction (`SIGILL`). As a guard, `Verifier` construction performs a runtime
feature check and panics with a clear message rather than faulting in the hot
path. Build on the deployment host (or with an explicit
`-C target-feature=+avx512f,+avx512dq,+avx512ifma` matching the deployment CPU).

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

```rust
use ed25519_simd::{Verifier, VerifyInput, VerifyPolicy};

let mut verifier = Verifier::with_policy(VerifyPolicy::Zip215);

let inputs = [VerifyInput {
    public_key,
    signature,
    message,
}];

let mut out = vec![false; inputs.len()];
verifier.verify_batch(&inputs, &mut out);
assert!(out[0]);
```

Each output entry corresponds to the input at the same index, so callers can see
which signatures passed or failed.

## Key Caching

Verification repeatedly needs a decoded public key and a precomputed
variable-base multiplication table. `Verifier::new()` and
`Verifier::with_policy(...)` use `NullKeyCache`, so decoded keys are not retained
across batches by default. This keeps cold or mostly-distinct workloads from
paying for cache bookkeeping they do not use.

Use `LruKeyCache` when a workload has a hot key set worth retaining:

- `with_cache_capacity(...)` bounds the retained key set.
- `preload_public_keys(...)` decodes and pins known hot keys.
- `verifier.cache()` returns `&LruKeyCache`, which exposes optional cache
  stats and hot-key reporting.

Applications that already manage their own small hot set can provide a custom
`KeyCache` to `Verifier::with_cache(...)`; the cache stores `CachedPublicKey`
values, so misses decoded by the verifier can be retained without re-decoding.

The verifier keeps any per-chunk decoded tables in local scratch while a chunk
is being verified, even with `NullKeyCache`:

```rust
use ed25519_simd::{LruKeyCache, Verifier, VerifyPolicy};

let mut verifier = Verifier::with_cache(VerifyPolicy::Zip215, LruKeyCache::new());
verifier.preload_public_keys(&hot_keys);
```

## SIMD Path

The crate batches eight signatures per AVX-512 IFMA chunk. There is no scalar
fallback: single verifications and ragged batch tails are processed as padded
SIMD chunks, and required target features are enforced by the root compile-time
gate (see [Requirements](#requirements)).

## Benchmark Snapshot

The following numbers are Criterion medians in microseconds per signature for
distinct-key batches. The `ed25519-simd` rows use `NullKeyCache`, so decoded keys
are not retained across batches.

Command:

```sh
RUSTFLAGS="-C target-cpu=native -C target-feature=+avx512f,+avx512dq,+avx512ifma" \
  cargo bench --bench solana_ed25519_compare -- distinct_keys \
  --sample-size 20 --warm-up-time 0.2 --measurement-time 0.5
```

Message length 1:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 5.59 | 5.63 | 5.61 | 5.64 |
| ed25519-simd Dalek null-cache | 5.53 | 5.60 | 5.60 | 5.55 |
| solana-ed25519 Zip215 batch[^batch-api] | 14.02 | 13.01 | 12.47 | 12.24 |
| solana-ed25519 Dalek loop | 22.47 | 22.49 | 22.38 | 22.39 |
| ed25519-dalek batch[^batch-api] | 11.54 | 10.46 | 9.92 | 9.68 |
| ed25519-dalek loop | 17.51 | 17.42 | 17.40 | 17.45 |
| aws-lc-rs parsed loop | 22.55 | 22.56 | 22.55 | 22.55 |
| ring loop | 30.64 | 30.56 | 30.55 | 31.69 |
| sodiumoxide loop | 35.60 | 35.53 | 35.52 | 35.58 |
| openssl loop | 58.72 | 58.46 | 58.27 | 59.11 |

Message length 1024:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 5.94 | 5.97 | 5.96 | 5.96 |
| ed25519-simd Dalek null-cache | 5.91 | 5.90 | 5.88 | 5.93 |
| solana-ed25519 Zip215 batch[^batch-api] | 14.91 | 13.98 | 13.47 | 13.33 |
| solana-ed25519 Dalek loop | 23.45 | 23.45 | 23.42 | 23.50 |
| ed25519-dalek batch[^batch-api] | 12.56 | 11.50 | 10.92 | 10.63 |
| ed25519-dalek loop | 18.44 | 18.44 | 18.41 | 18.41 |
| aws-lc-rs parsed loop | 23.66 | 23.78 | 23.66 | 23.65 |
| ring loop | 31.70 | 31.72 | 31.67 | 32.85 |
| sodiumoxide loop | 36.74 | 36.99 | 36.79 | 36.88 |
| openssl loop | 59.41 | 59.00 | 59.25 | 59.34 |

Mixed message lengths:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 5.74 | 5.67 | 5.70 | 5.69 |
| ed25519-simd Dalek null-cache | 5.69 | 5.65 | 5.68 | 5.62 |
| solana-ed25519 Zip215 batch[^batch-api] | 14.09 | 13.09 | 12.64 | 12.48 |
| solana-ed25519 Dalek loop | 22.65 | 22.55 | 22.67 | 22.58 |
| ed25519-dalek batch[^batch-api] | 11.63 | 10.64 | 10.14 | 9.82 |
| ed25519-dalek loop | 17.56 | 17.55 | 17.59 | 17.59 |
| aws-lc-rs parsed loop | 22.70 | 22.74 | 22.85 | 22.73 |
| ring loop | 30.68 | 30.76 | 30.94 | 31.88 |
| sodiumoxide loop | 35.71 | 35.72 | 35.88 | 35.82 |
| openssl loop | 59.09 | 58.54 | 58.67 | 58.93 |

[^batch-api]: The batch APIs for `solana-ed25519` and `ed25519-dalek` return a
    single pass/fail result for the whole batch. They do not identify exactly
    which signatures in the batch were invalid.

## Compatibility Target

Compatibility with [`solana-ed25519`] is a design constraint, not just a
benchmark target. The benchmark compares throughput against `solana-ed25519`,
while the tests compare accept/reject decisions against the matching verifier
entry points.

[`solana-ed25519`]: https://crates.io/crates/solana-ed25519
