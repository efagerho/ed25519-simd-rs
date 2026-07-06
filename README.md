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
feature check and panics with a clear message instead of faulting in this
crate's hot path.

This guard reduces, but cannot eliminate, the risk of a raw `SIGILL`: the
`-C target-feature`/`-C target-cpu=native` flags that enable AVX-512 apply to
the entire binary, not just this crate, so the compiler is free to use AVX-512
instructions in any code built with those flags — including the standard
library's generic/monomorphized code (formatting, collections, panic/backtrace
machinery, etc.) — whether or not it ever calls into `ed25519-simd`. Code that
runs before a `Verifier` is constructed, or unrelated code elsewhere in the
same binary, is not covered by this check. The guard's real value is catching
the common case (a `Verifier` built and used near the start of a program, per
the usage pattern above) with a clear message rather than a bare `SIGILL`; it
is not a substitute for building on the deployment host (or with an explicit
`-C target-feature=+avx512f,+avx512dq,+avx512ifma` matching the deployment
CPU).

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

- `HotKeyCache::with_capacity(...)` bounds the evictable retained key set;
  pass it to `Verifier::with_cache(...)`.
- `verifier.cache_mut().preload(...)` decodes and pins known hot keys; pinned
  keys are retained outside the capacity bound and are not evicted. It
  returns the keys that failed to decode instead of silently dropping them.
- `verifier.cache_mut().unpin(...)` releases a pin (e.g. keys from a rotated-out
  validator set) so they become ordinary evictable entries again; pinning has
  no automatic expiry, so a workload that repeatedly preloads a changing key
  set should unpin the keys it no longer needs.
- `verifier.cache()` returns `&HotKeyCache`, which exposes optional cache
  stats and hot-key reporting.

The verifier keeps any per-chunk decoded tables in local scratch while a chunk
is being verified, even with `NullKeyCache`:

```rust,no_run
use ed25519_simd::{HotKeyCache, Verifier, VerifyPolicy};
# let hot_keys: Vec<[u8; 32]> = Vec::new();

let mut verifier = Verifier::with_cache(VerifyPolicy::Zip215, HotKeyCache::new());
let rejected = verifier.cache_mut().preload(&hot_keys);
assert!(rejected.is_empty(), "some hot keys failed to decode: {rejected:?}");
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

Command. The comparison bench lives in the `benches-compare` workspace member
(it depends on several other Ed25519/crypto libraries purely for comparison,
kept out of the main crate's dependency tree so `cargo test` doesn't build
them), so it's run from there rather than the crate root:

```sh
cd benches-compare
RUSTFLAGS="-C target-cpu=native -C target-feature=+avx512f,+avx512dq,+avx512ifma" \
  cargo bench --bench solana_ed25519_compare -- distinct_keys
```

Message length 1:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 5.18 | 5.16 | 5.16 | 5.16 |
| ed25519-simd Dalek null-cache | 5.14 | 5.14 | 5.14 | 5.14 |
| solana-ed25519 Zip215 batch[^batch-api] | 14.05 | 13.03 | 12.58 | 12.33 |
| solana-ed25519 Dalek loop | 22.40 | 22.40 | 22.41 | 22.41 |
| ed25519-dalek batch[^batch-api] | 14.35 | 13.24 | 12.73 | 12.47 |
| ed25519-dalek loop | 20.22 | 20.15 | 20.19 | 20.19 |
| aws-lc-rs parsed loop | 22.56 | 22.60 | 22.57 | 22.60 |
| ring loop | 30.63 | 30.53 | 30.54 | 31.71 |
| sodiumoxide loop | 35.60 | 35.46 | 35.49 | 35.62 |
| openssl loop | 59.14 | 58.77 | 59.31 | 59.24 |

Message length 1024:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 5.46 | 5.46 | 5.46 | 5.48 |
| ed25519-simd Dalek null-cache | 5.40 | 5.42 | 5.42 | 5.40 |
| solana-ed25519 Zip215 batch[^batch-api] | 15.01 | 14.04 | 13.59 | 13.32 |
| solana-ed25519 Dalek loop | 23.52 | 23.52 | 23.41 | 23.45 |
| ed25519-dalek batch[^batch-api] | 15.41 | 14.30 | 13.70 | 13.46 |
| ed25519-dalek loop | 21.18 | 21.22 | 21.19 | 21.20 |
| aws-lc-rs parsed loop | 23.70 | 23.71 | 23.78 | 23.68 |
| ring loop | 31.68 | 31.66 | 31.78 | 32.60 |
| sodiumoxide loop | 36.77 | 36.77 | 36.79 | 36.81 |
| openssl loop | 59.80 | 60.35 | 59.65 | 59.76 |

Mixed message lengths:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 5.31 | 5.25 | 5.26 | 5.23 |
| ed25519-simd Dalek null-cache | 5.25 | 5.21 | 5.21 | 5.19 |
| solana-ed25519 Zip215 batch[^batch-api] | 14.25 | 13.16 | 12.72 | 12.49 |
| solana-ed25519 Dalek loop | 22.54 | 22.51 | 22.60 | 22.64 |
| ed25519-dalek batch[^batch-api] | 14.46 | 13.44 | 12.93 | 12.63 |
| ed25519-dalek loop | 20.33 | 20.32 | 20.36 | 20.34 |
| aws-lc-rs parsed loop | 22.74 | 22.86 | 22.85 | 22.83 |
| ring loop | 30.77 | 30.85 | 30.84 | 31.67 |
| sodiumoxide loop | 35.73 | 35.78 | 35.75 | 35.80 |
| openssl loop | 59.27 | 59.90 | 59.17 | 59.65 |

[^batch-api]: The batch APIs for `solana-ed25519` and `ed25519-dalek` return a
    single pass/fail result for the whole batch. They do not identify exactly
    which signatures in the batch were invalid.

### Hot Key Repeats

Same command, filtered to the `hot_keys` group:

```sh
cd benches-compare
RUSTFLAGS="-C target-cpu=native -C target-feature=+avx512f,+avx512dq,+avx512ifma" \
  cargo bench --bench solana_ed25519_compare -- hot_keys
```

This scenario cycles through 4 distinct keys to fill each batch and reuses
the same `Verifier` across benchmark iterations, so `HotKeyCache` is warm
(all hits) after the first iteration. It quantifies the `HotKeyCache` win
referenced in [Key Caching](#key-caching) for a workload that actually
repeats a small key set:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 5.19 | 5.20 | 5.19 | 5.20 |
| ed25519-simd Zip215 hot-key cache (warm) | 4.72 | 4.72 | 4.72 | 4.72 |

## Compatibility Target

Compatibility with [`solana-ed25519`] is a design constraint, not just a
benchmark target. The benchmark compares throughput against `solana-ed25519`,
while the tests compare accept/reject decisions against the matching verifier
entry points.

[`solana-ed25519`]: https://crates.io/crates/solana-ed25519
