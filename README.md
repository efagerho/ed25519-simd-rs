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
across batches to be worth retaining. The [Hot Key Repeats](#hot-key-repeats)
benchmark below quantifies both directions on this host: a genuinely hot key
set verifies ~35 % faster than `NullKeyCache` (5.5 vs 8.5 µs/signature),
while a churning key set (working set far beyond capacity, so entries are
evicted before reuse) **costs nothing**: all per-key table work is deferred
until a key has actually been seen again, so misses pay only the map insert
and land within a few percent of `NullKeyCache`. A mis-sized cache wastes
memory, not throughput.

How retention works (and how to size it):

- `HotKeyCache::with_capacity(...)` bounds the retained key set; pass it to
  `Verifier::with_cache(...)`. Successful key decodes are retained after
  verification, so reuse the same verifier across batches.
- **Two-hit promotion hysteresis.** A retained key is upgraded to the fast
  split-ladder form (an extra `[2^127]·A` table, built SIMD-batched) only on
  its **second cache hit**, never at insert. Single-use keys therefore pay
  almost nothing beyond the insert itself, and keys that oscillate between
  hit and eviction never trigger rebuild loops. The full win arrives from a
  key's second reuse onward.
- **Sizing guidance (this host; the crossover scales with L2).** Retention
  wins while the resident set stays small: −35 % at 4 hot keys, −23 % at 256
  fully-resident keys. It breaks even around **~900 resident keys** (promoted
  entries are ~5.4 KB each) and loses beyond that, where the retained tables
  thrash cache and fresh decode wins. `NullKeyCache` is flat
  (~8.5 µs/signature) at any key count. Bound the capacity to your genuinely
  recurring key set — in the low hundreds at most — rather than the total
  key universe.

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

The following numbers are Criterion medians in microseconds per signature for
distinct-key batches, measured 2026-07-10 on **AWS c8i.2xlarge (Intel Xeon
6975P-C, Granite Rapids), ~3.78 GHz sustained, kernel 6.17.0-1017-aws,
rustc 1.97.0, `RUSTFLAGS="-C target-cpu=native"`**. The `ed25519-simd` rows use
`NullKeyCache`, so decoded keys are not retained across batches.

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
| ed25519-simd Zip215 null-cache | 8.49 | 8.48 | 8.50 | 8.50 |
| ed25519-simd Dalek null-cache | 8.44 | 8.42 | 8.45 | 8.45 |
| solana-ed25519 Zip215 batch[^batch-api] | 17.78[^p0] | 16.36[^p0] | 15.64[^p0] | 15.28[^p0] |
| solana-ed25519 Dalek loop | 32.53[^p0] | 32.52[^p0] | 32.57[^p0] | 32.92[^p0] |
| ed25519-dalek batch[^batch-api] | 18.14[^p0] | 16.55[^p0] | 16.32[^p0] | 16.29[^p0] |
| ed25519-dalek loop | 26.82[^p0] | 26.77[^p0] | 26.81[^p0] | 27.29[^p0] |
| aws-lc-rs parsed loop | 31.05[^p0] | 31.01[^p0] | 31.05[^p0] | 31.02[^p0] |
| ring loop | 34.38[^p0] | 34.91[^p0] | 35.70[^p0] | 36.17[^p0] |
| sodiumoxide loop | 37.73[^p0] | 38.28[^p0] | 38.93[^p0] | 39.19[^p0] |
| openssl loop | 90.92[^p0] | 91.99[^p0] | 92.52[^p0] | 92.81[^p0] |

Message length 1024:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 8.86 | 8.87 | 8.86 | 8.86 |
| ed25519-simd Dalek null-cache | 8.82 | 8.84 | 8.82 | 8.83 |
| solana-ed25519 Zip215 batch[^batch-api] | 19.21[^p0] | 17.78[^p0] | 17.08[^p0] | 16.71[^p0] |
| solana-ed25519 Dalek loop | 34.00[^p0] | 34.00[^p0] | 34.04[^p0] | 34.38[^p0] |
| ed25519-dalek batch[^batch-api] | 19.60[^p0] | 18.04[^p0] | 17.77[^p0] | 17.73[^p0] |
| ed25519-dalek loop | 28.24[^p0] | 28.28[^p0] | 28.28[^p0] | 28.76[^p0] |
| aws-lc-rs parsed loop | 32.51[^p0] | 32.50[^p0] | 32.52[^p0] | 32.54[^p0] |
| ring loop | 35.83[^p0] | 36.47[^p0] | 37.14[^p0] | 37.49[^p0] |
| sodiumoxide loop | 39.37[^p0] | 39.98[^p0] | 40.67[^p0] | 40.88[^p0] |
| openssl loop | 92.66[^p0] | 93.29[^p0] | 93.73[^p0] | 93.48[^p0] |

Mixed message lengths:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 8.67 | 8.63 | 8.62 | 8.64 |
| ed25519-simd Dalek null-cache | 8.63 | 8.56 | 8.59 | 8.57 |
| solana-ed25519 Zip215 batch[^batch-api] | 18.01[^p0] | 16.60[^p0] | 15.87[^p0] | 15.49[^p0] |
| solana-ed25519 Dalek loop | 32.71[^p0] | 32.71[^p0] | 32.85[^p0] | 33.20[^p0] |
| ed25519-dalek batch[^batch-api] | 18.32[^p0] | 16.84[^p0] | 16.59[^p0] | 16.50[^p0] |
| ed25519-dalek loop | 26.99[^p0] | 26.99[^p0] | 27.02[^p0] | 27.57[^p0] |
| aws-lc-rs parsed loop | 31.31[^p0] | 31.26[^p0] | 31.26[^p0] | 31.27[^p0] |
| ring loop | 34.51[^p0] | 35.19[^p0] | 35.93[^p0] | 36.44[^p0] |
| sodiumoxide loop | 37.89[^p0] | 38.56[^p0] | 39.18[^p0] | 39.40[^p0] |
| openssl loop | 91.57[^p0] | 92.21[^p0] | 92.19[^p0] | 92.37[^p0] |

[^batch-api]: The batch APIs for `solana-ed25519` and `ed25519-dalek` return a
    single pass/fail result for the whole batch. They do not identify exactly
    which signatures in the batch were invalid.

[^p0]: Third-party rows were measured once on this host (2026-07-09 session,
    identical build flags) and are not re-run per crate change; the
    `ed25519-simd` rows are from the 2026-07-10 session. Cross-session drift
    on this host is ~1–3 %, immaterial at these ratios.

### Hot Key Repeats

Same command, filtered to the `hot_keys` group:

```sh
cd benches-compare
RUSTFLAGS="-C target-cpu=native -C target-feature=+avx512f,+avx512dq,+avx512ifma" \
  cargo bench --bench solana_ed25519_compare -- hot_keys
```

This scenario cycles through 4 distinct keys to fill each batch and reuses
the same `Verifier` across benchmark iterations, so `HotKeyCache` is warm
after the first iterations (entries are promoted to the split-ladder form on
their second hit; see [Key Caching](#key-caching)). The churn row is the
adversarial opposite: every batch is distinct keys with `capacity(4)`, so the
steady state is all-miss:

| Backend | 8 | 16 | 32 | 64 |
|---|---:|---:|---:|---:|
| ed25519-simd Zip215 null-cache | 8.49 | 8.51 | 8.49 | 8.49 |
| ed25519-simd Zip215 hot-key cache (warm) | 5.52 | 5.53 | 5.52 | 5.52 |
| ed25519-simd Dalek hot-key cache (warm) | 5.38 | 5.39 | 5.39 | 5.38 |
| ed25519-simd Zip215 hot-key cache (churn, capacity 4, all-miss) | 8.69 | 8.78 | 8.79 | 8.79 |

## Compatibility Target

Compatibility with [`solana-ed25519`] is a design constraint, not just a
benchmark target. The benchmark compares throughput against `solana-ed25519`,
while the tests compare accept/reject decisions against the matching verifier
entry points.

[`solana-ed25519`]: https://crates.io/crates/solana-ed25519
