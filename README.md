# ed25519-simd

`ed25519-simd` is a verification-only Ed25519 crate focused on high-throughput
batch verification. It verifies signatures and reports the result for each input
lane; it does not provide signing APIs or handle private key material.

The implementation is designed to be acceptance-compatible with the
`solana-ed25519` crate from `anza-xyz/cryptography`. The tests include
differential checks against the Anza verifier for both supported verification
policies and for edge cases such as small-order points, non-canonical encodings,
and scalar-boundary signatures.

## Requirements

**This crate requires `x86_64` with AVX-512 (F, DQ, IFMA) and has no scalar
fallback.** All verification — including single-signature checks and the tails of
non-multiple-of-eight batches — runs through the 8-wide AVX-512 IFMA path. The
crate fails at compile time unless the required target features are enabled.
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
instruction (`SIGILL`). As a guard, `Verifier` construction performs a one-time
runtime feature check and panics with a clear message rather than faulting in the
hot path. Build on the deployment host (or with an explicit
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
  check and accepts non-canonical point encodings according to the Anza
  `verify_zebra` / batch verifier behavior.
- `VerifyPolicy::Dalek` performs a stricter Dalek-style canonical-`R` check and
  applies Anza's legacy excluded-encoding filters.

Both policies reject non-canonical `S` scalars (`S >= L`).

## Batch Verification

All verification goes through a `Verifier`, which is constructed once and reused.
It holds the precomputed base-point table and a pluggable, statically-selected
key cache, so construction is not free — build it once and call `verify_batch`
repeatedly:

```rust
use ed25519_simd::{Verifier, VerifyInput, VerifyPolicy};

let mut verifier = Verifier::with_policy(VerifyPolicy::Zip215);
verifier.preload_public_keys(&hot_keys);

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
variable-base multiplication table. The default verifier uses `LruKeyCache` to
retain that per-key state across batches:

- `Verifier::new()` / `Verifier::with_policy(...)` use `LruKeyCache`.
- `preload_public_keys(...)` decodes and pins known hot keys.
- `with_policy_and_cache_capacity(...)` bounds the retained key set.
- `verifier.cache()` returns `&LruKeyCache`, which exposes optional cache
  stats and hot-key reporting.

Cold workloads can choose `NullKeyCache`, which retains no decoded keys and
exposes no cache reports. The verifier keeps any per-chunk decoded tables in
local scratch while a chunk is being verified:

```rust
use ed25519_simd::{NullKeyCache, Verifier, VerifyPolicy};

let verifier = Verifier::with_cache(VerifyPolicy::Zip215, NullKeyCache::new());
```

## SIMD Path

The crate batches eight signatures per AVX-512 IFMA chunk. There is no scalar
fallback: single verifications and ragged batch tails are processed as padded
SIMD chunks, and required target features are enforced by the root compile-time
gate (see [Requirements](#requirements)).

## Compatibility Target

Compatibility with the Solana/Anza cryptography implementation is a design
constraint, not just a benchmark target. The benchmark compares throughput
against `anza-xyz/cryptography`, while the tests compare accept/reject decisions
against the matching Anza verifier entry points.
