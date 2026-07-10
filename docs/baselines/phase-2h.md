# Hot-key fast path (split ladder + lazy promotion) — before/after (2026-07-09)

**Hardware/build:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) · ~3.78 GHz sustained · kernel 6.17.0-1017-aws · rustc 1.97.0 · `RUSTFLAGS="-C target-cpu=native"`

Criterion medians in µs per signature (before \| after \| Δ%), mean of two
runs per side. Change under test: chunks whose eight lanes are all promoted
cache hits run a halved-doubling ladder over exact integer scalar splits
(`k = k₀ + 2¹²⁷k₁`, `s = s₀ + 2¹²⁷s₁`) against per-key `A′ = [2¹²⁷]A` tables
— 124 doublings instead of 252, identical group element, both policies.

Promotion is lazy with a two-hit hysteresis: a key's `A′` table is built (one
SIMD pass shared by all promoting lanes of a chunk) only on its second cache
hit. A promote-on-first-hit variant was measured first and rebuilt tables in
a loop when keys oscillated between hit and eviction (+23.5 % on the
capacity-churn bench at n=8); the hysteresis removes that entirely — churn
lands at +0.9 %, indistinguishable from ambient drift, because keys evicted
before their second hit never pay for promotion.

### Judge — hot workloads (µs/signature: before \| after \| Δ%)

| scenario | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| hot_keys/distinct_4 · zip215 (hotcache) | 7.63 \| 5.57 \| -27.0% | 7.59 \| 5.56 \| -26.7% | 7.61 \| 5.58 \| -26.8% | 7.50 \| 5.57 \| -25.7% |
| hot_keys/distinct_4 · dalek (hotcache) | 7.56 \| 5.47 \| -27.6% | 7.55 \| 5.48 \| -27.5% | 7.51 \| 5.48 \| -27.0% | 7.50 \| 5.48 \| -26.9% |
| hot_keys/distinct_4 · zip215 (nullcache side-guard) | 8.75 \| 8.87 \| +1.3% | 8.72 \| 8.85 \| +1.6% | 8.74 \| 8.84 \| +1.1% | 8.71 \| 8.85 \| +1.5% |
| hot_keys/churn_cap4 · zip215 (hotcache, all-miss) | 13.33 \| 13.46 \| +0.9% | 17.73 \| 17.85 \| +0.7% | 17.72 \| 17.90 \| +1.0% | 17.72 \| 17.89 \| +1.0% |

### Large-key sweep (µs/signature: before \| after \| Δ%)

| scenario | n=256 | n=1024 |
|---|---|---|
| hot_keys/large_distinct · zip215 (hotcache) | 7.77 \| 6.20 \| -20.3% | 9.21 \| 9.39 \| +2.0% |
| hot_keys/large_distinct · zip215 (nullcache) | 8.71 \| 8.90 \| +2.2% | 8.72 \| 8.88 \| +1.8% |

### Guard — cold/NullKeyCache flatness (µs/signature: before \| after \| Δ%)

| scenario | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| distinct_keys/msg_len_1 · zip215 | 8.84 \| 8.87 \| +0.3% | 8.84 \| 8.87 \| +0.3% | 8.77 \| 8.86 \| +1.0% | 8.78 \| 8.86 \| +1.0% |
| distinct_keys/msg_len_1 · dalek | 8.68 \| 8.83 \| +1.7% | 8.70 \| 8.85 \| +1.8% | 8.67 \| 8.81 \| +1.6% | 8.70 \| 8.84 \| +1.6% |
| distinct_keys/msg_len_1024 · zip215 | 9.21 \| 9.21 \| +0.1% | 9.19 \| 9.18 \| -0.2% | 9.19 \| 9.22 \| +0.3% | 9.21 \| 9.18 \| -0.3% |
| distinct_keys/msg_len_1024 · dalek | 9.05 \| 9.20 \| +1.7% | 9.04 \| 9.19 \| +1.7% | 9.04 \| 9.21 \| +1.9% | 9.07 \| 9.21 \| +1.5% |
| distinct_keys/msg_len_mixed · zip215 | 9.03 \| 9.02 \| -0.1% | 8.94 \| 9.00 \| +0.7% | 8.99 \| 8.99 \| -0.0% | 8.90 \| 8.89 \| -0.1% |
| distinct_keys/msg_len_mixed · dalek | 8.90 \| 8.98 \| +0.9% | 8.83 \| 8.96 \| +1.4% | 8.83 \| 8.92 \| +1.0% | 8.79 \| 8.92 \| +1.5% |

Both policies improve together (zip215 −26.6 %, dalek −27.2 % mean) — the
split ladder computes the identical group element, so the acceptance suites
are unaffected. Retention crossover re-measured with promoted (~2×, ≈5.4 KB)
entries: hot improves −20 % at 256 resident keys, regresses at 1024; crossover ≈ 900
keys, *extended* from ≈ 700 because retained keys are now cheaper to verify.
