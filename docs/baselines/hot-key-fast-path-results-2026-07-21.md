# Hot-key fast path (lazy promotion + [2¹²⁷]A split ladder) — results

Change under test: a key's second verification promotes its cache entry — the
verifier precomputes `A′ = [2¹²⁷]A` (one wide 127-doubling pass shared by all
promoting lanes of a chunk) and normalizes both of the key's tables to affine
(one batch inversion). Chunks whose eight lanes all carry promoted keys verify
with a four-scalar ~127-bit ladder over the plain integer splits
`k = k₀ + 2¹²⁷k₁`, `s = s₀ + 2¹²⁷s₁`, riding `A`, `A′`, `B`, `B′ = [2¹²⁷]B`:
**124 point doublings per signature instead of 252**, table additions unchanged
(96, all 7 M affine mixed-adds on the gated path). The identities
`[k]A = [k₀]A + [k₁]A′` and `[s]B = [s₀]B + [s₁]B′` are ℤ-module axioms — they
hold for every group element, torsion included — so the ladder computes the
identical group element and acceptance is bit-identical by construction for
both policies. Any chunk with a non-promoted lane takes the existing ladder
unchanged. `B′` is a second ~33 KB static basepoint table (`LazyLock`, built
once per process).

Promotion is lazy with a two-hit hysteresis: `A′` is built on a key's second
cache hit, never at insert, so single-use and churning keys never pay it. (A
promote-on-first-hit variant rebuilt tables in a loop under capacity churn,
+23.5 %; the hysteresis removes that failure mode.) From operation counts the
build is roughly half a signature per key, breaking even after ~2–3 fast
verifications.

## Measured

`benches/hot_profile` (added by this change) and `benches/cold_profile`:
crate-only lean binaries, `-C target-cpu=native`, one pinned core, base vs
branch interleaved same-session; ns/sig, vs the `#23` branch. Hot and Dalek
rows: min-of-4 session; cold Zip215 and churn rows: min-of-7 session.

| workload | AMD EPYC 9R45 (Zen 5) | Intel Xeon 6975P-C |
|---|---|---|
| hot, 4 keys | 4527 → 3296 (−27.2 %) | 7574 → 5371 (−29.1 %) |
| hot, 256 distinct resident | 4580 → 3378 (−26.3 %) | 7656 → 5490 (−28.3 %) |
| hot, 1024 distinct resident | 4591 → 3371 (−26.6 %) | – |
| cold, Zip215 (`NullKeyCache`) | 5101 → 5243 (+2.8 %) | 8558 → 8715 (+1.8 %) |
| cold, Dalek (`NullKeyCache`) | 5042 → 5121 (+1.6 %) | 8417 → 8542 (+1.5 %) |
| churn (cap-4, 512 distinct keys, all-miss) | 5220 → 5411 (+3.7 %) | 8763 → 8994 (+2.6 %) |

An earlier session measured the Zip215 cold gap at +1.6 % on both vendors; the
cold cost is +1.5–3 % depending on layout draw. With `NullKeyCache` none of the
new code executes, so the cold delta is code placement (the unrolled ladder
exceeds µop-cache capacity on both vendors), not added work.

Churn: subtracting the same session's cold gap leaves ≈ 0.9 pp of cache-specific
cost on both vendors, consistent with the doubled entry copied at insert
(~5.5 KB — every entry reserves both tables; promotion fills the second). Vs
`main` the same workload measures −0.4 % (Intel) / +2.4 % (Zen 5); `main`'s own
cache already loses 0.7–3 % under all-miss churn relative to cold.

## Cache sizing

At 1024 distinct resident promoted keys the lean harness still shows −26.6 %
(Zen 5). Earlier fat-harness (Criterion) sweeps on the Intel host found
retention degrading beyond ≈ 700–900 resident keys as tables spill L2.
Guidance unchanged: bound `HotKeyCache::with_capacity(...)` to the key set
that actually recurs — low hundreds — rather than the key universe.

Recorded null result (do not repeat): storing cache entries with the redundant
`z2` field dropped (3 fields instead of 4) was implemented, validated, and
measured at 4/256/1024 resident keys — all deltas inside noise. Verification is
compute-bound here (0.87 L2-misses/sig at baseline), so table bytes are not the
bottleneck; the 4-field layout stays, and the ~25 % table-memory cut remains
available if per-key footprint ever matters.

## Correctness

Golden tests: the promotion-built `A′` table base equals 127 independent
doublings of the decompressed key; every `B′` entry is pinned against an
independent projective reference; split recomposition `k₀ + 2¹²⁷k₁ = k` on
random and boundary scalars; split-vs-full ladder **point equality** (not just
accept-equivalence) on random and adversarial inputs including small-order and
torsioned `A`. The frozen differential acceptance suite against
`solana-ed25519` passes unchanged on both hosts, including warm-cache and
mixed-validity cases.
