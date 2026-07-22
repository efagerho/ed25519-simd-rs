# Hot-key fast path (lazy promotion + [2¹²⁷]A split ladder) — results

Change under test: a key's second verification promotes its cache entry — the
verifier precomputes `A′ = [2¹²⁷]A` (one wide 127-doubling pass shared by all
promoting lanes of a chunk) and normalises both of the key's tables to affine. 
Chunks whose eight lanes all carry promoted keys verify with a four-scalar 
~127-bit ladder over the split integers
`k = k₀ + 2¹²⁷k₁`, `s = s₀ + 2¹²⁷s₁`, riding `A`, `A′`, `B`, `B′ = [2¹²⁷]B`:
**124 point doublings per signature instead of 252**, table additions 
unchanged. The acceptance is bit-identical by construction for both policies. 
Any chunk with a non-promoted lane takes the existing ladder unchanged. 
`B′` is a second ~33 KB static basepoint table.

Promotion is lazy: `A′` is built on a key's second cache hit, so single-use 
and churning keys never pay it. The cache build is roughly half a signature
per key, breaking even after ~2–3 fast verifications.

## Measured

`benches/hot_profile` (added by this change) and `benches/cold_profile`:
crate-only lean binaries, `-C target-cpu=native`, one pinned core in ns/sig, 
compared against the `#23` branch.

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

At 1024 key cache size, the lean harness still shows −26.6 % (Zen 5). 
Retained tables cost ~5.5 KB per key, so a large resident set
eventually outgrows L2 and lookups slow down: in the Criterion comparison
bench on the Intel host, the benefit of retention degraded once the resident
set passed ≈ 700–900 keys. Set `HotKeyCache::with_capacity(...)` to the
number of keys that actually recur in the workload.

Note: I did tests with cache entries without the redundant `z2` field, which
lowers size from 4 field elements to 3. Measured at 4/256/1024 resident keys
without notable improvements - observed 0.87 L2-misses/sig at baselin, so 
table size is not the bottleneck.

## Correctness

New tests are added. The `A′` table built at promotion is checked
against 127 independent doublings of the key point, and every `B′` entry
against an independently computed reference. The split `k₀ + 2¹²⁷k₁ = k` is
verified on random and boundary scalars. The split ladder must produce the
same point as the full ladder on random and adversarial inputs, including 
small-order and torsioned `A`. On top of that, the frozen differential 
acceptance suite against `solana-ed25519` passes unchanged on both hosts, 
including warm-cache and mixed-validity cases.
