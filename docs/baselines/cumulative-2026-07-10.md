# Cumulative measurement — old main (`cbc0add`) vs new main (`a5d1cef`), 2026-07-10

**Hardware:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) ·
~3.78 GHz sustained (3.63 GHz sustained-AVX-512) · kernel 6.17.0-1017-aws ·
rustc 1.97.0 · `RUSTFLAGS="-C target-cpu=native"`

**Protocol:** single session, strictly sequential, **interleaved**
(old₁ → new₁ → old₂ → new₂; means of 2 runs per side) — the honest
Phase-0-lineage-vs-today numbers. Cross-day anchors had drifted ~1–3 %, which
this measurement supersedes. "Old main" = `cbc0add` (pre-1a); "new main" =
`a5d1cef` (1a + 1b + 2h + F1 + Phase 3; 1c/2f/F2 rejected by measurement;
2r spike inert). µs/signature: old \| new \| Δ%.

## Standard tables

| scenario | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| distinct_keys/msg_len_1 · zip215 (nocache) | 8.94 \| 8.49 \| -5.0% | 8.94 \| 8.48 \| -5.1% | 8.88 \| 8.50 \| -4.2% | 8.93 \| 8.50 \| -4.8% |
| distinct_keys/msg_len_1 · dalek (nocache) | 8.84 \| 8.44 \| -4.5% | 8.86 \| 8.42 \| -5.0% | 8.86 \| 8.45 \| -4.6% | 8.85 \| 8.45 \| -4.5% |
| distinct_keys/msg_len_1024 · zip215 (nocache) | 9.35 \| 8.86 \| -5.2% | 9.25 \| 8.87 \| -4.2% | 9.32 \| 8.86 \| -5.0% | 9.33 \| 8.86 \| -5.1% |
| distinct_keys/msg_len_1024 · dalek (nocache) | 9.27 \| 8.82 \| -4.8% | 9.28 \| 8.84 \| -4.8% | 9.24 \| 8.82 \| -4.5% | 9.29 \| 8.83 \| -5.0% |
| distinct_keys/msg_len_mixed · zip215 (nocache) | 9.18 \| 8.67 \| -5.5% | 9.04 \| 8.63 \| -4.5% | 9.09 \| 8.62 \| -5.2% | 8.97 \| 8.64 \| -3.7% |
| distinct_keys/msg_len_mixed · dalek (nocache) | 9.06 \| 8.63 \| -4.7% | 9.01 \| 8.56 \| -4.9% | 9.03 \| 8.59 \| -4.8% | 8.94 \| 8.57 \| -4.1% |
| garbage_sigs/invalid_25pct · zip215 (nocache) | 8.96 \| 8.53 \| -4.8% | 8.98 \| 8.48 \| -5.6% | 8.93 \| 8.49 \| -4.9% | 8.93 \| 8.47 \| -5.1% |
| garbage_sigs/invalid_50pct · zip215 (nocache) | 8.85 \| 8.47 \| -4.3% | 8.96 \| 8.46 \| -5.6% | 8.96 \| 8.48 \| -5.4% | 8.95 \| 8.47 \| -5.3% |
| hot_keys/distinct_4 · zip215 (hotcache) | 8.03 \| 5.52 \| -31.2% | 8.02 \| 5.53 \| -31.0% | 8.01 \| 5.52 \| -31.1% | 7.96 \| 5.52 \| -30.6% |
| hot_keys/distinct_4 · dalek (hotcache) | 7.90 \| 5.38 \| -31.9% | 7.92 \| 5.39 \| -31.9% | 7.85 \| 5.39 \| -31.4% | 7.87 \| 5.38 \| -31.6% |
| hot_keys/distinct_4 · zip215 (nullcache) | 8.98 \| 8.49 \| -5.4% | 8.91 \| 8.51 \| -4.5% | 8.99 \| 8.49 \| -5.6% | 8.96 \| 8.49 \| -5.3% |
| hot_keys/churn_cap4 · zip215 (hotcache) — *pre-fix, see below* | 9.16 \| 13.09 \| +42.8% | 9.19 \| 17.49 \| +90.3% | 9.17 \| 17.48 \| +90.6% | 9.21 \| 17.49 \| +89.9% |

| large-key sweep | n=256 | n=1024 |
|---|---|---|
| hot_keys/large_distinct · zip215 (hotcache) | 8.05 \| 6.16 \| -23.4% | 8.34 \| 9.28 \| +11.3% |
| hot_keys/large_distinct · zip215 (nullcache) | 8.90 \| 8.49 \| -4.6% | 8.96 \| 8.50 \| -5.2% |

## Headline

- **Cold / distinct keys (both policies, all msg lengths): −4.2…−5.6 %.**
- **Hot cached keys: −31 % both policies** (zip 8.0 → 5.52, dalek 7.9 → 5.38 µs/sig).
- Retention crossover ≈ 900 keys (hot wins −23 % at 256 resident; loses at 1024).

## ⚠ Finding: churn regression vs old main (pre-existing, quantified today)

`hot_keys/churn_cap4` (working set ≫ capacity, all-miss steady state):
old main 9.2 µs/sig → new main **13.1–17.5 µs/sig (+43…+90 %)**. This is NOT
from tonight's phases — the overnight churn gate held at 1b levels — it is
**Phase 1b's insert-time `normalized_affine`** (one ~5 µs field inversion per
miss-insert), unamortized when keys are evicted before reuse. The churn
scenario was only added tonight, so 1b's gate (hot-path win, nocache flat)
never saw it. NullKeyCache is unaffected (8.5 µs/sig on the same workload).

**RESOLVED same day (1b-fix, lazy normalization).** The 1b normalization moved
from insert into the 2h two-hit promotion pass; fresh inserts store the table
as decoded and churn inserts pay only the map insert. Re-measured against
`cbc0add`, same-session interleaved ×2 (`fix_old_*`/`fix_new_*` baselines):

| scenario (1b-fix vs old main) | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| hot_keys/churn_cap4 · zip215 (hotcache) | 9.18 \| 8.69 \| **−5.4%** | 9.24 \| 8.78 \| **−5.0%** | 9.22 \| 8.79 \| **−4.6%** | 9.24 \| 8.79 \| **−4.9%** |
| hot_keys/distinct_4 · zip215 (hotcache) | 8.00 \| 5.48 \| −31.5% | 8.02 \| 5.49 \| −31.5% | 7.96 \| 5.49 \| −31.0% | 7.98 \| 5.49 \| −31.2% |
| hot_keys/distinct_4 · dalek (hotcache) | 7.94 \| 5.39 \| −32.2% | 7.96 \| 5.39 \| −32.2% | 7.96 \| 5.40 \| −32.3% | 7.90 \| 5.39 \| −31.8% |

Churn is now *faster* than pre-1a (free inserts + the F1/Phase-3 cold-ladder
wins on the miss path); warm hot paths are unchanged within noise
(fix-vs-old matches main-vs-old); the 40-config nocache guard diverges from
main's deltas by +0.07 pp mean (flat). Large-sweep n=1024 also improved
(+11.3 % → +9.1 % vs old). HotKeyCache under churn is no longer harmful —
it simply doesn't help.
