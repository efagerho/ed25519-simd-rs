# Overnight report — 2026-07-09/10

**Hardware:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) ·
~3.78 GHz sustained (3.63 GHz sustained-AVX-512) · kernel 6.17.0-1017-aws ·
rustc 1.97.0 · `RUSTFLAGS="-C target-cpu=native"`

**main untouched tonight.** Everything below lives on `overnight` and its
phase branches. Full frozen suite (all 7 suites) **green on the final tip**
(`a883ba5`); I1 held at every commit — no fixture was touched all night.

## Per-phase verdicts

| phase | result | Δ (judge) | commit / branch | disposition |
|---|---|---|---|---|
| 2h cached-key scalar split | **PASS** (round 2, after hysteresis fix) | hot **−26.6 % zip / −27.2 % dalek**; churn +0.9 % (=drift); guard flat | `2c446f0` | **MERGED** |
| 2f ×19 carry-fold | FAIL (no consistent win) | mean **+0.20 %**, 23/60 wins | `phase-2f-mul19` | **PARKED · NEEDS-REVIEW** |
| F1 loose interior doublings | **PASS** (4-run tie-break on two n=8 stragglers) | mean **−1.06 %**, 60/60 on extended means | `b783dc0` | **MERGED** (tie-break flagged) |
| Phase 3 radix-4096 fold | **PASS** (cold+hot non-regressing, win > noise) | cold **−1.8 % median** (min −2.7 %); hot noise-flat; cold_profile 8652 ns/sig | `bd78d56` | **MERGED** |
| F2 vpgatherqq transpose | FAIL (uniform regression) | **+1.51 %**, 0/60 wins | `phase-f2-gather-transpose` | **PARKED · null recorded** |
| F3 add carry pass | not attempted | — | — | **SKIPPED** (audit: sub-0.1 %, time) |
| 2r hEEA_approx_q spike | gate NOT met | **4,440 cycles/sig** vs ≤2,500 gate; obligations 1–3 all pass | `a883ba5` (inert module, no wiring) | measured; **revival not recommended at tonight's cost** |

Flags for morning review: (i) 2h's promotion policy deviates from the review's
literal "first reuse" — hysteresis (2nd hit) was required to make churn = 1b
(measured +23.5 % without it; both rounds recorded); (ii) F1's 4-run tie-break
extends the "both runs" protocol; (iii) commit `301025a` accidentally swept a
temporary src reversion (staged by a bench checkout) — forward-fixed in
`7dea998`, no net change; noted since the fetch loop may have harvested it.

## Cumulative snapshot — Phase 0 baseline vs overnight tip (µs/signature: Phase 0 \| tip \| Δ%)

Caveat: endpoints are different sessions weeks of wall-clock apart in machine
state (ambient drift ±1 % observed tonight); per-phase tables in each
phase report are the controlled comparisons.

| scenario | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| distinct_keys/msg_len_1 · zip215 (nocache) | 8.87 \| 8.62 \| -2.8% | 8.79 \| 8.62 \| -2.0% | 8.86 \| 8.60 \| -3.0% | 8.84 \| 8.58 \| -2.9% |
| distinct_keys/msg_len_1 · dalek (nocache) | 8.75 \| 8.50 \| -2.8% | 8.75 \| 8.50 \| -2.9% | 8.81 \| 8.50 \| -3.6% | 8.82 \| 8.51 \| -3.6% |
| distinct_keys/msg_len_1024 · zip215 (nocache) | 9.24 \| 8.95 \| -3.1% | 9.21 \| 9.00 \| -2.3% | 9.22 \| 8.96 \| -2.8% | 9.21 \| 8.99 \| -2.3% |
| distinct_keys/msg_len_mixed · zip215 (nocache) | 9.01 \| 8.80 \| -2.4% | 8.98 \| 8.69 \| -3.3% | 8.97 \| 8.71 \| -2.9% | 8.95 \| 8.72 \| -2.5% |
| hot_keys/distinct_4 · zip215 (hotcache) | 7.92 \| 5.55 \| -29.9% | 8.02 \| 5.57 \| -30.6% | 8.02 \| 5.53 \| -31.0% | 8.01 \| 5.54 \| -30.9% |
| hot_keys/distinct_4 · zip215 (nullcache) | 8.98 \| 8.58 \| -4.5% | 8.98 \| 8.59 \| -4.4% | 8.96 \| 8.59 \| -4.2% | 8.97 \| 8.57 \| -4.4% |

Scenarios added tonight (no Phase 0 column; overnight-tip values, µs/sig):

| scenario | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| hot_keys/distinct_4 · dalek (hotcache) | 5.47 | 5.48 | 5.47 | 5.47 |
| hot_keys/churn_cap4 · zip215 (hotcache) | 13.17 | 17.60 | 17.62 | 17.59 |

| large-key sweep (µs/sig, overnight tip) | n=256 | n=1024 |
|---|---|---|
| hotcache zip215 | 6.20 | 9.30 |
| nullcache zip215 | 8.59 | 8.56 |

## Retention crossover (updated tonight)

Promoted entries are ≈ 2× (~5.4 KB/key). Measured: 256 keys — hotcache 6.20
vs nullcache 8.90 µs/sig (retention wins −30 %); 1024 keys — 9.39 vs 8.88
(loses). **Crossover ≈ 900 keys** (was ≈ 700 pre-2h): the split ladder makes
retained keys cheaper, extending the win region despite doubled entries.
README guidance: bound the cache to the recurring key set; crossover scales
with L2.

## Parked list (code + full reports on their branches)

- `phase-2f-mul19` — ×19 carry-fold: bit-identical, tested, measured null/
  slight regression on GNR (`docs/baselines/phase-2f.md`).
- `phase-f2-gather-transpose` — gather transpose: uniform +1.5 % regression
  (`docs/baselines/phase-f2.md`).

## Net effect of the night

Hot (cached, repeating keys): **≈ −30 % vs Phase 0** (7.9–8.0 → 5.5 µs/sig,
both policies). Cold (distinct keys): **≈ −2.3…−3.6 % tonight** on top of the
1a/1b gains already on main (cumulative vs Phase 0: cold ≈ −3 %, plus the
hot-path transformation). All merged work is acceptance-frozen (I1),
deterministic (I2), and carries goldens + per-phase before/after ×2 tables.
