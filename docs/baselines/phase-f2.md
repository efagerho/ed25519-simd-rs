# Phase F2 — vpgatherqq table transpose: NULL RESULT (regression), reverted

**Hardware:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) ·
~3.78 GHz sustained · kernel 6.17.0-1017-aws · rustc 1.97.0 ·
`RUSTFLAGS="-C target-cpu=native"`

Experiment (audit F2): replace `WideFe::from_field_refs`'s ~40-scalar-store +
5-load transpose with five `vpgatherqq` (lane pointers as scale-1 offsets).
Hypothesis from 1a's overshoot: the transpose is a first-order cost.

## Gate verdict: FAIL — consistent regression, reverted

Before = overnight tip (2h+F1+P3, `after_p3` baselines); after = F2; 60 configs,
mean of 2 runs:

- mean **+1.51 %**, median +1.57 %, range +0.19 % … **+2.59 %**
- wins: **0/60** (run1 1/60, run2 1/60) — uniformly slower

`vpgatherqq` is decisively worse than the store-forward transpose on Granite
Rapids (gather µop cost dominates; the 1a effect was footprint, not transpose
dispatch). Audit F2 should be closed with this measured null — the hypothesis
is falsified on this µarch, symmetric with 2f's null. Correctness was fine
(frozen suite green); this is purely a performance revert.

Kept on branch `phase-f2-gather-transpose` (code + this report); `overnight`
continues without it.

## README-style snapshot (µs/signature: before \| after \| Δ%)

| scenario | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| distinct_keys/msg_len_1 · zip215 (nocache) | 8.62 \| 8.73 \| +1.3% | 8.62 \| 8.73 \| +1.3% | 8.60 \| 8.73 \| +1.5% | 8.58 \| 8.74 \| +1.8% |
| distinct_keys/msg_len_1024 · zip215 (nocache) | 8.95 \| 9.10 \| +1.7% | 9.00 \| 9.11 \| +1.2% | 8.96 \| 9.12 \| +1.8% | 8.99 \| 9.09 \| +1.1% |
| distinct_keys/msg_len_mixed · zip215 (nocache) | 8.80 \| 8.92 \| +1.4% | 8.69 \| 8.84 \| +1.7% | 8.71 \| 8.87 \| +1.8% | 8.72 \| 8.83 \| +1.2% |
| hot_keys/distinct_4 · zip215 (hotcache) | 5.55 \| 5.56 \| +0.2% | 5.57 \| 5.60 \| +0.5% | 5.53 \| 5.60 \| +1.1% | 5.54 \| 5.58 \| +0.9% |
| hot_keys/distinct_4 · dalek (hotcache) | 5.47 \| 5.49 \| +0.3% | 5.48 \| 5.50 \| +0.3% | 5.47 \| 5.50 \| +0.4% | 5.47 \| 5.48 \| +0.2% |
| hot_keys/churn_cap4 · zip215 (hotcache) | 13.17 \| 13.28 \| +0.8% | 17.60 \| 17.72 \| +0.7% | 17.62 \| 17.75 \| +0.7% | 17.59 \| 17.74 \| +0.8% |

| scenario | n=256 | n=1024 |
|---|---|---|
| hot_keys/large_distinct · zip215 (hotcache) | 6.20 \| 6.23 \| +0.4% | 9.30 \| 9.39 \| +1.0% |
