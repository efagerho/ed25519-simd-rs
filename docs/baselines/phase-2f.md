# Phase 2f — ×19 carry-fold replacement: PARKED (gate FAIL) — NEEDS-REVIEW

**Hardware:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) ·
~3.78 GHz sustained (3.63 GHz under sustained AVX-512) · kernel 6.17.0-1017-aws ·
rustc 1.97.0 · `RUSTFLAGS="-C target-cpu=native"`

Change (plan §2f / audit F5, commit on branch `phase-2f-mul19`): every
`vpmullq`-by-19 in the reduce chains replaced sitewise — `madd52lo` accumulate
where the carry bound (< 2¹³) proves 19·x < 2⁵², exact shift-add
`(x≪4)+(x≪1)+x` at the large-operand sites. Bit-identical semantics (frozen
suite green in release and debug with bound asserts active; I1 untouched).

## Gate verdict: FAIL — no consistent-sign win

Requirement: consistent-sign win across all configs, both runs. Measured
(before = overnight tip `2c446f0` via its `after_2hv2` baselines, identical
code; after = 2f, mean of 2 runs, 60 configs):

- mean Δ **+0.196 %** (a slight net regression), median +0.14 %
- mean-of-2 wins: **23/60**; run1 wins 28/60, run2 wins 21/60
- range −0.55 % … +1.18 %

The predicted +0.5–1 % win does not exist on this µarch: either `vpmullq` is
cheaper on Granite Rapids than the audit's cost model assumed, or the 3-op
shift-add chain lengthens the carry-tail dependency path by as much as the
multi-µop multiply cost it removes. Flat-to-slightly-negative either way; the
gate's intent (demonstrable win) fails under any drift assumption.

**Disposition:** parked on `phase-2f-mul19` (implementation + report), NOT
merged; `overnight` continues from `2c446f0`. Morning options: discard (record
as a 1c-style null), or re-gate on different hardware. The audit F5 entry
should gain a "measured null on GNR" note either way.

## README-style snapshot (µs/signature: before \| after \| Δ%)

| scenario | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| distinct_keys/msg_len_1 · zip215 (nocache) | 8.87 \| 8.88 \| +0.1% | 8.87 \| 8.88 \| +0.2% | 8.86 \| 8.88 \| +0.2% | 8.86 \| 8.85 \| -0.1% |
| distinct_keys/msg_len_1024 · zip215 (nocache) | 9.21 \| 9.26 \| +0.5% | 9.18 \| 9.27 \| +1.0% | 9.22 \| 9.25 \| +0.3% | 9.18 \| 9.21 \| +0.3% |
| distinct_keys/msg_len_mixed · zip215 (nocache) | 9.02 \| 9.04 \| +0.1% | 9.00 \| 8.99 \| -0.1% | 8.99 \| 8.96 \| -0.3% | 8.89 \| 8.97 \| +0.8% |
| hot_keys/distinct_4 · zip215 (hotcache) | 5.57 \| 5.63 \| +1.1% | 5.56 \| 5.63 \| +1.2% | 5.58 \| 5.60 \| +0.4% | 5.57 \| 5.61 \| +0.8% |
| hot_keys/distinct_4 · dalek (hotcache) | 5.47 \| 5.53 \| +0.9% | 5.48 \| 5.51 \| +0.6% | 5.48 \| 5.50 \| +0.3% | 5.48 \| 5.51 \| +0.6% |
| hot_keys/churn_cap4 · zip215 (hotcache) | 13.46 \| 13.44 \| -0.1% | 17.85 \| 17.85 \| -0.0% | 17.90 \| 17.85 \| -0.3% | 17.89 \| 17.88 \| -0.0% |

| scenario | n=256 | n=1024 |
|---|---|---|
| hot_keys/large_distinct · zip215 (hotcache) | 6.20 \| 6.26 \| +1.0% | 9.39 \| 9.43 \| +0.3% |
