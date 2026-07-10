# Phase F1 — loose interior doublings: MERGED (gate pass on extended protocol)

**Hardware:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) ·
~3.78 GHz sustained (3.63 GHz under sustained AVX-512) · kernel 6.17.0-1017-aws ·
rustc 1.97.0 · `RUSTFLAGS="-C target-cpu=native"`

Change (audit F1, charter constraints honored): `double_impl` gains a
`LOOSE_OUT` const parameter used ONLY by `double4`'s three interior steps —
they emit loose x, y, z via `multiply_loose` (skipping the trailing
`reduce_loose` pass; limb0 < 2⁶⁰). `double_without_t` is unchanged globally
(the decide path's `equals_lanes`/`identity_lanes` compare limb
representations and need strict operands). Bound comments at every site;
e, f, g, h remain strict multiply operands (subtract_wide ends in
reduce_loose). Saves one reduce_loose pass × 3 fields × 3 interior steps per
double4 — 189/252 doublings on the cold ladder, 93/124 on the split ladder.

## Gate verdict: PASS (extended protocol — documented)

Standard 2-run protocol: mean **−1.06 %**, 58/60 configs win, run2 59/60 —
but two hot n=8 configs straddled zero (+0.15 %, +0.37 %, inside the ±1.3 %
noise band). Per the charter this is the ambiguous case; rather than park a
clearly real win, two additional `hot_keys/distinct_4` rounds were run and the
straddlers judged on the **4-run mean**:

- hotcache zip215 n=8: **−0.10 %** (runs: +0.02, +0.29, −0.09, −0.61)
- hotcache dalek n=8: **−0.11 %** (runs: +0.97, −0.23, −0.51, −0.67)

With the 4-run means, **all 60 configs are negative** → consistent-sign win.
The effect is smaller on hot small batches (the split ladder has half the
doublings, so half the reduce_loose passes to save) and strongest on the cold
ladder (−1.2 %+), matching the audit's ~1–1.5 % ceiling. ⚠ The tie-break
extension beyond the literal "both runs" wording is flagged for morning review.

Correctness: frozen suite green in release and debug; outputs bit-identical
(loose limbs are a representation change only; every downstream comparison
path normalizes first — decide path untouched).

## README-style snapshot (µs/signature: before \| after \| Δ%)

| scenario | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| distinct_keys/msg_len_1 · zip215 (nocache) | 8.87 \| 8.74 \| -1.5% | 8.87 \| 8.72 \| -1.6% | 8.86 \| 8.73 \| -1.4% | 8.86 \| 8.75 \| -1.3% |
| distinct_keys/msg_len_1024 · zip215 (nocache) | 9.21 \| 9.12 \| -1.0% | 9.18 \| 9.14 \| -0.4% | 9.22 \| 9.11 \| -1.2% | 9.18 \| 9.11 \| -0.8% |
| distinct_keys/msg_len_mixed · zip215 (nocache) | 9.02 \| 8.94 \| -1.0% | 9.00 \| 8.84 \| -1.8% | 8.99 \| 8.86 \| -1.4% | 8.89 \| 8.79 \| -1.2% |
| hot_keys/distinct_4 · zip215 (hotcache, 4-run) | 5.57 \| 5.56 \| -0.1% | 5.56 \| 5.54 \| -0.4% | 5.58 \| 5.53 \| -0.9% | 5.57 \| 5.54 \| -0.5% |
| hot_keys/distinct_4 · dalek (hotcache, 4-run) | 5.47 \| 5.47 \| -0.1% | 5.48 \| 5.45 \| -0.6% | 5.48 \| 5.45 \| -0.6% | 5.48 \| 5.45 \| -0.6% |
| hot_keys/churn_cap4 · zip215 (hotcache) | 13.46 \| 13.37 \| -0.7% | 17.85 \| 17.79 \| -0.4% | 17.90 \| 17.79 \| -0.6% | 17.89 \| 17.79 \| -0.5% |

| scenario | n=256 | n=1024 |
|---|---|---|
| hot_keys/large_distinct · zip215 (hotcache) | 6.20 \| 6.18 \| -0.3% | 9.39 \| 9.36 \| -0.3% |
