# Phase 3 — radix-4096 fixed-base fold: MERGED (gate pass)

**Hardware:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) ·
~3.78 GHz sustained (3.63 GHz under sustained AVX-512) · kernel 6.17.0-1017-aws ·
rustc 1.97.0 · `RUSTFLAGS="-C target-cpu=native"`

Change: full ladder's fixed-base adds fold three radix-16 digits (radix-4096):
21 triples + lone digit 63 = **22 base adds instead of 32**; `BasepointTable4096`
(±2184 affine multiples, ≈ 524 KB heap, once per process). Split ladder (2h)
unchanged. Pair-fold path kept as the cfg(test) differential oracle.

## Gate verdict: PASS ("cold AND hot non-regressing, win > noise")

Before = overnight tip (2h+F1, via `after_f1` baselines); after = Phase 3;
mean of 2 runs, 60 configs:

- **Cold (the target): all wins**, −1.8 % median, min −2.73 % — well above the
  ±1.3 % noise band. The ~524 KB table did **not** regress the cold path: the
  workload remains compute-bound (Phase 0: 0.87 L2-miss/sig headroom), and
  `cargo bench --bench cold_profile` confirms — **8652 ns/sig** on this build
  (vs 9030 at Phase 0).
- **Hot: non-regressing.** Six configs show +0.13…+0.37 % — all on the
  split-ladder path, which does not touch the 4096 table (physically
  unaffected; pure noise), and run 2 alone shows **60/60 negative**.
- Overall mean **−1.60 %**, run2 60/60 wins.

Correctness: sampled radix-4096 table golden vs an independent addition chain;
old-vs-new ladder differential (CLAUDE.md rule) — point equality across
ordinary/torsion keys × boundary/random scalars × projective/affine tables;
frozen suite green (I1).

## README-style snapshot (µs/signature: before \| after \| Δ%)

| scenario | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| distinct_keys/msg_len_1 · zip215 (nocache) | 8.74 \| 8.62 \| -1.4% | 8.72 \| 8.62 \| -1.2% | 8.73 \| 8.60 \| -1.6% | 8.75 \| 8.58 \| -2.0% |
| distinct_keys/msg_len_1 · dalek (nocache) | 8.67 \| 8.50 \| -2.0% | 8.68 \| 8.50 \| -2.1% | 8.69 \| 8.50 \| -2.2% | 8.72 \| 8.51 \| -2.4% |
| distinct_keys/msg_len_1024 · zip215 (nocache) | 9.12 \| 8.95 \| -1.9% | 9.14 \| 9.00 \| -1.5% | 9.11 \| 8.96 \| -1.6% | 9.11 \| 8.99 \| -1.3% |
| distinct_keys/msg_len_mixed · zip215 (nocache) | 8.94 \| 8.80 \| -1.5% | 8.84 \| 8.69 \| -1.6% | 8.86 \| 8.71 \| -1.7% | 8.79 \| 8.72 \| -0.7% |
| hot_keys/distinct_4 · zip215 (hotcache, split path) | 5.57 \| 5.55 \| -0.5% | 5.55 \| 5.57 \| +0.4% | 5.53 \| 5.53 \| +0.1% | 5.54 \| 5.54 \| -0.2% |
| hot_keys/distinct_4 · dalek (hotcache, split path) | 5.49 \| 5.47 \| -0.4% | 5.46 \| 5.48 \| +0.3% | 5.47 \| 5.47 \| +0.1% | 5.46 \| 5.47 \| +0.2% |
| hot_keys/churn_cap4 · zip215 (hotcache, miss path) | 13.37 \| 13.17 \| -1.5% | 17.79 \| 17.60 \| -1.0% | 17.79 \| 17.62 \| -1.0% | 17.79 \| 17.59 \| -1.1% |

| scenario | n=256 | n=1024 |
|---|---|---|
| hot_keys/large_distinct · zip215 (hotcache) | 6.18 \| 6.20 \| +0.3% | 9.36 \| 9.30 \| -0.7% |
