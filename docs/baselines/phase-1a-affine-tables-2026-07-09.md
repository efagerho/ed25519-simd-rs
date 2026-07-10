# Affine cached basepoint table — before/after (2026-07-09)

**Hardware/build:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) · ~3.78 GHz sustained · kernel 6.17.0-1017-aws · rustc 1.97.0 · `RUSTFLAGS="-C target-cpu=native"`

Criterion medians in µs per signature (before \| after \| Δ%), mean of two runs per side; run-to-run noise on this host is ±1.3 % worst case. Change under test: the basepoint multiples table normalized to affine cached form (one batch inversion at construction), making each fixed-base mixed addition 7 M instead of 8 M with a 3-field gather.

Message length 1:

| Backend | 8 | 16 | 32 | 64 |
|---|---|---|---|---|
| ed25519-simd Zip215 null-cache | 9.00 \| 8.69 \| -3.5% | 9.00 \| 8.72 \| -3.2% | 9.00 \| 8.68 \| -3.6% | 8.99 \| 8.71 \| -3.1% |
| ed25519-simd Dalek null-cache | 8.92 \| 8.61 \| -3.4% | 8.95 \| 8.64 \| -3.4% | 8.90 \| 8.61 \| -3.3% | 8.85 \| 8.60 \| -2.7% |

Message length 1024:

| Backend | 8 | 16 | 32 | 64 |
|---|---|---|---|---|
| ed25519-simd Zip215 null-cache | 9.41 \| 9.02 \| -4.2% | 9.36 \| 9.05 \| -3.3% | 9.38 \| 9.04 \| -3.6% | 9.37 \| 9.04 \| -3.6% |
| ed25519-simd Dalek null-cache | 9.29 \| 8.95 \| -3.6% | 9.30 \| 8.98 \| -3.4% | 9.31 \| 8.99 \| -3.4% | 9.34 \| 8.96 \| -4.0% |

Mixed message lengths:

| Backend | 8 | 16 | 32 | 64 |
|---|---|---|---|---|
| ed25519-simd Zip215 null-cache | 9.18 \| 8.88 \| -3.3% | 9.12 \| 8.80 \| -3.6% | 9.14 \| 8.82 \| -3.6% | 9.12 \| 8.78 \| -3.8% |
| ed25519-simd Dalek null-cache | 9.14 \| 8.79 \| -3.8% | 9.04 \| 8.71 \| -3.6% | 9.02 \| 8.73 \| -3.2% | 8.95 \| 8.69 \| -2.9% |

All 40 measured configurations (including invalid-signature mixes) improved,
range −2.7 % … −4.2 %, mean −3.4 %. Correctness is gated by a golden test
pinning every table entry against an independent projective reference and by
the differential acceptance suite (bit-identical accept/reject decisions).
