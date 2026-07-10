# Affine cached hot-key entries — before/after (2026-07-09)

**Hardware/build:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) · ~3.78 GHz sustained · kernel 6.17.0-1017-aws · rustc 1.97.0 · `RUSTFLAGS="-C target-cpu=native"`

Criterion medians in µs per signature (before \| after \| Δ%), mean of two runs per side. Change under test: retained hot-key tables normalized to affine cached form, so all-hit chunks run the 7 M mixed addition on the variable-base side as well; the single-use (null-cache) decode path is unchanged.

Hot key repeats (4 distinct keys cycled, Zip215):

| Backend | 8 | 16 | 32 | 64 |
|---|---|---|---|---|
| hot-key cache (warm) | 7.66 \| 7.58 \| -1.0% | 7.68 \| 7.57 \| -1.4% | 7.67 \| 7.57 \| -1.3% | 7.69 \| 7.59 \| -1.3% |
| null-cache | 8.72 \| 8.76 \| +0.5% | 8.70 \| 8.77 \| +0.9% | 8.71 \| 8.75 \| +0.5% | 8.72 \| 8.71 \| -0.1% |

Distinct keys (cold-path guard, message length 1):

| Backend | 8 | 16 | 32 | 64 |
|---|---|---|---|---|
| ed25519-simd Zip215 null-cache | 8.64 \| 8.71 \| +0.8% | 8.64 \| 8.71 \| +0.8% | 8.63 \| 8.65 \| +0.3% | 8.63 \| 8.60 \| -0.3% |
| ed25519-simd Dalek null-cache | 8.55 \| 8.65 \| +1.2% | 8.58 \| 8.60 \| +0.3% | 8.58 \| 8.60 \| +0.2% | 8.58 \| 8.61 \| +0.3% |

The warm hot-key path improves a consistent −1.0…−1.4 % (above the ±0.3 %
hot-path noise); the cold-path guard is flat within noise across all 40
configurations (mean +0.13 %). Golden tests pin the normalized entries by
cross-multiplication against the projective originals, independent of the
inversion used to build them.
