# Phase 2r spike — hEEA_approx_q scalar halving: measured, gate NOT met

**Hardware:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) ·
scalar-code clock ~3.78 GHz · kernel 6.17.0-1017-aws · rustc 1.97.0 ·
`RUSTFLAGS="-C target-cpu=native"` · quiet machine (all benches completed
before measurement; perf-stat protocol)

Clean-room implementation of Algorithm 4 (`hEEA_approx_q`) of ElSheikh et al.,
TCHES 2025(3), from the paper's pseudocode only (`src/eea.rs`; their C was not
consulted). Two's-complement limbs, paper's Ed25519 limb-shrink schedule
(r: 4→3 limbs below len 191), stop_value 126, t in 3 limbs. NOT wired into the
verifier or ladder (per charter); revival decision is for external review.

## Gate verdict: **> 2.5k cycles/sig → dead again** (as measured tonight)

| metric | value |
|---|---|
| **cycles/reduction (perf-stat, 2M inputs)** | **≈ 4,440** (1,176 ns; IPC 2.93; ~13.2k instr/reduction) |
| gate | ≤ 2,500 → recommend revival | 
| iterations | mean 96.1 / max 115 (bench set); mean 95.92 / max 130 (10⁷ rig) — paper: 95.2, σ 6.4 ✓ |

Honest context, not a projection: this is a first-pass clean-room rendering at
~137 instructions/iteration; the paper's tuned C measures 3,531 cycles on a
2.6 GHz Coffee Lake. Identified slack: branchy sign/rotate selection (heavily
mispredicted at ~random branch outcomes), per-iteration |r| bit-length via
conditional negate, and by-value state rotation. A sign-magnitude, branchless
rework plausibly lands materially lower, but tonight's gate binds on the
measured number. The 2r doc's ~2.0k host-scaling projection did not survive
contact with this implementation.

## Obligations (all satisfied)

1. **Congruence + bounds + tail statistics, 10⁷ inputs:** ρ ≡ τ·v (mod ℓ)
   verified (1-in-64 subsample ≈ 156k full checks + all structured/random
   suites); `rho_bits max = 126` (structural); **`tau_bits max = 126`,
   zero samples ≥ 127 in 10,000,000** — both halves fit the 32-digit ladder
   with no tail violations observed; τ mean 124.80 bits (paper Table 3:
   123.8-ish ✓). The empirical-plus-guard framing stands: production wiring
   would still add the runtime guard or the 33-digit ladder insurance.
2. **τ ≠ 0:** debug-asserted; proof sketch (Prop.-3 invariant
   `t₁r₀ − t₀r₁ = ±ℓ`, ℓ prime, len(ρ) ≤ 126) recorded in the module docs.
3. **Adapted oracle semantics:** validated congruence/bounds/determinism/
   goldens of hEEA itself. Bonus cross-validation: the four pinned golden
   outputs are **bit-identical to the dead branch's Lagrange-reduction
   goldens** for the same seeds — two independent algorithms agreeing on the
   same short pairs.

Suite state: full frozen suite green with the spike module in-tree (inert:
nothing in the verifier references it).

## Morning decision inputs

- At 4.4k cycles the revival net is ≈ (7.5k − 4.4k) ≈ 3.1k ≈ 9 % — below the
  Phase 2 10 % floor, before integration costs.
- If an optimization pass is commissioned: target < 2.5k means halving the
  per-iteration instruction count — plausible given the paper's own numbers,
  not demonstrated tonight.
- Everything transfers if revived: §2 exactness proof, phase2-design §3.4
  ladder (now partially realized by 2h!), the B′ table (already shipped in
  2h), and this spike's property rig. Notably 2h already banked the halved
  doublings for cached keys — a revived 2r would extend the win to COLD keys
  only, which shrinks its marginal value vs the original Phase 2 analysis.
