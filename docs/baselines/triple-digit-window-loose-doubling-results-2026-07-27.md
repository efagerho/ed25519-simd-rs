# Ladder micro-optimizations (radix-4096 base window + loose interior doublings) — results

Two independent changes to the ladder, measured together.

**Radix-4096 base window.** Fixed-base adds fold THREE radix-16 digits into
one radix-4096 digit: 21 triples (digits 0..62) plus the lone top digit 63.
This amounts to 22 base adds per signature instead of 32 pair-folds.
The table is heap-allocated, and built once per process with one batch
inversion. It stores ±2184 affine multiples of `B`: 4369 entries ≈ 524 KB.
The old ±136 pair-fold table and ladder remain in the tree under `cfg(test)`
as the differential oracle; they are no longer compiled into the library.

**Loose interior doublings.** `double4`'s three interior doublings skip the
multiply's trailing carry sweep: outputs are loose (limb0 < 2⁶⁰,
limbs 1..4 < 2⁵¹, per `reduce_ifma_loose`), which the next doubling's
`square_loose`/`add_loose`/wide subtracts accept by design. The fourth
doubling and `double_without_t` stay strict — mixed adds and the decide
path's limb comparisons need strict operands. Saves one carry sweep × 3
fields × 3 steps per double4, ~570 sweeps per signature.

## Measured

`benches/cold_profile` (crate-only lean binary, 512 distinct keys,
`NullKeyCache`, msg len 1), `-C target-cpu=native`, one pinned core, branch
vs base interleaved same-session, min-of-7. Per row: `base → after (Δ)` in
ns/sig, vs the affine-tables branch (d1f437e).

| workload | Intel Xeon 6975P-C (Granite Rapids) | AMD EPYC 9R45 (Zen 5) |
|---|---|---|
| Zip215, msg 1    | 8672 → 8386 (−3.3 %) | 5064 → 4900 (−3.2 %) |
| Zip215, msg 1024 | 9138 → 8770 (−4.0 %) | 5361 → 5176 (−3.5 %) |
| Zip215, mixed    | 8744 → 8460 (−3.3 %) | 5131 → 4938 (−3.8 %) |
| Dalek, msg 1     | 8661 → 8315 (−4.0 %) | 5011 → 4858 (−3.1 %) |
| Dalek, msg 1024  | 8965 → 8742 (−2.5 %) | 5302 → 5121 (−3.4 %) |
| Dalek, mixed     | 8735 → 8376 (−4.1 %) | 5076 → 4908 (−3.3 %) |

Medians land between −3.4 % and −3.9 % in every config on both hosts.

Footprint: the binary shrinks (~−25 KB: +6 KB of ladder code, −33 KB of
static pair table), while runtime memory grows by the ~524 KB heap table,
allocated once per process.

## Correctness

Tests added for triple-fold ladder to produce the same point as the old 
ladder on ordinary and order-8 torsion keys over boundary and random scalars. 
Sampled entries of the radix-4096 table equal `[d]B` against an independent 
addition chain (identity, |d| ≤ 8, radix boundaries, extremes, and a random sample). 
The frozen differential acceptance suite against `solana-ed25519` passes unchanged on both hosts.
