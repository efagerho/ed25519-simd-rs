# Phase 2h design addendum — cached-key scalar split (no lattice)

Companion to `docs/optimization-plan.md` §Phase 2h. Self-contained: the parent
Phase 2 design (`docs/phase2-design.md`, NO-GO) lives on the dead
`phase-2-halved-scalars` branch; the §3.3/§3.4 material it contributes is
reproduced verbatim here with the 2h scalar mapping.

## 1. The identity (and why there is nothing to prove)

Split both ladder scalars by a plain integer split at bit 127 — **no mod-ℓ
reduction, no lattice, no short-vector pair**:

    k = k₀ + 2¹²⁷·k₁      s = s₀ + 2¹²⁷·s₁      (integer identities, no wrap)

and precompute `A′ = [2¹²⁷]A` (per key, on first reuse — §4) and `B′ = [2¹²⁷]B`
(once per process). Then

    [k]A = [k₀]A + [k₁]A′        [s]B = [s₀]B + [s₁]B′

by nothing more than the ℤ-module axioms (`[m+n]P = [m]P + [n]P`,
`[mn]P = [m]([n]P)`): the identities hold for **every** group element,
torsion components included, with no cofactor argument and no dependence on
point orders. The ladder therefore computes **the same group element**
`[s]B − [k]A` as today, only via a different addition chain. Consequently:

- **Acceptance is bit-identical by construction, for both policies.** Phase 2's
  Zip215-only restriction does *not* carry over — there is no `[v₁]` factor and
  no `[mℓ]A` offset, so the cofactorless Dalek comparison is equally unaffected.
  The differential suites still gate the change (I1), but the argument is one
  line, not a proof section.
- **No R table and no per-signature scalar work beyond byte splits.** R keeps
  coefficient 1 and is subtracted (Zip215) or compared (Dalek) at the end,
  exactly as today. The per-signature cost that killed Phase 2 — the Lagrange
  reduction — does not exist here. Its replacement, `A′`, is per-*key* work,
  paid once at the key's first reuse (§4).

The only proof obligations, per the plan: the digit bounds (§2) and a golden
`A′ = [2¹²⁷]A` test (§5).

## 2. Digit bounds (Phase 2 design §3.3, restated)

Signed radix-16, on 16-byte halves. A value `x < 2¹²⁷` has top nibble
(bits 124–127) ≤ 7; the signed-digit carry into that nibble is ≤ 1, so digit 31
≤ 8 — in range `[−8, 8]`, **no 33rd digit, exactly 32 digits**.

- `k₀, s₀ < 2¹²⁷` by the split. ✓
- `k₁ = k ≫ 127` and `s₁ = s ≫ 127`: `k, s < ℓ < 2²⁵² + 2¹²⁵`, so
  `k₁, s₁ ≤ 2¹²⁵`. ✓
- All four scalars are **non-negative** (unlike Phase 2's `v₀, v₁`): no sign
  normalization, no negated digit streams — the existing signed-digit recoding
  and ±symmetric tables are used as-is.
- Zero digits hit the identity table center; the digit count is a fixed 32 per
  scalar per lane, so the lockstep structure is unchanged (I2).

`debug_assert`: the recoding of each half asserts no carry out of digit 31.

## 3. Ladder (Phase 2 design §3.4 verbatim, scalars mapped)

Mapping from the Phase 2 text: `v₀ → k₀` on `A`, `v₁ → k₁` on `A′` (in place of
the deleted R table), `t₀ → s₀` on `B`, `t₁ → s₁` on `B′`.

    add k₀(31) on A,  k₁(31) on A′
    acc = double4
    add s₀-pair(15) on B, s₁-pair(15) on B′, k₀(30) on A, k₁(30) on A′
    for p in (0..15).rev():            # 15 more pair blocks
        acc = double4
        add k₀(2p+1) on A,  k₁(2p+1) on A′
        acc = double4
        add s₀-pair(p) on B, s₁-pair(p) on B′, k₀(2p) on A, k₁(2p) on A′

Totals per chunk pass: **31 × double4 = 124 doublings** (vs 252 today) and
**96 adds**: 32 on `A`, 32 on `A′`, 16 on `B`, 16 on `B′` (vs 96 = 64 + 32
today — the add count is unchanged; the entire win is the halved doubling
chain). Base-pair folding is unchanged in shape (`|d₂ₚ + 16·d₂ₚ₊₁| ≤ 136`,
16 folded digits each for `s₀`/`s₁`, indexing `BASE_TABLE` / `BASE_TABLE_PRIME`).

On the gated path every table is affine (A and A′ normalized at insert per 1b,
B and B′ affine per 1a), so all 96 adds are 7 M mixed-adds. The ladder ends in
`combined = [s]B − [k]A` exactly as `mul_base_minus_public` does today; the
policy-specific tails (subtract R + cofactor doublings / recompute-compare) are
untouched.

## 4. Tables

**`B′ = [2¹²⁷]B`** — once per process: generalize the 1a `BasepointTable`
constructor to an arbitrary base point (`from_point`), feed it 127 doublings of
`B`; same 273-entry signed affine-Niels layout, same batch-inversion
normalization, `LazyLock` beside `BASE_TABLE` (~33 KB second hot table region —
the compute-bound profile predicts harmless; asserted by the flatness guard).

**`A′ = [2¹²⁷]A`** — **lazy, SIMD-batched promotion** (review change to the
original insert-time scalar build):

- **When:** on a key's **first reuse** (first cache *hit* whose entry lacks
  `table_hi`), never at insert. Single-use keys pay nothing; a churn workload
  (misses evicted before reuse) degrades to **exactly 1b** — no A′ is ever
  built. The chunk that triggers promotion still runs the current ladder; the
  split ladder engages from the key's *second* reuse on.
- **How:** all promoting lanes of a chunk share **one wide 127-doubling pass**:
  recover each lane's `A` from its cached table's digit-1 entry (the cached
  fields give `(2X : 2Y : 2Z)`, a valid projective representative; `double()`
  never reads the input `T`), pack into a `WidePoint` (idle lanes carry the
  identity), 126 × `double_without_t` + 1 × `double`, then the existing SIMD
  radix-16 table builder — the same machinery the miss path uses — and
  `normalized_affine()` per promoted lane. One pass costs ≈ half a ladder and
  is paid **once per key ever**, amortized across every promoting lane in the
  chunk (8–80× cheaper than the scalar per-key build it replaces).
- **Adoption:** the verifier hands the upgraded entry back through
  `KeyCache::insert`; a retaining cache adopts `table_hi` into the existing
  entry (recency preserved), `NullKeyCache` drops it as always.

`CachedPublicKey::from_encoded` keeps its current cost (`table_hi: None`).
Promoted entries grow to two tables (~2×, ≈ 5.4 KB/key): the §6 sweep
re-measures the retention crossover (was ≈ 700 keys at 1-table entries; expect
roughly half).

## 5. Gating and tests

**Gating** (1b's pattern, one level up): a chunk takes the split ladder iff
**all 8 lanes are cache hits whose entries carry `table_hi`**; any miss or
missing split table routes the whole chunk through today's ladder, byte-for-
byte. Padded tail lanes duplicate a real lane, so gating is well-defined.

**Tests:**

- Golden `A′ = [2¹²⁷]A`: the promotion-built `table_hi` base equals 127
  independent doublings of the raw decompressed key point (full
  recover→wide-double→table→normalize pipeline); lazy-promotion semantics
  (none after insert, present after first reuse); recovery roundtrip
  (`recover(table(A))` compresses to `A`) for projective and affine tables on
  ordinary and small-order points.
- Golden `B′` table: every entry equals `[d·2¹²⁷]B` against an independent
  projective reference (1a's test shape).
- Split recomposition: `k₀ + 2¹²⁷k₁ = k` over random + boundary scalars
  (0, 1, `2¹²⁷ ± 1`, `ℓ−1`); digit-bound asserts.
- Ladder golden (with the wiring): split-vs-full ladder point equality on
  random and adversarial `(s, k, A)` including small-order and torsioned `A` —
  the point must be *equal*, not just accept-equivalent.
- Frozen acceptance suite unchanged (I1); warm-vs-cold differentials in
  `solana_ed25519_compat` already exercise cached-path acceptance identity.

## 6. Measurement plan and expectation

Judge (three prongs, before/after ×2, means of Criterion medians):

1. `hot_keys/distinct_4` — the steady-state hot-path win, **both policies**:
   the report must show Dalek improving consistently with Zip215 (the split
   computes the same point, so both benefit; the differential suites gate it).
2. `hot_keys/large_distinct` — re-find the retention crossover with ~2×
   promoted entries (was ≈ 700 keys).
3. `hot_keys/churn` (**new**): key set exceeds capacity, all-miss steady state
   — must stay at 1b levels (lazy promotion means no A′ is ever built).

Guard: `distinct_keys` (nocache) flat — the cold path gains a per-chunk gate
check and nothing else.

Hot-chunk arithmetic (model units, §5 calibration): doublings 252 → 124 saves
≈ 416 M + 512 S ≈ 855 units ≈ **7.5 k cycles/sig**; adds unchanged. Against the
~7.5 µs/sig (≈ 28–29 k cycles) hot-cache baseline that is **≈ +25 % on fully
hot chunks** (the plan's "≈ +20 %" with the 1a/1b table effects already in the
baseline). Zero effect on cold chunks; insert cost grows by the A′ build
(visible only in miss-heavy churn, bounded by the breakeven analysis).
