# Cache-entry layout experiment (null result) and hot-key cache sizing (2026-07-09)

**Hardware/build:** AWS c8i.2xlarge · Intel Xeon 6975P-C (Granite Rapids, 8 vCPU) · ~3.78 GHz sustained · kernel 6.17.0-1017-aws · rustc 1.97.0 · `RUSTFLAGS="-C target-cpu=native"`

Criterion medians in µs per signature, mean of two runs per side.

## Hot-key cache sizing — retention pays only for a small hot set

Measured with fully distinct resident keys (all cached after warmup), Zip215:

| resident hot keys | hot-key cache µs/sig | null-cache µs/sig | retention verdict |
|---|---|---|---|
| 4 | **7.45** | 8.70 | win, −14 % |
| 256 | **7.83** | 8.71 | win, −10 % |
| 1024 | 9.19 | **8.70** | lose, +6 % |

The null-cache path is flat (~8.7 µs/sig) at any key count — it decodes fresh
into small scratch tables that stay cache-resident. The hot-key cache degrades
as the resident set grows, because ~1000 retained tables spill L2. On this
host the crossover is ≈ 700 distinct resident keys (it scales with L2 size).
Guidance: bound `HotKeyCache::with_capacity(...)` to the key set that actually
recurs — in the low hundreds at most — rather than the total key universe.
The `hot_keys/large_distinct` bench group reproduces this sweep.

## Null result: 3-field cache-entry storage

Storing retained entries with the redundant `z2` field dropped (3 fields
instead of 4) was implemented, validated (bit-identical outputs), and measured
at three scales — 4, 256, and 1024 resident keys: deltas −0.05 %, −0.31 %,
+0.25 %, all inside the ±1.3 % noise band. Verification on this host is
compute-bound (0.87 L2-misses per signature measured at baseline), so table
bytes are not the bottleneck and the change was dropped. Recorded so the
experiment is not repeated.
