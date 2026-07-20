# Affine basepoint table + in-register transpose — before/after

Change under test: the basepoint multiples table is normalized to affine cached
form (one batch inversion at construction), making each fixed-base mixed
addition 7 M instead of 8 M with a 3-field gather; the SIMD table gather uses an
in-register transpose (masked loads + `unpack`/`shuffle`) rather than a
scalar-store-then-reload round trip.

Cold-path wall-clock, `cargo bench --bench cold_profile` (crate-only lean binary,
Zip215, 512 distinct keys, msg len 1, `NullKeyCache`), `-C target-cpu=native`,
one pinned core, min-of-replicates, base vs branch interleaved same-session.

| CPU | base (ns/sig) | after (ns/sig) | Δ |
|---|---:|---:|---:|
| Intel Xeon 6975P-C (Granite Rapids) | 8762 | 8477 | −3.3 % |
| AMD EPYC 9R45 (Zen 5) | 5236 | 5053 | −3.5 % |

On Zen 5 the improvement is separated cleanly from noise (every paired run
favors the branch; no distribution overlap) and corroborated by hardware
counters: instructions −4.8 %, legacy-decoder µop share 32.6 % → 27.3 %.

Correctness: А test pins every table entry against an independent
projective reference, and the differential acceptance suite against
`solana-ed25519` is bit-identical (unchanged accept/reject decisions) on both
hosts.
