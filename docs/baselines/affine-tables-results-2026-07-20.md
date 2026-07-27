# Affine basepoint table + in-register transpose — before/after

Change under test: the basepoint multiples table is normalized to affine cached
form (one batch inversion at construction), making each fixed-base mixed
addition 7 M instead of 8 M with a 3-field gather; the SIMD table gather uses an
in-register transpose (masked loads + `unpack`/`shuffle`) rather than a
scalar-store-then-reload round trip.

Cold-path wall-clock, `cargo bench --bench cold_profile` (crate-only lean binary,
512 distinct keys, `NullKeyCache`), `-C target-cpu=native`, one pinned core,
min-of-4, base vs branch interleaved same-session. Per row: `base → after (Δ)`
in ns/sig.

| workload | Intel Xeon 6975P-C (Granite Rapids) | AMD EPYC 9R45 (Zen 5) |
|---|---|---|
| Zip215, msg 1     | 8722 → 8505 (−2.5 %) | 5227 → 5052 (−3.3 %) |
| Zip215, msg 1024  | 9051 → 8797 (−2.8 %) | 5512 → 5355 (−2.8 %) |
| Zip215, mixed     | 8827 → 8613 (−2.4 %) | 5294 → 5128 (−3.1 %) |
| Dalek, msg 1      | 8663 → 8404 (−3.0 %) | 5233 → 5028 (−3.9 %) |
| Dalek, msg 1024   | 9075 → 8829 (−2.7 %) | 5457 → 5295 (−3.0 %) |
| Dalek, mixed      | 8748 → 8538 (−2.4 %) | 5294 → 5067 (−4.3 %) |

Correctness: a test pins every table entry against an independent
projective reference, and the differential acceptance suite against
`solana-ed25519` is bit-identical (unchanged accept/reject decisions) on both
hosts.
