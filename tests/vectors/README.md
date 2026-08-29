Test fixtures in this directory are copied from public Apache-2.0 Ed25519
conformance suites:

- `ed25519_wycheproof.json`: C2SP/Wycheproof
  `testvectors_v1/ed25519_test.json`.
- `ed25519_speccheck.json`: Novi `ed25519-speccheck` `cases.json`.

`avx512ifma.json` is an internal arithmetic fixture. Its field results were
generated independently with integer arithmetic modulo `2^255 - 19`; its point
encodings were generated from the RFC 8032 Edwards formulas. Keeping the
expected values checked in lets the SIMD unit tests avoid a second field and
point implementation in the crate.

`scalar_reduction.json` similarly fixes the expected group-order reduction and
signed radix-16 recoding for one full eight-lane chunk. It was generated with
integer arithmetic modulo the RFC 8032 group order `L`.
