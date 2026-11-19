# Formal verification

The current Coq proof covers paired field exponentiation in the optional `asm-pow2` backend.

The optional `asm-double4` backend implements four in-place point doublings on
x86-64 Linux. Its ABI and arithmetic contract are documented in
[`double4.S`](../src/wide/avx512ifma/double4.S), with compile-time Rust layout
checks, independent integer fixtures, Rust differential tests and a native
SysV register-preservation test. It does not yet have a Coq proof;
`verify-asm-pow2` certifies only paired exponentiation, even when both assembly
features are enabled. The subtraction model and its bound proofs are still
required before proving this new routine.

- `machine/` defines the x86-64 instruction model and tests its encodings and execution against Intel XED and native hardware. [Machine model and tests](machine/README.md)
- `pow2/` states the routine’s contract, proves it in the machine model, and explains how to check the proof against a linked executable. [Proof and audit instructions](pow2/README.md)

## Build with or without the proof

On x86-64 Linux, `asm-pow2` assembles `pow2.S` with Rust's built-in assembler.
`verify-asm-pow2` also enables that backend, checks the Coq proof, and embeds
the exact bytes that passed. Proof checking is off by default.

```sh
export RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma"
cargo build --release --features asm-pow2         # Assembly only
cargo build --release --features verify-asm-pow2  # Assembly with the proof checked
```

Install the following tools on the host that checks the proof or audits a linked executable.

- Python 3.8 or later (`python3`, standard library)
- LLVM MC (`llvm-mc`, or set `LLVM_MC` to its executable)
- GNU binutils (`nm`, `objcopy`, `objdump`)
- Coq with its standard library and the commands `coqdep`, `coqc`, and `coqchk`

To verify the bytes in an already linked executable from either build, follow
the [release audit instructions](pow2/README.md#check-the-release-executable).

`python3 -B verification/test_evidence.py` checks report replay, seed provenance
and audit manifest integrity without requiring Coq, XED or AVX-512 hardware.
