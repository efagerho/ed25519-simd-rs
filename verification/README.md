# Formal verification

Coq proofs cover paired field exponentiation, four in-place point doublings,
and cached point addition in the optional `asm-pow2`, `asm-double4`, and
`asm-cached-add` backends. Each routine has one public contract binding its
arithmetic, memory and ABI guarantees to the exact bytes of its linked
symbol. These are proofs in the tested machine model; independent refinement
to an x86 ISA specification remains open.

- `machine/` defines the x86-64 instruction model and tests its encodings and execution against Intel XED and native hardware. [Machine model and tests](machine/README.md)
- `pow2/` states the routine’s contract, proves it in the machine model, and explains how to check the proof against a linked executable. [Proof and audit instructions](pow2/README.md)
- `double4/` proves the four doubling formulas, including loose inputs, biased subtraction, in-place writes and the aligned stack frame. [Proof and audit instructions](double4/README.md)

- `cached_add/` proves cached addition with projective or affine operands, optional T, read-only staged inputs, and the aligned stack frame. [Proof and audit instructions](cached_add/README.md)

## Build with or without the proof

On x86-64 Linux, the three `asm-*` features assemble their respective sources
with Rust's built-in assembler. The corresponding `verify-asm-*` features enable
the backend, check its Coq proof, and embed the exact bytes that passed. Proof checking is off by default; the features are independent.

```sh
export RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma"
cargo build --release --features asm-pow2         # Assembly only
cargo build --release --features verify-asm-pow2  # Assembly with the proof checked
cargo build --release --features verify-asm-pow2,verify-asm-double4,verify-asm-cached-add  # All three proofs
```

Install the following tools on the host that checks the proof or audits a linked executable.

- Python 3.8 or later (`python3`, standard library)
- LLVM MC (`llvm-mc`, or set `LLVM_MC` to its executable)
- GNU binutils (`nm`, `objcopy`, `objdump`)
- Coq with its standard library and the commands `coqdep`, `coqc`, and `coqchk`

To verify the bytes in an already linked executable from either build, follow
the release audit instructions for [pow2](pow2/README.md#check-the-release-executable),
[double4](double4/README.md#check-the-release-executable), and
[cached addition](cached_add/README.md#check-the-release-executable).

`python3 -B verification/test_evidence.py` checks report replay, seed provenance
and audit manifest integrity without requiring Coq, XED or AVX-512 hardware.
