# Formal verification

Coq proofs cover paired field exponentiation, four in-place point doublings,
cached point addition, scalar reduction modulo L, and the radix-256 ladder
step enabled by the optional `asm` feature.
Each routine has one public contract binding its
arithmetic, memory and ABI guarantees to the exact bytes of its linked
symbol. These are proofs in the tested machine model; independent refinement
to an x86 ISA specification remains open.

- `machine/` defines the x86-64 instruction model and tests its encodings and execution against Intel XED and native hardware. [Machine model and tests](machine/README.md)
- `arithmetic/` contains the shared integer-expression, polynomial, interval and symbolic-instruction proofs. [Shared arithmetic](arithmetic/README.md)
- `pow2/` states the routine’s contract, proves it in the machine model, and explains how to check the proof against a linked executable. [Proof and audit instructions](pow2/README.md)
- `double4/` proves the four doubling formulas, including loose inputs, biased subtraction, in-place writes and the aligned stack frame. [Proof and audit instructions](double4/README.md)

- `cached_add/` proves cached addition with projective or affine operands, optional T, read-only staged inputs, and the aligned stack frame. [Proof and audit instructions](cached_add/README.md)

- `scalar/` proves canonical reduction of all eight 512-bit inputs modulo L, including optimized Montgomery carries, conditional subtraction, and byte-memory/ABI guarantees. [Proof and audit instructions](scalar/README.md)

- `ladder_step/` proves the composition of five calls using the linked double4 and cached-add contracts. [Contract and linked audit](ladder_step/README.md)

## Build with or without the proof

On x86-64 Linux, `asm` assembles all five backends with Rust's built-in
assembler. Each `verify-asm-*` feature enables `asm`, checks the named
routine's Coq proof, and embeds that routine's exact bytes that passed.
Proof checking is off by default and can be selected independently for each
of the four standalone routines. The ladder audit checks its relative call
displacements after the linker has assigned all three symbol addresses.

```sh
export RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma"
cargo build --release --features asm            # All assembly, no build-time proof checking
cargo build --release --features verify-asm-pow2 # All assembly, with the pow2 proof checked
cargo build --release --features verify-asm-pow2,verify-asm-double4,verify-asm-cached-add,verify-asm-scalar  # All four proofs
```

Install the following tools on the host that checks the proof or audits a linked executable.

- Python 3.8 or later (`python3`, standard library)
- LLVM MC (`llvm-mc`, or set `LLVM_MC` to its executable)
- GNU binutils (`nm`, `objcopy`, `objdump`)
- Coq with its standard library and the commands `coqdep`, `coqc`, and `coqchk`

To verify the bytes in an already linked executable from either build, follow
the release audit instructions for [pow2](pow2/README.md#check-the-release-executable),
[double4](double4/README.md#check-the-release-executable),
[cached addition](cached_add/README.md#check-the-release-executable), and
[scalar reduction](scalar/README.md#replay-against-a-release-executable).
For the composed routine, run the [ladder-step audit](ladder_step/README.md).

`python3 -B verification/test_evidence.py` checks report replay, seed provenance
and audit manifest integrity without requiring Coq, XED or AVX-512 hardware.

## Shared proof infrastructure

The public contracts and `Object` theorems remain in their routine
folders. Common execution proofs live in `machine/`: lane projection,
aligned-cell separation, output-write coverage, trace frames, and lifting
logical execution to concrete byte reads at every prefix. Each routine
supplies its actual program, ABI layout, region permissions, and checked
instruction trace; its entry construction and mathematical specification
remain explicit.

`arithmetic/` uses the Coq namespace `ProofArithmetic`. It has no dependency
on a routine's program or field specification. Polynomial congruence takes
an explicit modulus. Symbolic instruction translation takes an explicit
AND-mask width while retaining the machine's fixed 52-bit IFMA operands
and 64-bit word arithmetic. Field and scalar checkers supply their own
proved mask conditions, bounds and refinement policies.

`proof_build.py` compiles both libraries and checks each complete object
certificate. The routine drivers list their proof modules and specializations.
Audit bundles retain the shared sources, namespace mappings and build driver
alongside the routine proofs. Every certificate still requires closed
assumptions and successful `coqchk` on `Object`.
