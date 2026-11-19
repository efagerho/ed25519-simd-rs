# Four in-place doublings

Start with one theorem:

```coq
Object.assembled_double4_correct : Audit.double4_contract ObjectBytes.symbol_bytes
```

[`Audit.double4_contract`](coq/Audit.v) is the complete public claim for
`ed25519_simd_double4_ifma`. Its only parameter is the linked symbol's bytes.
[`Object.v`](coq/Object.v) proves it without axioms. The independently stated
arithmetic specification is in [`Double4Spec.v`](coq/Double4Spec.v), with
limb bounds in [`Bounds.v`](coq/Bounds.v).

## What the theorem guarantees

RDI points to an exclusive, initialized, 64-byte-aligned `WidePoint` occupying
1,280 bytes. X, Y, Z and T start at offsets 0, 320, 640 and 960. Each coordinate
has five vectors of eight little-endian qwords. Limb `i` of lane `j` has
offset `64*i + 8*j` within its coordinate and weight `2^(51*i)`.

For each input X, Y and Z, in each lane:

- All limbs are nonnegative; limb 0 is below `2^60`.
- `limb1 + floor(limb0 / 2^51) < 2^52`.
- Limbs 2, 3 and 4 are below `2^52`.

Incoming T can contain arbitrary qwords and is never read. There is no
curve-membership or extended-coordinate invariant precondition. Modulo
`p = 2^255 - 19`, the result is four applications of these formulas:

```text
A = X²       B = Y²       C = Z²       D = (X + Y)²
E = D - A - B             G = B - A
F = G - 2C               H = -A - B
X' = EF      Y' = GH      Z' = FG      T' = EH
```

The first three rounds need only X, Y and Z. Every final coordinate has
limbs 0, 2, 3 and 4 below `2^51` and limb 1 below `2^52`. These bounds imply
the next doubling's input condition (`reduced_loose`) and the field
multiplication bound of `2^52` per limb.

The same theorem also guarantees:

- Finite execution and normal return, RBX/RBP/R12–R15 preservation, and RSP
  advanced by eight bytes from its entry value.
- Every output byte is written. Vector writes fit in the point or the
  1,280-byte aligned scratch area. Saved RBP, alignment padding and two
  nested return addresses require at most 1,352 bytes below entry RSP.
- Calls, returns, PUSH and POP use the same byte memory as vector accesses.
  Every pop reads the expected qword. The caller's return bytes remain
  unchanged at every trace prefix; all bytes outside the point and private
  stack interval retain their original values.
- Starting from one actual byte array and unsigned register values, the
  proof constructs the logical entry. Every logical vector read agrees
  exactly with little-endian byte decoding at every memory-event prefix.
  Integer registers and vector lanes remain unsigned qwords.
- For all four SysV stack alignment cases, the modeled alignment agrees
  with integer `AND RSP,-64` at the concrete placement.

Memory/ABI safety and output initialization hold independently of the
arithmetic input bounds. Placements must not wrap the 64-bit address space;
the point, stack and code regions must be disjoint. Native callers must
supply accessible storage, a SysV-aligned stack, a valid return address and
AVX-512F/DQ/IFMA support. These requirements are explicit in
[`Double4ABI.v`](coq/Double4ABI.v), [`Double4Memory.v`](coq/Double4Memory.v) and
[`Double4Bytes.v`](coq/Double4Bytes.v).

## Check the release executable

From the repository root, with Python 3.8+, LLVM MC, GNU binutils and Coq
(`coqdep`, `coqc`, `coqchk`) on PATH:

```sh
elf=/path/to/unstripped-release-elf
python3 -B verification/double4/audit.py "$elf" \
  --output ./double4-audit --cases ./double4-cases.jsonl --seed 42
```

The checker independently extracts the ELF symbol bytes, expands `double4.S`
with LLVM MC, and generates a readable Coq program. Coq proves that encoding
that program equals the extracted bytes, including padding, and proves its
execution contract. The checker requires `Closed under the global context`
and runs `coqchk`. It retains all proof sources, both instruction listings,
raw symbol bytes, tool versions, logs and SHA-256 hashes in the audit directory.
[`audit.py`](audit.py) · [`certificate.py`](certificate.py) · [`listing.py`](listing.py)

An auditor can rebuild the retained proof without the repository or assembler:

```sh
cd double4-audit
set -e
for proof_source in $(coqdep -sort -f _CoqProject); do
  coqc -Q machine Machine -Q arithmetic ProofArithmetic "$proof_source"
done
coqchk -Q machine Machine -Q arithmetic ProofArithmetic -silent Object
```

Compiling `Object.v` must print `Closed under the global context`. In
`coqtop -quiet -Q machine Machine`, inspect the exact theorem type:

```coq
Require Object Audit ObjectBytes.
Check Object.assembled_double4_correct : Audit.double4_contract ObjectBytes.symbol_bytes.
```

Compare `Program.v` and `double4.expanded.S` with
`objdump -d -M intel --disassemble=ed25519_simd_double4_ifma "$elf"`.
Both retained listings show symbol-relative instruction offsets; the assembly
listing also shows the bytes. `manifest.json` binds the evidence to the ELF
and symbol hashes. Rebuilding, rather than trusting the manifest, repeats
the kernel check.

To check and embed certified bytes during a Rust build:

```sh
export RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma"
cargo build --release --features verify-asm-pow2,verify-asm-double4
```

The build runs the same theorem and emits literal certified bytes through
[`review.py`](review.py). Release auditing still checks the final linked
artifact. `asm-double4` alone selects the same assembly without requiring
the proof toolchain.

The optional case export covers every modeled vector instruction occurrence
in the symbol, using its linked bytes and full seeded input registers. It
also checks that native probes cover every scalar/control form in the caller.
With a pinned XED kit and supported CPU:

```sh
python3 -B verification/machine/tests/run.py --backend all \
  --xed-kit /path/to/xed-kit --report ./machine-report.json
python3 -B verification/machine/tests/run.py --backend all \
  --xed-kit /path/to/xed-kit --cases ./double4-cases.jsonl \
  --report ./double4-report.json
```

## Proof structure and trust boundary

| Files | Responsibility |
| --- | --- |
| [Shared Interval.v](../arithmetic/Interval.v), `Symbolic.v` | Sound signed interval evaluation and symbolic instruction execution. Subtraction keeps its `2^64` remainder unless both bounds prove no wrap. Relational square-input hints require proofs. |
| `Kernels.v`, `KernelInterface.v` | Check addition/reduction, loose squaring, biased subtraction/reduction, paired multiplication and single multiplication against the actual generated instruction blocks. Reuse the proved field polynomial checker from pow2. |
| `RoundArithmetic.v`, `Preparation.v`, `Finish.v` | Compose the kernel results with the actual register moves and scratch loads/stores into one doubling. |
| `Round.v`, `Execution.v`, `Logical.v` | Check the actual caller path, including three early rounds and the final T-producing round, and lift lane arithmetic to the full machine state. |
| `FrameProof.v`, `Double4Bytes.v`, `ReadFootprint.v` | Stack/ABI preservation, shared byte-memory agreement, complete output writes, and absence of incoming T reads. |
| `EntryTests.v` | Concrete witnesses for all four stack alignments, rejection of a wrong return address, and unconditional initialization even for limbs outside the arithmetic bound. |
| `Audit.v`, `Object.v` | The public contract and its proof bound to independently supplied symbol bytes. |

Generators, interval checks and polynomial normalization do not supply
unchecked correctness claims: their results are justified by Coq proofs and
rechecked by the kernel. Byte extraction and the auditor's identification of
the release ELF remain part of the evidence process.

The instruction semantics, encodings and abstraction of pointers are a
remaining trust boundary. Subtraction has native/XED boundary and aliasing
tests. The aligned-frame probe tests saved RBP, both nested return slots,
all four padding cases, memory guards and register contents. Shared lemmas
prove instruction/block agreement, word bounds, memory frames, exact byte
reads and alignment arithmetic. Tests do not replace an independent ISA
refinement theorem; that theorem remains open.
[`Machine model`](../machine/README.md) · [`ISA obligation`](../machine/proofs/README.md)

This certificate proves the four coordinate formulas. It does not yet prove
the group-theoretic statement `[16]P`, the surrounding Rust caller, constant
time on physical hardware, or the complete Ed25519 verifier.
