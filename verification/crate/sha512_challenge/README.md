# Eight-lane SHA-512 challenge

The release theorem is **`assembled_sha512_challenge_correct`**. For each lane
`j` it proves that byte `i` of `SHA-512(R[j] || A[j] || message[j])` is at
`out + 64*(i/8) + 8*j + i%8` on return. Each message has its own length.
A lane that finishes early keeps its digest while the other lanes continue.
The theorem also gives the return PC, restored RSP, SysV callee-saved registers,
and preservation of every byte outside the private stack and the 512-byte output.
[Public contract](coq/Audit.v) · [Release theorem](coq/Object.v) · [Digest postcondition](coq/Output.v)

## What to audit

1. **Identify the release image.** Compare the ELF, the symbol
   `ed25519_simd_sha512_challenge`, and its read-only data with the manifest.
   Coq re-encodes the complete symbol, including the internal row helper, and
   checks the shuffle mask, length literals, IV and all 80 round constants.
   The decoder reads the actual branch displacements, RIP-relative operands,
   stack adjustment and row increments. It follows the K pointer to determine
   which constants each group of rounds consumes. [ELF extraction](audit.py) ·
   [Image](coq/Image.v) · [Control flow](coq/Control.v)
2. **Check the ABI.** RDI supplies the output, RSI and RDX the consecutive
   32-byte R and public-key encodings, and RCX and R8 the eight message
   pointers and eight byte lengths. The placement premises permit unaligned
   external buffers and overlapping read-only inputs. A zero-length slice
   needs no readable message byte. Check the disjoint output and private
   stack, the slice length limit, and the mapping of the linked constants
   at the same load bias as the code. [Rust call](../../../src/sha512.rs) ·
   [Placement and stack layout](coq/Frame.v)
3. **Check the instruction semantics.** The round and transpose lists supply
   operands to both the encoder and the interpreter. Verify the qword lanes,
   rotate direction, destination operand of ternary logic, and 128-bit
   sublanes of the byte shuffle. Coq checks the ternary truth tables and
   every routed byte. It proves that executing the round instructions with
   a rotating register assignment and a 16-word schedule ring implements
   reference compression for arbitrary blocks and incoming states.
   [Rounds](coq/Rounds.v) · [Transpose](coq/Transpose.v) · [Compression refinement](coq/Block.v)
4. **Check the grouped execution against the disassembly.** The outer routine
   uses instruction-group semantics. This correspondence is part of the
   trusted model. Compare the two prefix loads, pointer and length addressing,
   full-row test, borrow and partial-row masks, length-word insertion, state
   spills, and masked stores with their groups in the image. Check which
   registers the groups clobber. The model combines disjoint row stores and
   reads the immutable constants once. Coq proves that the actual stack
   values used for feed-forward and the trailer agree with the input, that
   writes preserve the input bytes, and that all modeled message-byte loads
   stay within their lane's slice. The shared byte memory also holds the saved
   RBP and return addresses. [Assembly](../../../src/sha512.S) ·
   [Row loads and masks](coq/Rows.v) · [Grouped execution](coq/Execution.v) ·
   [Refinement to physical memory](coq/Refinement.v)

The reference function is independent of lane packing and assembly. Its
transcription of FIPS 180-4 and the shared x86 and memory semantics have
their own audit guides. [SHA-512 specification](../../sha512/README.md) ·
[Shared audit surface](../../README.md#shared-audit-surface)

## Reproduce the certificate

With the shared Coq libraries built, run this against the intended release ELF
using a fresh output directory.

```sh
python3 -B verification/crate/sha512_challenge/audit.py "$ELF" --output "$AUDIT"
python3 -B verification/crate/sha512_challenge/mutations.py "$ELF" --audit "$AUDIT"
```

The audit checks the public declaration against its expected type, runs
`coqchk`, and requires `Print Assumptions` to report a closed theorem.
On an AVX-512F/BW host, add `--native` to compare the modeled rotates,
ternary instructions and byte shuffle with hardware. CI runs the certificate
and mutation checks on the ZIP-215 release ELF. Each of the eleven mutations
gets a Coq proof that the published contract is false for the altered image.
For the changed rotate, a second proof executes the altered round from a
concrete register state and finds the wrong SHA-512 result. [Hardware probes](probes.py) ·
[Mutation checks](mutations.py) · [Round counterexample](coq/RotationMutant.v)
