# Digest to signed radix-16 digits

The public theorem `assembled_digest_to_radix16_correct` covers one call to
`ed25519_simd_digest_to_radix16`, including the scalar reducer it calls.
For each lane, let H be its unsigned 512-bit input. On return, digit k is
the signed byte at `RDI + 64*lane + k`. Every digit is in **[-8, 7]**, and
the integer sum of `digit[k] * 16^k` for k from 0 through 63 equals
**H mod L**. This covers every digest, including zero and the maximal input.
[Public contract](coq/Audit.v) · [Theorem](coq/Object.v)

The same return has a unique store trace. It includes the saved RDI, the
implicit call push, the scalar reducer's stores and the packed digit stores
after the reducer returns. Replay starts with the caller's memory and produces
the entire returned byte memory. Every prefix stays within the 512-byte
output and the 16 bytes immediately below entry RSP.
[Trace and permission bounds](coq/Execution.v)

## What to audit

1. Check the two linked symbols and their relative addresses against the
   release ELF. Coq re-encodes the wrapper, checks the CALL displacement,
   and applies the reducer theorem to the same input memory and the return
   address actually pushed. [Wrapper listing](coq/Program.v) · [Reducer contract](../scalar/README.md)
2. Check the input and output layouts. Digest word `i` for lane `j` is the
   little-endian qword at `RSI + 8*(8*i + j)`, with word zero least
   significant. RDI designates a disjoint 512-byte output, with arbitrary byte
   alignment. Read `signed_digits` and the reconstruction equality in
   `run_correct`. The digit weights and the signed-byte range specify the
   unique balanced encoding. [Candidate call](../../../src/wide/avx512ifma/post_hash.inc) · [Canonical scalar recoding](../../curve25519/SignedRadix16.v)
3. Check the entry and return conditions. The SysV stack allows 16 private
   bytes below entry RSP for saved RDI and the nested return address. The
   code and buffers are disjoint from the stack. The theorem requires a
   unique return to the caller, restoration of RSP and the callee-saved
   registers, initialization of all eight output rows, and byte preservation
   outside the output and private stack. Entry witnesses cover every combination
   of input and output alignment and all four SysV stack residues modulo 64. [Execution proof](coq/Execution.v) · [Entry witnesses](coq/EntryTests.v)
4. Review the shared packed-instruction semantics. Adding the digit bias
   can produce a 53rd bit in a 52-bit limb. Coq checks how the packing code
   carries that bit into the next word. It also checks the
   resulting word values and the expression for every one of the 512 stored
   bytes, including unpack and shuffle indices. The machine model and its
   relationship to native execution are part of the audit surface.
   [Packing proof](coq/Packing.v) · [Byte routing](coq/Routing.v) · [Shared trust boundary](../../README.md#shared-audit-surface)

## Replay

Build the all-assembly release executable as in the crate audit guide.
Supply its path as `ELF`. The audit checks the public theorem's type and
assumptions, runs `coqchk`, and retains both symbol images, the proof sources,
and the ELF hash. The mutation checks corrupt a carry, a shuffle selector,
and the relative call target. For each altered ELF, Coq binds the modified
listing to its bytes, checks the wrong digit or call destination, and proves
the negation of the public contract. [Crate audit guide](../README.md#build-and-audit) · [Counterexamples](coq/Counterexample.v)

```sh
python3 -B verification/crate/radix16/audit.py "$ELF" --output ./radix16-audit
python3 -B verification/crate/radix16/mutations.py "$ELF" --audit ./radix16-audit
```
