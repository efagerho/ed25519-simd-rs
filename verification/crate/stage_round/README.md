# Table selection and staging

The public theorem `assembled_stage_round_correct` binds the linked
`ed25519_simd_stage_round` symbol to the contents of all 440 output qwords.
For round `p`, let `e = 2*p` and `o = e+1`. In each lane, column `c`
copies the complete 64-bit word at offset `8*c` in the selected entry.
The destination is row `first+c`, qword `lane`. [Contract](coq/Audit.v) · [Theorem](coq/Object.v)

| Operand | First row | Columns | Zero-based entry index for this lane |
| --- | ---: | ---: | --- |
| Odd key | 0 | 20 | `8 − k[o]` |
| Affine base | 20 | 15 | `136 + s[e] + 16*s[o]` |
| Even key | 35 | 20 | `8 − k[e]` |

## What to audit

1. Match the six SysV register arguments and the Rust layouts to `placement`.
   RDI points to 3,520 exclusive bytes aligned to 64. RSI points to eight
   pointers to 17-entry key tables. Pointers may repeat. RDX points to 273
   affine entries. RCX and R8 point to lane-major signed-byte arrays, each
   eight rows of 64 digits. R9 is in 0–31. The four digits read per lane must
   be in −8 through 7. Check that the caller supplies readable input regions,
   a return slot, and writable output disjoint from all of them and the code.
   [Full ladder caller](../../../src/wide/avx512ifma/mul_s_base_minus_k_public.S) · [Rust inputs](../../../src/wide/avx512ifma/ladder_step_asm.rs) · [Table layout and construction](../../../src/edwards.rs)
2. Check `selected` against the table ordering. Projective entries store five
   words each of Y−X, Y+X, 2dT and 2Z. Affine entries omit 2Z. The theorem
   copies arbitrary limb bits. The mathematical point represented by a table
   entry depends on how Rust constructed the table. The separate ladder theorem
   consumes the staged operands under its point-representation premises.
   [Selection arithmetic](coq/Selection.v) · [Ladder contract](../ladder_step/README.md)
3. Check `access_coverage`, `initializes_output` and `stage_correct`. Each full
   vector load fits in a selected entry. The other data loads read pointers
   and digits. The routine writes all 55 rows, preserves every byte outside
   the output, restores the SysV saved registers, and returns through the
   original stack word with RSP advanced by eight. Table addresses depend
   on public digits. [Typed instruction listing](coq/Program.v) · [Transpose proof](coq/Routing.v) · [Shared machine assumptions](../../README.md#shared-audit-surface)

## Replay

Build the all-assembly benchmark and pass its linked ELF to the audit.

```sh
export RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma"
cargo build --locked --release --features asm --bench cold_profile_dalek \
  --target x86_64-unknown-linux-gnu --message-format=json > /tmp/stage-build.json
elf=$(jq -r 'select(.target.name == "cold_profile_dalek" and .executable != null) | .executable' /tmp/stage-build.json)
python3 -B verification/crate/stage_round/audit.py "$elf" --output ./stage-audit
python3 -B verification/crate/stage_round/mutations.py "$elf" --audit ./stage-audit
```

The audit checks the public type and assumptions, runs `coqchk`, and retains
the symbol bytes and ELF digest. Each mutation binds the changed listing to
its own linked bytes. A concrete call with eight repeated key pointers exposes
a wrong index, a wrong unpack, or a load beyond the last key entry.
[Audit driver](audit.py) · [Counterexamples](coq/Counterexample.v)
