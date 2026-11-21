# Linked radix-256 ladder step

For each of eight lanes, the linked `ed25519_simd_ladder_step_ifma` wrapper
computes **`[256]P + [16]Odd + Base + Even`** when its inputs satisfy the limb
bounds and represent the named Edwards points. The result represents that
sum in XYZ in both modes. Full mode also produces a valid extended T.
Omitted-T mode writes zero to all five T vectors.

Public theorem in `Ed25519Simd.LadderStep`. [Statement](coq/Audit.v) · [Proof](coq/Object.v)

```coq
Object.assembled_ladder_step_correct : Audit.ladder_contract
```

The theorem binds the wrapper and both callees to a single linked executable.
It proves a unique modeled return to the original caller with RSP advanced
by eight, SysV saved registers restored, and bytes outside the point and
private stack preserved. Bounded inputs alone suffice for the coordinate
formulas and reduced limb bounds.

## What to audit

1. **The call targets.** In the retained `LadderStep/LinkedBytes.v` and
   manifest, match the wrapper, double4, and cached-add addresses and bytes to
   the same ELF. In `program`, follow all five calls in order. In `dispatch`,
   check that each permitted target requires an execution of that callee
   and replays its writes into the caller’s memory. The three symbols use a
   common load bias. [Wrapper and contract](coq/Audit.v) · [Callee dispatch](coq/Callees.v) · [Linked audit](audit.py)
2. **The caller and staging.** Compare `placement_ok` with the call in the outer assembly loop.
   RDI points to the in-place 1,280-byte point. RSI points to a separate,
   64-byte-aligned 3,520-byte buffer with projective Odd at offset 0, affine
   Base at 1,280, and projective Even at 2,240. RDX is the final T flag, zero
   or one. Check the stack allowance of up to 1,384 bytes below entry RSP,
   the loose XYZ bounds, and the 52-bit cache limbs. The assembly staging
   routine selects signed entries and transposes their limbs before this
   theorem starts. The staging theorem proves which source word occupies each
   row and lane of those three operands. The [full-ladder theorem](../full_ladder/README.md) composes all 32 pairs.
   [Staging theorem](../stage_round/README.md) · [Full ladder caller](../../../src/wide/avx512ifma/mul_s_base_minus_k_public.S) · [Assembly ABI](../../../src/wide/avx512ifma/ladder_step.S) · [Entry witnesses](coq/EntryTests.v)
3. **The schedule and group meaning.** Read `result_value` and `group_result`
   against `ladder_sum`. Four doublings precede the Odd addition and four more
   precede the Base addition, giving the weights 256, 16, 1, 1. The Odd
   addition may omit T because the next doubling uses only XYZ. The Base
   addition must produce T for the Even addition. Check that the initial XYZ
   represents P with nonzero Z and that each cache represents its named point
   with one nonzero scale, equal to one for the affine Base.
   [Coordinate schedule](../../curve25519/Edwards.v) · [Group interpretation](../../curve25519/group/Representation.v) · [Composition of limb bounds](coq/Schedule.v)

Apply the [crate audit procedure](../README.md#what-to-audit) to all three
symbols. The [doubling](../double4/README.md#what-to-audit) and
[cached-addition](../cached_add/README.md#what-to-audit) guides cover the two
callee contracts used here.

## Check a release executable

Use an unstripped release executable built with `--features asm` and the
[verification toolchain](../README.md#build-and-audit).
The output directory must be new.

```sh
python3 -B verification/crate/ladder_step/audit.py "$ELF" --output "$AUDIT"
python3 -B verification/crate/ladder_step/mutations.py "$ELF" --audit "$AUDIT"
```

The first command extracts each symbol's bytes and address, checks the
two existing callee theorems in distinct Coq namespaces, compiles the
ladder theorem, and runs `coqchk` on its dependency closure. The audit
directory includes the generated sources, `LadderStep/LinkedBytes.v`, the two
callee byte literals, `assumptions.txt`, and `coqchk.log`.
The audit instantiates the public theorem on concrete input memory for
both T modes and all four supported stack alignments. A separate base-point
fixture checks the group interpretation in both modes. The second command checks
an unchanged control and four mutations. One swaps the odd and base operands
in the group claim while leaving the bytes and coordinate contract intact.
Two others change both the bytes and the modeled instructions so that byte
equality succeeds before the execution proof fails.

## Proof boundaries

[`LinkedCalls.v`](../../machine/execution/LinkedCalls.v) gives the wrapper instructions
their encoding and sequencing. The wrapper and leaf refinement execute overlapping
register and stack instructions with the same [word and byte operations](../../machine/execution/WordSemantics.v).
The caller agreement theorems cover the relocated PC, registers, flags and memory. A
call pushes its actual continuation. [`Callees.v`](coq/Callees.v) admits
a return only with an execution of the linked callee's block interpreter
and a replay of its memory events. [`Calls.v`](coq/Calls.v) applies one
frame rule at all five call sites. [`Execution.v`](coq/Execution.v)
tracks the live registers, saved stack slots, and original staged memory.
The field kernels are proved in the callee theorems.

The hardware comparison includes the ladder differential and SysV ABI tests.
The [shared audit surface](../../README.md#shared-audit-surface) describes the
assumptions for applying the linked theorem to native execution.
