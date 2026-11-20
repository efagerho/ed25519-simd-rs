# Linked radix-256 ladder step

The public theorem is `Ed25519Simd.LadderStep.Object.assembled_ladder_step_correct`. Read
[`ladder_contract`](coq/Audit.v) for the statement and
[`ladder_sum` and `ladder_represents`](../../curve25519/group/Representation.v)
for its group-level meaning. The theorem
binds the wrapper and both callees to the bytes of one linked x86-64 ELF.
All three symbols may be relocated by the same load bias.

Given a point, three staged cached operands, and their alignment and limb
bounds, the wrapper executes this [coordinate schedule](../../curve25519/Edwards.v) in each of eight lanes.

1. Double four times and add the odd projective operand, omitting T.
2. Double four times and add the affine base operand, computing T.
3. Add the even projective operand, computing T when requested.

If a lane's inputs represent Edwards points `P`, `Odd`, `Base`, and `Even`,
its output represents **`[256]P + [16]Odd + Base + Even`**. The input
point needs only valid X, Y, Z. Each cache must encode its named point
with one nonzero scale, equal to one for the affine base cache.
The output has nonzero Z and the correct X/Z and Y/Z in both modes.
Full mode also proves T/Z = (X/Z)(Y/Z). With T omitted, the assembly
writes literal zero to all five T limbs.

The proof uses the [affine Edwards addition law](../../curve25519/group/Affine.v)
over the [concrete prime field](../../curve25519/group/PrimeField.v). It proves
that both addition denominators are nonzero for all on-curve points, including
torsion points. The coordinate congruences and reduced limb bounds also hold
for bounded inputs with no curve interpretation.
Every modeled run returns to the original return address with the same
result. The SysV callee-saved registers are restored and every byte outside
the point and the private stack is preserved, including the staged operands.
The contract starts at the staged bytes. Rust digit selection, cache staging,
and the outer ladder loop remain separate verification targets.

## Check a release executable

Use an unstripped release executable built with `--features asm` and the
[verification toolchain](../../README.md#build-with-or-without-the-proof).
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
their encoding and execution on word registers and flat byte memory. A
call pushes its actual continuation. [`Callees.v`](coq/Callees.v) admits
a return only with an execution of the linked callee's block interpreter
and a replay of its memory events. [`Calls.v`](coq/Calls.v) applies one
frame rule at all five call sites. [`Execution.v`](coq/Execution.v)
tracks the live registers, saved stack slots, and original staged memory.
The field kernels are proved in the callee theorems.

The trusted interpretation includes extraction of bytes and symbol addresses
from the ELF and the machine model's correspondence to x86. Instruction
images are immutable and separate from data memory. The hardware comparison
includes the ladder differential and SysV ABI tests. Independent ISA
refinement for this instruction subset remains open.
