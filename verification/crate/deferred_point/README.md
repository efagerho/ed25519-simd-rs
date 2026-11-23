# Deferred carries in the public double-scalar ladder

Audit **`Ed25519Simd.FullLadder.Object.assembled_full_ladder_correct`** for an ELF with the private doubling and affine-add entries. In each of eight lanes the complete ladder returns an Edwards point representing **[s]B − [k]A**. The caller supplies valid signed-digit buffers, tables representing the specified multiples, and the stated memory placement. Both final T modes return reduced limbs. Extended mode returns a valid T coordinate. XYZ mode writes zero to all five T limbs. [Public statement](../full_ladder/coq/Audit.v) · [Digit and table premises](../full_ladder/coq/Operands.v)

## What to audit

1. Match the seven symbol addresses, sizes and bytes in the manifest to the executable. The two private entry stubs each share a body with a public symbol. Check that the public PC is at its actual offset within that image and that all relative calls resolve to the intended entries. Coq re-encodes both complete point images and checks their layouts. [ELF listing](listing.py) · [Entry adapters](coq/Concrete.v) · [Linked dispatch](coq/StepCallees.v)
2. Check the limb bounds on each handoff. The private doubling and affine addition can return X and Y limbs as large as `300 * 2^52 − 1`. Their Z and T retain the ordinary reduced bounds. The next cached addition accepts these X/Y inputs. The arithmetic proof compares all 20 stored rows with the proved field formulas. For the comparison it carries X/Y in the proof and proves this preserves their residues. A separate interval proof bounds the actual words *before* this carry. [Bounds and formulas](../PointResults.v) · [Raw limb bounds](coq/RawBounds.v) · [Comparison carry](coq/Normalize.v)
3. Check the five calls of one ladder step, the special top-digit round and the 31 remaining rounds. The private affine entry sets both flags internally. The final public addition receives the caller’s T flag. The step theorem covers concrete calls and byte memory. The full-ladder theorem follows the outer control flow with a symbolic stack and passes the live accumulator and staged words between native calls. Read the outer execution model and its placement premises alongside the mathematical conclusion. [Step statement](../ladder_step/coq/Audit.v) · [Outer execution model](../full_ladder/README.md#what-to-audit) · [Shared machine and memory assumptions](../../README.md#shared-audit-surface)

The checked-in production assembly uses the public entries. The experimental assembly can be reproduced by applying the fixture patch to copies of those sources. The audit takes its candidate bytes from the supplied ELF. The reference `double4.S` and `add_cached.S` retained as sources provide the comparison programs. [Fixture patch](tests/private-entries.patch) · [Trace-equivalence soundness](../../machine/execution/TraceEquivalence.v)

## Replay

With the repository’s Coq dependencies installed, run the following from its root. Use a fresh evidence directory. The manifest identifies the ELF, proof sources, theorem type, assumptions and `coqchk` result.

```sh
python3 -B verification/crate/deferred_point/audit.py /path/to/candidate-elf \
  --output ./deferred-ladder-audit
```

To check the point ABI on its own, select `--component deferred_point`. Its theorem covers both doubling entries, the private affine entry, and all four public addition modes. It includes the input read extent, complete output writes, stack and saved-register restoration, byte replay, and the coordinate equations for the same return. [Point statement](coq/Audit.v) · [Concrete contract](coq/Concrete.v)

To reproduce the candidate and check a premature skipped carry, a shortened doubling loop and an incorrect IFMA half, use the following commands.

```sh
python3 -B verification/crate/deferred_point/tests/fixture.py ./deferred.elf
python3 -B verification/crate/deferred_point/audit.py ./deferred.elf --output ./fixture-audit
python3 -B verification/crate/deferred_point/tests/mutations.py ./deferred.elf --audit ./fixture-audit
```

Each mutation is applied to a temporary ELF. Coq first checks the changed bytes and instruction layout. The dispatch proof rejects the two loop changes. The output-equivalence proof rejects the incorrect IFMA instruction.
