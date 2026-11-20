# Radix-51 field circuits

The ZIP-215 and projective small-order proofs share this checker for field
arithmetic in word circuits. Each routine supplies its decoded circuit, its
allowed input rows and a list of checkpoints. At each checkpoint,
`verify_sound` proves the stated field congruence and bounds on all five
limbs. When a zero test needs a positive representative, the checker also
proves that lower bound. [Checker and soundness theorem](Check.v) · [Word operations](Arithmetic.v)

For an audit, read the input row mapping and the final mask predicate in
the routine’s public contract. The checker discharges the intermediate
congruences and bounds. `zero_gate_result` connects the limbwise bit test
to zero modulo p, and `four_zero_bits` connects the three mask unions to
the four field roots. These results depend on the shared machine word and
field semantics. [Zero test](Zero.v) · [Mask lemmas](RootMasks.v) · [Shared trust boundary](../../README.md#shared-audit-surface)
