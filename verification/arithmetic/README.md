# Shared arithmetic proofs

This directory is the Coq namespace `ProofArithmetic`. The definitions and
proofs are independent of the field prime, scalar modulus, and assembly
programs and can be built using only the Coq standard library.

| File | Shared result |
| --- | --- |
| [Expressions.v](Expressions.v) | Integer expressions with exact meanings for quotient and remainder. |
| [Polynomial.v](Polynomial.v) | Normalization preserves meaning; checked coefficient identities imply exact equality or congruence for an explicit nonzero modulus. |
| [Ranges.v](Ranges.v) | Numeric bounds and their expression evaluator, with no exact-expression claim. Bound operations and positive-divisor checks are shared. |
| [Interval.v](Interval.v) | Symbolic expressions paired with numeric bounds. Erasing the expression agrees with the bounds evaluator; remainder removal requires both endpoints in range. Refinement hints require proofs. |
| [Radix.v](Radix.v) | Little-endian positional integers and a value bound for bounded digits. |

[Machine instruction translation](../machine/symbolic/Expressions.v) returns `None` for memory instructions.
Its soundness theorem requires a successful translation and proves equality
with the machine result without exceptions. Routine interpreters handle loads
and memory IFMA explicitly; their checks reject unsupported translations.

The field wrapper in `Curve25519.FieldPolynomial` specializes congruence to
`2^255-19`. Scalar reduction imports the general checker directly. The
routine symbolic interpreters retain their distinct load, mask-register,
and refinement policies, using the shared instruction-soundness theorem.
The cached-add bounds-only interpreter stores `Ranges.bounds` and uses
`Ranges.range_eval_sound`. It does not construct or discard dummy expressions.
`Interval.abstract_enclosure` proves that the symbolic evaluator produces
exactly the same bounds as the numeric evaluator.

Build and check these modules through any routine's certificate driver.
The driver compiles `machine/` first and provides both namespace mappings;
the retained audit bundle can be rebuilt using its `_CoqProject`.
