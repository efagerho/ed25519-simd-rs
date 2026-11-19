# Shared arithmetic proofs

This directory is the Coq namespace `ProofArithmetic`. The definitions and
proofs are independent of the field prime, scalar modulus, and assembly
programs. `Symbolic.v` relates expressions to the existing `Machine`
instruction semantics.

| File | Shared result |
| --- | --- |
| [Expressions.v](Expressions.v) | Integer expressions with exact meanings for quotient and remainder. |
| [Polynomial.v](Polynomial.v) | Normalization preserves meaning; checked coefficient identities imply exact equality or congruence for an explicit nonzero modulus. |
| [Interval.v](Interval.v) | Signed bounds and symbolic values are sound; removing a remainder requires both interval endpoints in range. Refinement hints require proofs. |
| [Symbolic.v](Symbolic.v) | Instruction expressions agree with the machine under explicit operand conditions. AND has a caller-selected mask width; IFMA stays 52-bit and wrapping arithmetic stays 64-bit. |

The field wrapper in `pow2/coq/Polynomial.v` specializes congruence to
`2^255-19`. Scalar reduction imports the general checker directly. The
routine symbolic interpreters retain their distinct load, mask-register,
and refinement policies, using the shared instruction-soundness theorem.
The cached-add bounds-only interpreter uses `Interval.abstract_bounds`
without retaining symbolic expressions.

Build and check these modules through any routine's certificate driver.
The driver compiles `machine/` first and provides both namespace mappings;
the retained audit bundle can be rebuilt using its `_CoqProject`.
