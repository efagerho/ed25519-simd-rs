# Curve25519 mathematics

The `Curve25519` Coq library defines the mathematics shared by the assembly
proofs. It uses the [general arithmetic library](../arithmetic/README.md)
and can be checked independently of the machine model.

| Files | What they define or prove |
| --- | --- |
| [Field.v](Field.v), [FieldPolynomial.v](FieldPolynomial.v) | Field congruence modulo `2^255 - 19` and the polynomial checker specialized to that modulus. |
| [Radix51.v](Radix51.v) | The value and bounds of a field element represented by five radix-51 limbs. |
| [Scalar.v](Scalar.v) | The scalar order `L` and canonical reduction modulo `L`. |
| [Edwards.v](Edwards.v) | The coordinate formulas for doubling, cached addition, and the ladder step. |
| [PrimeField.v](group/PrimeField.v), [Affine.v](group/Affine.v) | The prime field and the affine Edwards group law. |
| [Representation.v](group/Representation.v) | How XYZ, extended, and cached coordinates represent group elements. |

The theorem `ladder_represents` connects the coordinate schedule to the group
sum `[256]P + [16]Odd + Base + Even`. When the routine omits T, the result
uses only X, Y, and Z. The group proofs use Coqprime. [Representation theorem](group/Representation.v)
