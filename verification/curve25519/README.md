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
| [Torsion.v](Torsion.v) | The determinant, mixed-subtraction numerators, and four field zero tests for one lane of the ZIP-215 equation check. |
| [SmallOrderFilter.v](SmallOrderFilter.v) | Every exact small-order root passes the 64-bit rejection filter for bounded projective X and Y. |
| [PrimeField.v](group/PrimeField.v), [Affine.v](group/Affine.v) | The prime field and the affine Edwards group law. |
| [Representation.v](group/Representation.v) | How XYZ, extended, and cached coordinates represent group elements. |
| [Cofactor.v](group/Cofactor.v) | The Edwards group meaning of the projective small-order check, mixed-subtraction torsion check and determinant shortcut. |

The theorem `ladder_represents` connects the coordinate schedule to the group
sum `[256]P + [16]Odd + Base + Even`. When the routine omits T, the result
uses only X, Y, and Z. The group proofs use Coqprime. [Representation theorem](group/Representation.v)

For ZIP-215, start at `torsion_check_correct`. Given valid extended
representations of `P` and `R` with `Z_R = 1` in the field, the four
zero tests accept exactly when `[8](P − R)` is the identity. The proof
shows that the two computed numerators have the same nonzero scale as
the affine coordinates of `P − R`. [Integer equations](Torsion.v) · [Group theorem](group/Cofactor.v)

The shortcut has a weaker input requirement. For any two valid XYZ
representations, `torsion_shortcut_iff` proves that
`X_P Y_R − Y_P X_R = 0` modulo the field prime exactly when
`[2](P − R)` is the identity. This includes equal points represented at
different scales. If the determinant vanishes in every lane, each lane
therefore satisfies the ZIP-215 equation. The linked assembly certificate
connects both branch outcomes to the returned mask. [Shortcut theorem](group/Cofactor.v) · [Assembly theorem](../crate/torsion/README.md)
