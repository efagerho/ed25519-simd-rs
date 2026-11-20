"""Independent field and representation contract for paired exponentiation."""

RADIX = 2**51
P = 2**255 - 19
EXPONENT = (P - 5) // 8
INPUT_MAX = (2**52 - 1,) * 5
OUTPUT_MAX = (RADIX - 1, RADIX + 511, RADIX - 1, RADIX - 1, RADIX - 1)


def integer(limbs):
    return sum(limb * RADIX**i for i, limb in enumerate(limbs))


def field_result(input_limbs):
    """Executable specification for one lane of either field."""
    return pow(integer(input_limbs), EXPONENT, P)
