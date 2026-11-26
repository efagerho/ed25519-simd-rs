# SHA-512

`Spec.sha512 : list byte -> list byte` maps a single byte string to its
64 digest bytes. Its domain in FIPS 180-4 is messages shorter than `2^128`
bits. The definition uses only the Coq standard library. It builds the
padded message and all 80 schedule words in order, then folds the compression
function over the blocks. [Spec.v](Spec.v)

## What to audit

| FIPS 180-4 sections | What to compare in the definition |
| --- | --- |
| 5.1.2, 5.2.2 | The delimiter is `80` in hex. Zero bytes bring the message to 112 modulo 128 bytes. The last 16 bytes encode the original **bit** length in big-endian order. Each block has sixteen big-endian words. |
| 4.1.3, 4.2.3, 5.3.5 | Check the Boolean functions, rotation and shift counts, eight initial words, and all 80 constants in order. |
| 6.4.2 | Check the four schedule indices, additions modulo `2^64`, simultaneous update of the eight working words, addition of the incoming state after each block, and digest serialization. |

The normative reference is the Secure Hash Standard. [FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf)

Coq proves that splitting and rejoining the padded blocks preserves every
byte, that the 16-byte trailer decodes to the original bit length throughout
the standard's domain, that compression takes 80 rounds, and that the digest
has 64 bytes. Executable checks compare literal output bytes for the empty
input, `abc`, and NIST's 112-byte two-block example. [Facts.v](Facts.v) ·
[Vectors.v](Vectors.v) · [NIST worked examples](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf)

The 16-word rolling schedule and the reassociated additions in each round yield the reference compression rounds. Encoding the high and low length words separately yields the reference 16-byte trailer. [Schedule and rounds](Compression.v) · [Length trailer](LengthTrailer.v)

To check this directory on its own, run the following commands from a copy
of the directory with Coq installed.

```sh
coq_makefile -f _CoqProject -o Makefile
make
coqchk -silent -Q . SHA512 SHA512.Facts SHA512.Vectors SHA512.Compression SHA512.LengthTrailer
```

The challenge routine has its own output layout and proof obligations.
[Eight-lane challenge proof](../crate/sha512_challenge/README.md)
