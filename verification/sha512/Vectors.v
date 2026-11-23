From Coq Require Import List Strings.Byte Strings.String.
From SHA512 Require Import Spec.
Import ListNotations.
Local Open Scope string_scope.

(* Expected values are literal digest bytes, independent of the encoder.
   The one- and two-block examples are from NIST's SHA-512 worked examples. *)

Example sha512_empty :
  sha512 [] =
  [xcf; x83; xe1; x35; x7e; xef; xb8; xbd;
   xf1; x54; x28; x50; xd6; x6d; x80; x07;
   xd6; x20; xe4; x05; x0b; x57; x15; xdc;
   x83; xf4; xa9; x21; xd3; x6c; xe9; xce;
   x47; xd0; xd1; x3c; x5d; x85; xf2; xb0;
   xff; x83; x18; xd2; x87; x7e; xec; x2f;
   x63; xb9; x31; xbd; x47; x41; x7a; x81;
   xa5; x38; x32; x7a; xf9; x27; xda; x3e].
Proof. vm_compute. reflexivity. Qed.

Example sha512_abc :
  sha512 (list_byte_of_string "abc") =
  [xdd; xaf; x35; xa1; x93; x61; x7a; xba;
   xcc; x41; x73; x49; xae; x20; x41; x31;
   x12; xe6; xfa; x4e; x89; xa9; x7e; xa2;
   x0a; x9e; xee; xe6; x4b; x55; xd3; x9a;
   x21; x92; x99; x2a; x27; x4f; xc1; xa8;
   x36; xba; x3c; x23; xa3; xfe; xeb; xbd;
   x45; x4d; x44; x23; x64; x3c; xe8; x0e;
   x2a; x9a; xc9; x4f; xa5; x4c; xa4; x9f].
Proof. vm_compute. reflexivity. Qed.

Example sha512_two_blocks :
  sha512 (list_byte_of_string
    ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
     "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")) =
  [x8e; x95; x9b; x75; xda; xe3; x13; xda;
   x8c; xf4; xf7; x28; x14; xfc; x14; x3f;
   x8f; x77; x79; xc6; xeb; x9f; x7f; xa1;
   x72; x99; xae; xad; xb6; x88; x90; x18;
   x50; x1d; x28; x9e; x49; x00; xf7; xe4;
   x33; x1b; x99; xde; xc4; xb5; x43; x3a;
   xc7; xd3; x29; xee; xb6; xdd; x26; x54;
   x5e; x96; xe5; x5b; x87; x4b; xe9; x09].
Proof. vm_compute. reflexivity. Qed.
