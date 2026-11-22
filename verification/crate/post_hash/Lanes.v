From Coq Require Import ZArith Lia.
From Curve25519 Require Import Radix51 Edwards.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Import Decode Limbs.
Local Open Scope Z_scope.

Definition coordinates_of (o:output) := Coordinates (Limbs.pack (ox o)) (Limbs.pack (oy o))
  (Limbs.pack (oz o)) (Limbs.pack (ot o)).
Definition octet (w:Z) i := Z.shiftr w (8*Z.of_nat i) mod 256.
Lemma octet_bit w i j : (j<8)%nat ->
 Z.testbit(octet w i)(Z.of_nat j)=Z.testbit w (8*Z.of_nat i+Z.of_nat j).
Proof. intro J;unfold octet;change 256 with (2^8).
 rewrite Z.mod_pow2_bits_low,Z.shiftr_spec by lia;f_equal;lia. Qed.

Definition component (o:output) c := match c with
 | O=>ox o | S O=>oy o | S(S O)=>oz o | _=>ot o end.
Definition words (os:nat->output) (w:nat) :=
 let row:=(w/8)%nat in component (os (w mod 8)%nat) (row/5)%nat (row mod 5)%nat.
Lemma word_cell os i j : (j<8)%nat -> cell(words os)i j=
 component (os j) (i/5)%nat (i mod 5)%nat.
Proof.
 intro J;unfold cell,words. replace ((i*8+j)/8)%nat with i by
 (apply Nat.div_unique with (r:=j);lia).
 now replace ((i*8+j) mod 8)%nat with j by (apply Nat.mod_unique with (q:=i);lia).
Qed.
Lemma word_coords os j : (j<8)%nat -> point_values (words os) j=coordinates_of(os j).
Proof.
 intro J. unfold point_values,point_from_fields,word_coordinate,field_at,coordinates_of,Limbs.pack,limbs.
 now rewrite !word_cell by exact J.
Qed.
