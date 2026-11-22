From Coq Require Import ZArith Znumtheory Bool Lia.
From Machine Require Import isa.X86 isa.Shift memory.ByteMemory.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Import Limbs.
Local Open Scope Z_scope.

(* Lane indices in four consecutive 64-byte loads. VSHUFI64X2 selects
   128-bit blocks, VPERMT2Q selects qwords from the concatenated sources. *)
Definition shuffle (a b:nat->nat) (imm j:nat) :=
 let block:=(j/2)%nat in let src:=(imm/4^block mod 4*2+j mod 2)%nat in
 if Nat.ltb block 2 then a src else b src.
Definition load_index (row j:nat) := (8*row+j)%nat.
Definition transpose (word lane:nat) :=
 let imm:=if Nat.ltb word 2 then 136%nat else 221%nat in
 let a:=shuffle (load_index 0) (load_index 1) imm in
 let b:=shuffle (load_index 2) (load_index 3) imm in
 let index:=(2*lane+word mod 2)%nat in
 if Nat.ltb index 8 then a index else b (index mod 8)%nat.
Lemma transpose_ok w j : (w<4)%nat -> (j<8)%nat -> transpose w j=(4*j+w)%nat.
Proof. intros W J;destruct w as [|[|[|[|w]]]];try lia;
 do 8 (destruct j;[reflexivity|]);lia. Qed.
Definition qword flat base w j := read_word flat (base+8*Z.of_nat(transpose w j)).
Definition masked a := Z.land a (Z.ones 51).
Definition splice a b right left := masked (Z.lor (vpsrlq a right) (vpsllq b left)).
Definition unpack flat base lane :=
 let w n:=qword flat base n lane in
 five (masked(w 0%nat)) (splice (w 0%nat) (w 1%nat) 51 13)
  (splice (w 1%nat) (w 2%nat) 38 26) (splice (w 2%nat) (w 3%nat) 25 39)
  (masked(vpsrlq (w 3%nat) 12)).

Lemma unpack_strict flat ptr j : field_bound (fun _=>radix-1) (unpack flat ptr j).
Proof.
 assert (M:forall z,0<=masked z<=radix-1).
 { intro;unfold masked;rewrite Z.land_ones by lia. pose proof(Z.mod_pos_bound z radix ltac:(unfold radix;lia)).
   change (2^51) with radix;lia. }
 intros [|[|[|[|i]]]] H; apply M.
Qed.

Definition sign flat base lane := Z.testbit (qword flat base 3 lane) 63.
Definition encoded flat base lane := read_le 32 flat (base+32*Z.of_nat lane).
Definition slice z offset width := (Z.shiftr z offset) mod 2^width.

Lemma qword_ok flat base w j : byte_memory flat ->
 (w<4)%nat -> (j<8)%nat -> qword flat base w j=slice (encoded flat base j) (64*Z.of_nat w) 64.
Proof.
 intros B W J. unfold qword,slice. rewrite transpose_ok by assumption.
 rewrite Z.shiftr_div_pow2 by lia. apply read_word_encoded. intros k K.
 unfold FlatMemory.word_byte. rewrite Z.div_div by (try apply Z.pow_nonzero;try apply Z.pow_pos_nonneg;lia).
 rewrite <-Z.pow_add_r by lia. replace (64*Z.of_nat w+8*k) with (8*(8*Z.of_nat w+k)) by ring.
 pose proof (read_le_byte 32 flat (base+32*Z.of_nat j) (Z.to_nat (8*Z.of_nat w+k)) B ltac:(lia)) as E.
 rewrite Z2Nat.id in E by lia. unfold encoded. unfold FlatMemory.word_byte in E. rewrite E.
 f_equal;lia.
Qed.

Local Lemma splice_slice z offset (r l:nat) : (r+l=64)%nat -> (0<=offset) ->
 splice (slice z offset 64) (slice z (offset+64) 64) r l = slice z (offset+Z.of_nat r) 51.
Proof.
 intros Total O. unfold splice,masked,vpsrlq,vpsllq,low64,slice. rewrite !Z.land_ones by lia.
 apply Z.bits_inj;intro i. destruct (Z_lt_ge_dec i 0);[rewrite !Z.testbit_neg_r by lia;reflexivity|].
 rewrite !Z.testbit_mod_pow2 by lia. destruct (i <? 51) eqn:I;[apply Z.ltb_lt in I|reflexivity].
 cbn [andb]. rewrite Z.lor_spec,Z.shiftr_spec,Z.testbit_mod_pow2,Z.testbit_mod_pow2 by lia.
 rewrite Z.shiftl_spec by lia. destruct (Z_lt_ge_dec i (Z.of_nat l)).
 - rewrite (Z.testbit_neg_r _ (i-Z.of_nat l)) by lia.
   rewrite (proj2(Z.ltb_lt (i+Z.of_nat r) 64) ltac:(lia)), Bool.andb_false_r, Bool.orb_false_r. cbn [andb].
   rewrite !Z.shiftr_spec by lia. f_equal;lia.
 - rewrite (proj2(Z.ltb_ge (i+Z.of_nat r) 64) ltac:(lia)), (proj2(Z.ltb_lt i 64) ltac:(lia)).
   cbn [andb orb]. rewrite Z.testbit_mod_pow2 by lia.
   rewrite (proj2(Z.ltb_lt (i-Z.of_nat l) 64) ltac:(lia));cbn [andb]. rewrite !Z.shiftr_spec by lia. f_equal;lia.
Qed.
Lemma unpack_correct flat base j : byte_memory flat -> (j<8)%nat ->
 let z:=encoded flat base j in
 split_field (unpack flat base j) /\ pack(unpack flat base j)=z mod 2^255 /\
 sign flat base j=Z.testbit z 255.
Proof.
 intros B J z. unfold unpack,sign. rewrite !qword_ok by (assumption || lia). fold z.
 change (64*Z.of_nat 0) with 0. change (64*Z.of_nat 1) with (0+64).
 change (64*Z.of_nat 2) with ((0+64)+64). change (64*Z.of_nat 3) with (((0+64)+64)+64).
 rewrite !splice_slice by lia. unfold slice,masked,vpsrlq.
 rewrite !Z.land_ones, Z.mod_pow2_bits_low, Z.shiftr_spec by lia.
 rewrite !Z.shiftr_div_pow2 by lia.
 change (0+Z.of_nat 51) with 51. change (0+64+Z.of_nat 38) with 102.
 change (0+64+64+Z.of_nat 25) with 153. change (0+64+64+64) with 192.
 rewrite Z.div_1_r. change (2^51) with radix. change (2^Z.of_nat 12) with 4096.
 rewrite <- (Zmod_div_mod radix (2^64) z) by (unfold radix; first [lia|exists 8192;reflexivity]).
 assert (Top: (z/2^192 mod 2^64/4096) mod radix = (z/2^204) mod radix).
 { pose proof (Z.div_mod (z/2^192) (2^64) ltac:(discriminate)) as D.
   pose proof (Z.div_mod (z/2^192 mod 2^64) 4096 ltac:(discriminate)) as E.
   pose proof (Z.mod_pos_bound (z/2^192 mod 2^64) 4096 ltac:(lia)).
   pose proof (Z.div_mod z (2^192) ltac:(discriminate)).
   pose proof (Z.mod_pos_bound z (2^192) ltac:(lia)).
   pose proof (Z.div_mod (z/2^192 mod 2^64 /4096) radix ltac:(unfold radix;discriminate)).
   pose proof (Z.div_mod (z/2^204) radix ltac:(unfold radix;discriminate)).
   pose proof (Z.mod_pos_bound (z/2^192 mod 2^64 /4096) radix ltac:(unfold radix;lia)).
   pose proof (Z.mod_pos_bound (z/2^204) radix ltac:(unfold radix;lia)).
   pose proof (Z.div_mod z (2^204) ltac:(discriminate)).
   pose proof (Z.mod_pos_bound z (2^204) ltac:(lia)).
   unfold radix in *;lia. }
 rewrite Top. assert (R:forall a, 0<=a mod radix<radix) by (intro;apply Z.mod_pos_bound;unfold radix;lia).
 split.
 - assert (Small:forall a, 0<=a mod radix<=split-1) by (intro a; specialize(R a);unfold radix,split in *;lia).
   intros [|[|[|[|i]]]] Bound;apply Small.
 - split;[|reflexivity]. unfold pack,limbs,five.
   pose proof (fun a=>Z.div_mod a radix ltac:(unfold radix;discriminate)) as F.
   pose proof (F z);pose proof (F (z/2^51));pose proof(F(z/2^102));pose proof(F(z/2^153));pose proof(F(z/2^204)).
   repeat rewrite Z.div_div in * by (unfold radix; first [apply Z.pow_nonzero;lia|lia]).
   change (z/radix) with (z/2^51) in *.
   change (2^51*radix) with (2^102) in *. change (2^102*radix) with (2^153) in *.
   change (2^153*radix) with (2^204) in *. change (2^204*radix) with (2^255) in *.
   pose proof(Z.div_mod z (2^255) ltac:(discriminate)). unfold radix in *;lia.
Qed.
