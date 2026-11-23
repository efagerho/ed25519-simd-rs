(* SHA-512 on byte strings (FIPS 180-4). *)
From Coq Require Import NArith List Strings.Byte PeanoNat.
Import ListNotations.
Local Open Scope N_scope.

(* Sections 5.1.2 and 5.2.2. The standard's domain is bit_length < 2^128. *)
Definition bit_length (message : list byte) := 8 * N.of_nat (length message).

Definition low_byte (x : N) : byte :=
  match Byte.of_N (x mod 256) with Some b => b | None => x00 end.

Fixpoint big_endian (width : nat) (x : N) : list byte :=
  match width with
  | O => []
  | S n => big_endian n (x / 256) ++ [low_byte x]
  end.

Definition read_big_endian (bytes : list byte) :=
  fold_left (fun acc b => 256 * acc + Byte.to_N b) bytes 0.

Definition zero_count n := (127 - ((n + 16) mod 128))%nat.

Definition pad (message : list byte) : list byte :=
  message ++ [x80] ++ repeat x00 (zero_count (length message)) ++
  big_endian 16 (bit_length message).

Fixpoint chunks {A} (count width : nat) (xs : list A) : list (list A) :=
  match count with
  | O => []
  | S n => firstn width xs :: chunks n width (skipn width xs)
  end.

(* Section 4.1.3. All word sums are reduced modulo 2^64. *)
Definition word x := x mod 2^64.
Definition rotate_right x n :=
  N.lor (N.shiftr x n) (word (N.shiftl x (64 - n))).
Definition xor3 x y z := N.lxor (N.lxor x y) z.
Definition ch x y z := N.lxor (N.land x y) (N.land (N.lnot x 64) z).
Definition maj x y z := xor3 (N.land x y) (N.land x z) (N.land y z).
Definition sum0 x := xor3 (rotate_right x 28) (rotate_right x 34) (rotate_right x 39).
Definition sum1 x := xor3 (rotate_right x 14) (rotate_right x 18) (rotate_right x 41).
Definition sigma0 x := xor3 (rotate_right x 1) (rotate_right x 8) (N.shiftr x 7).
Definition sigma1 x := xor3 (rotate_right x 19) (rotate_right x 61) (N.shiftr x 6).

Record state := State { a : N; b : N; c : N; d : N; e : N; f : N; g : N; h : N }.

(* Sections 5.3.5 and 4.2.3, in standard order. *)
Definition initial := State
  0x6a09e667f3bcc908 0xbb67ae8584caa73b 0x3c6ef372fe94f82b 0xa54ff53a5f1d36f1
  0x510e527fade682d1 0x9b05688c2b3e6c1f 0x1f83d9abfb41bd6b 0x5be0cd19137e2179.

Definition constants : list N :=
  [0x428a2f98d728ae22; 0x7137449123ef65cd; 0xb5c0fbcfec4d3b2f; 0xe9b5dba58189dbbc;
   0x3956c25bf348b538; 0x59f111f1b605d019; 0x923f82a4af194f9b; 0xab1c5ed5da6d8118;
   0xd807aa98a3030242; 0x12835b0145706fbe; 0x243185be4ee4b28c; 0x550c7dc3d5ffb4e2;
   0x72be5d74f27b896f; 0x80deb1fe3b1696b1; 0x9bdc06a725c71235; 0xc19bf174cf692694;
   0xe49b69c19ef14ad2; 0xefbe4786384f25e3; 0x0fc19dc68b8cd5b5; 0x240ca1cc77ac9c65;
   0x2de92c6f592b0275; 0x4a7484aa6ea6e483; 0x5cb0a9dcbd41fbd4; 0x76f988da831153b5;
   0x983e5152ee66dfab; 0xa831c66d2db43210; 0xb00327c898fb213f; 0xbf597fc7beef0ee4;
   0xc6e00bf33da88fc2; 0xd5a79147930aa725; 0x06ca6351e003826f; 0x142929670a0e6e70;
   0x27b70a8546d22ffc; 0x2e1b21385c26c926; 0x4d2c6dfc5ac42aed; 0x53380d139d95b3df;
   0x650a73548baf63de; 0x766a0abb3c77b2a8; 0x81c2c92e47edaee6; 0x92722c851482353b;
   0xa2bfe8a14cf10364; 0xa81a664bbc423001; 0xc24b8b70d0f89791; 0xc76c51a30654be30;
   0xd192e819d6ef5218; 0xd69906245565a910; 0xf40e35855771202a; 0x106aa07032bbd1b8;
   0x19a4c116b8d2d0c8; 0x1e376c085141ab53; 0x2748774cdf8eeb99; 0x34b0bcb5e19b48a8;
   0x391c0cb3c5c95a63; 0x4ed8aa4ae3418acb; 0x5b9cca4f7763e373; 0x682e6ff3d6b2b8a3;
   0x748f82ee5defb2fc; 0x78a5636f43172f60; 0x84c87814a1f0ab72; 0x8cc702081a6439ec;
   0x90befffa23631e28; 0xa4506cebde82bde9; 0xbef9a3f7b2c67915; 0xc67178f2e372532b;
   0xca273eceea26619c; 0xd186b8c721c0c207; 0xeada7dd6cde0eb1e; 0xf57d4f7fee6ed178;
   0x06f067aa72176fba; 0x0a637dc5a2c898a6; 0x113f9804bef90dae; 0x1b710b35131c471b;
   0x28db77f523047d84; 0x32caab7b40c72493; 0x3c9ebe0a15c9bebc; 0x431d67c49c100d4c;
   0x4cc5d4becb3e42b6; 0x597f299cfc657e2a; 0x5fcb6fab3ad6faec; 0x6c44198c4a475817].

(* Section 6.4.2. Build W[0..79] in order. Before extend t the list
   contains exactly W[0..t-1], so all four lookups refer to earlier words. *)
Definition extend (ws : list N) (t : nat) :=
  let prev := fun i => nth (t - i) ws 0 in
  ws ++ [word (sigma1 (prev 2%nat) + prev 7%nat + sigma0 (prev 15%nat) + prev 16%nat)].

Definition schedule (block : list byte) :=
  let first16 := map read_big_endian (chunks 16 8 block) in
  fold_left extend (seq 16 64) first16.

Definition round (s : state) (kw : N * N) :=
  let '(k, w) := kw in
  let t1 := h s + sum1 (e s) + ch (e s) (f s) (g s) + k + w in
  let t2 := sum0 (a s) + maj (a s) (b s) (c s) in
  State (word (t1 + t2)) (a s) (b s) (c s)
        (word (d s + t1)) (e s) (f s) (g s).

Definition compress (s : state) (block : list byte) :=
  let v := fold_left round (combine constants (schedule block)) s in
  State (word (a s + a v)) (word (b s + b v)) (word (c s + c v)) (word (d s + d v))
        (word (e s + e v)) (word (f s + f v)) (word (g s + g v)) (word (h s + h v)).

Definition digest_bytes (s : state) :=
  flat_map (big_endian 8) [a s; b s; c s; d s; e s; f s; g s; h s].

Definition sha512 (message : list byte) : list byte :=
  let padded := pad message in
  digest_bytes (fold_left compress (chunks (length padded / 128) 128 padded) initial).
