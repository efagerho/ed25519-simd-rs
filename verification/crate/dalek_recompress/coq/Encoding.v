From Coq Require Import ZArith Bool Lia Field.
From Coqprime.elliptic Require GZnZ.
From Curve25519.group Require Export PointEncoding.
From Machine Require Import memory.ByteMemory.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Import PrimeField Affine Cofactor Decompression.
From Ed25519Simd.Decode Require Import Kernels.
From Curve25519 Require Import Radix51Digits.
From Ed25519Simd.Decode Require Import Scale Power Unpack Decode.
From Ed25519Simd.Dalek Require Import FieldOps.
Local Open Scope Z_scope.
Local Notation val := (GZnZ.val prime).

Definition y_matches k flat ptr j z y :=
 let a:=unpack flat ptr j in negb(noncanonical a) && high_test (subtract_product k a z y) 0.
Lemma y_matches_ok k flat ptr j z y : checked k=true -> byte_memory flat -> (j<8)%nat ->
 split_field z -> split_field y -> value z<>0%fp ->
 (y_matches k flat ptr j z y=true <-> encoded flat ptr j mod 2^255=val (value y/value z)%fp).
Proof.
 intros C B J Zr Y NZ. set (a:=unpack flat ptr j).
 destruct(unpack_correct flat ptr j B J) as [A [E _]];fold a in A,E.
 destruct(fused_ok k a z y C A Zr Y) as [Bound [L V]]. set (h:=subtract_product k a z y) in *.
 assert (Pos:1<pack h) by (apply positive_from_low; assumption).
 unfold y_matches;fold a h. rewrite andb_true_iff,negb_true_iff,digits_canonical by apply unpack_strict.
 rewrite high_test_correct,congruent_value by (auto || lia).
 fold (value h);rewrite V,<-E. set (v:=(value y/value z)%fp).
 assert (R:0<=val v<prime) by (rewrite (GZnZ.inZnZ prime v);apply Z.mod_pos_bound;unfold prime;lia).
 assert (Lo:0<=pack a) by (rewrite E;apply Z.mod_pos_bound;lia).
 split.
 - intros [P D]. change ((value a*value z-value y)%fp=0%fp) in D. assert (Q:value a=v).
   { unfold v. replace (value y) with (value a*value z)%fp;[field;exact NZ|].
     replace (value a*value z)%fp with ((value a*value z-value y)+value y)%fp by ring.
     rewrite D;ring. }
   apply (f_equal val) in Q. change (pack a mod prime=val v) in Q;now rewrite Z.mod_small in Q by lia.
 - intro Eq;split;[lia|]. assert (Q:value a=v).
   { apply GZnZ.zirr. change (pack a mod prime=val v);rewrite Z.mod_small;lia. }
   change ((value a*value z-value y)%fp=0%fp). rewrite Q;unfold v;field;exact NZ.
Qed.

(* The slow path is selected for all eight lanes when any top digit is
   large. A lane on the fast path must itself pass the unsigned test. *)
Definition x_parity (slow:bool) h := if slow then parity_after h else Z.odd(h 0%nat).
Lemma x_parity_ok slow h : bounded h -> (slow=false -> h 4%nat<radix-1) ->
 x_parity slow h=parity(value h).
Proof.
 intros B Fast. destruct slow.
 - unfold x_parity;rewrite parity_after_ok,canonical_odd_ok by assumption;reflexivity.
 - apply low_digit_parity; auto.
Qed.

Lemma encoding_equal flat ptr j P : byte_memory flat ->
 (encoded flat ptr j=compression P <->
 encoded flat ptr j mod 2^255=val(y P) /\ Z.testbit (encoded flat ptr j) 255=parity(x P)).
Proof.
 intro B. apply compression_parts. exact (read_le_bound 32 flat (ptr+32*Z.of_nat j) B).
Qed.
