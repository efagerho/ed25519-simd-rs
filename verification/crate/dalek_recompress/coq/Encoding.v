From Coq Require Import ZArith Bool Lia Field.
From Coqprime.elliptic Require GZnZ.
From Machine Require Import memory.ByteMemory.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Import PrimeField Affine Cofactor Decompression.
From Ed25519Simd.Decode Require Import Kernels Limbs Scale Power Unpack Decode.
From Ed25519Simd.Dalek Require Import FieldOps.
Local Open Scope Z_scope.
Local Notation val := (GZnZ.val prime).

Definition noncanonical h :=
 (Z.land (Z.land (h 1%nat) (h 2%nat)) (Z.land (h 3%nat) (h 4%nat)) =? radix-1) &&
 (radix-19 <=? h 0%nat).
Lemma digits_canonical h : field_bound (fun _=>radix-1) h ->
 (noncanonical h=false <-> pack h<prime).
Proof.
 intro B. assert (D:bounded h) by (intros i I;specialize(B i I);lia).
 pose proof(high_test_digits h (h 0%nat-(radix-19)) D) as H.
 unfold high_test in H. replace (radix-19+(h 0%nat-(radix-19))) with (h 0%nat) in H by ring.
 rewrite Z.eqb_refl,Bool.andb_true_r in H.
 pose proof(B 0%nat ltac:(lia));pose proof(B 1%nat ltac:(lia));pose proof(B 2%nat ltac:(lia));
 pose proof(B 3%nat ltac:(lia));pose proof(B 4%nat ltac:(lia)).
 unfold noncanonical. destruct (Z.eqb _ (radix-1)) eqn:E, (Z.leb_spec (radix-19) (h 0%nat));
 unfold pack,limbs,radix,prime in *; intuition lia.
Qed.
Definition y_matches k flat ptr j z y :=
 let a:=unpack flat ptr j in negb(noncanonical a) && high_test (subtract_product k a z y) 0.
Lemma y_matches_ok k flat ptr j z y : checked k=true -> byte_memory flat -> (j<8)%nat ->
 split_field z -> split_field y -> value z<>0%fp ->
 (y_matches k flat ptr j z y=true <-> encoded flat ptr j mod 2^255=val (value y/value z)%fp).
Proof.
 intros C B J Zr Y NZ. set (a:=unpack flat ptr j).
 destruct(unpack_correct flat ptr j B J) as [A [E _]];fold a in A,E.
 destruct(fused_ok k a z y C A Zr Y) as [Bound [L V]]. set (h:=subtract_product k a z y) in *.
 assert (Pos:1<pack h).
 { unfold pack,limbs;pose proof(Bound 1%nat ltac:(lia));pose proof(Bound 2%nat ltac:(lia));
   pose proof(Bound 3%nat ltac:(lia));pose proof(Bound 4%nat ltac:(lia));unfold radix in *;lia. }
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
 - specialize(Fast eq_refl). destruct(bounded_value _ B) as [Lo _].
   assert (Hi:pack h<prime).
   { pose proof(B 0%nat ltac:(lia));pose proof(B 1%nat ltac:(lia));pose proof(B 2%nat ltac:(lia));
     pose proof(B 3%nat ltac:(lia));unfold pack,limbs,prime,radix in *;lia. }
   change (Z.odd(h 0%nat)=Z.odd(pack h mod prime)). rewrite Z.mod_small by lia.
   unfold pack,limbs;rewrite Z.odd_add,Z.odd_mul. symmetry;apply Bool.xorb_false_r.
Qed.

Definition compress (P:point) := val(y P) + (if parity(x P) then 2^255 else 0).
(* The cache-hit screen discards a chunk only when every encoded Y is
   outside this interval. Either sign gives the same low 255 bits. *)
Lemma strict_encoding_y_range P : multiple 8 P <> identity ->
  1 < compress P mod 2^255 < prime-1.
Proof.
 intro Strong.
 assert (Range:0<=val(y P)<prime).
 { rewrite (GZnZ.inZnZ prime (y P));apply Z.mod_pos_bound;unfold prime;lia. }
 assert (Limit:prime<2^255) by (unfold prime;lia).
 assert (Packed:compress P mod 2^255=val(y P)).
 { unfold compress;destruct (parity(x P)).
   - replace (val(y P)+2^255) with (val(y P)+1*2^255) by ring.
     rewrite Z.mod_add by lia. apply Z.mod_small;lia.
   - rewrite Z.add_0_r;apply Z.mod_small;lia. }
 rewrite Packed.
 assert (Y0:y P <> 0%fp).
 { intro Y;apply Strong,eight_identity_iff;rewrite Y;ring. }
 assert (Unit:y P <> 1%fp /\ y P <> (0-1)%fp).
 { assert (Weak: y P=1%fp \/ y P=(0-1)%fp -> False).
   { intro Y. assert (Zero:on_curve 0%fp (y P)).
     { destruct Y as [-> | ->];unfold on_curve;ring. }
     assert (X:x P=0%fp).
     { eapply (unique_signed_root (parity(x P)) _ _ (y P));
       [apply on_edwards|exact Zero|right;reflexivity|left;reflexivity]. }
     apply Strong,eight_identity_iff;rewrite X;ring. }
   tauto. }
 destruct Unit as [Y1 Ym].
 assert (ValEq:forall a b:fp, val a=val b -> a=b) by (intros [a A] [b B];apply GZnZ.zirr).
 assert (val(y P)<>0) by (intro E;apply Y0,ValEq;exact E).
 assert (val(y P)<>1) by (intro E;apply Y1,ValEq;exact E).
 assert (val(y P)<>prime-1) by (intro E;apply Ym,ValEq;exact E).
 lia.
Qed.

Lemma encoding_equal flat ptr j P : byte_memory flat ->
 (encoded flat ptr j=compress P <->
 encoded flat ptr j mod 2^255=val(y P) /\ Z.testbit (encoded flat ptr j) 255=parity(x P)).
Proof.
 intro B. pose proof (read_le_bound 32 flat (ptr+32*Z.of_nat j) B) as Bound.
 fold (encoded flat ptr j) in Bound. set (w:=encoded flat ptr j) in *.
 assert (Range:0<=val(y P)<prime) by (rewrite(GZnZ.inZnZ prime (y P));apply Z.mod_pos_bound;unfold prime;lia).
 change (0<=w<2^256) in Bound. assert (Hi:0<=w/2^255<2) by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 pose proof(Z.div_mod w (2^255) ltac:(discriminate)).
 pose proof(Z.mod_pos_bound w (2^255) ltac:(lia)).
 replace (Z.testbit w 255) with (Z.odd (w/2^255)) by (rewrite <-Z.shiftr_div_pow2 by lia;change (Z.testbit (Z.shiftr w 255) 0=Z.testbit w 255);rewrite Z.shiftr_spec by lia;reflexivity). unfold compress. destruct(parity(x P));
 destruct (Z.eq_dec (w/2^255) 0) as [Q|N]; try assert (Q:w/2^255=1) by lia;
 rewrite Q; cbn [Z.odd];unfold prime in *;intuition lia.
Qed.
