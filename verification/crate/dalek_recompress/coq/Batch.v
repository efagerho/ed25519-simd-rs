From Coq Require Import ZArith List Bool Lia Field.
From Machine Require Import memory.ByteMemory.
From Curve25519 Require Import Field Edwards Radix51.
From Curve25519.group Require Import PrimeField Affine Representation Decompression.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Import Kernels Power Limbs Unpack Decode.
From Ed25519Simd.Dalek Require Import FieldOps Encoding Masks.
Local Open Scope Z_scope.

Definition point_words flat base i word := read_word flat (base+1280*Z.of_nat i+8*Z.of_nat word).
Definition coord words (row:nat) j d := cell words (row+d)%nat j.
Definition coord_bounds words := forall r j,(r<15)%nat -> (j<8)%nat -> 0<=cell words r j<split.
Definition valid_chunk words (P:nat->point) := coord_bounds words /\
 forall j,(j<8)%nat -> represents_xyz (point_values words j) (P j).

Section Batch.
Variable k:kernels.
Variable flat:Z->Z.
Variables points encodings:Z.
Variable small:nat->option Z.
Let words:=point_words flat points.
Definition ptr i := encodings+256*Z.of_nat i.
Definition xx i := coord (words i) 0.
Definition yy i := coord (words i) 5.
Definition zz i := coord (words i) 10.
Definition flags i j := y_matches k flat (ptr i) j (zz i j) (yy i j).
Definition signs i j := sign flat (ptr i) j.
Definition vecmul (a b:nat->Power.field) j := mul k (a j) (b j).
Fixpoint prefix i := match i with
 | O=>zz O | S t=>vecmul (zz i) (prefix t) end.
Fixpoint any_y n := match n with O=>0 | S i=>Z.lor (any_y i) (byte(flags i)) end.
Definition affine_x i reciprocal := vecmul (xx i) reciprocal.
Definition parities (a:nat->Power.field) :=
 let slow:=existsb (fun j=>radix-1 <=? a j 4%nat) (seq 0 8) in
 fun j=>x_parity slow (a j).
Definition score_x (a:nat->Power.field) (sg ys:nat->bool) (called:option Z) previous :=
 let m:=score_mask (byte(parities a)) (byte sg) (byte ys) in
 if m =? 0 then Some (Z.shiftl previous 8)
 else option_map (append_mask previous m) called.
Definition score i inv previous := score_x (affine_x i inv) (signs i) (flags i) (small i) previous.
Fixpoint backward n acc previous := match n with
 | O=>Some previous
 | S i=>let inv:=match i with O=>acc | S t=>vecmul (prefix t) acc end in
   match score i inv previous with None=>None | Some next=>
   backward i (vecmul (zz i) acc) next end end.
Definition returned n := match n with O=>Some 0 | S last=>
 if any_y n =? 0 then Some 0 else backward n (fun j=>inverse k (prefix last j)) 0 end.

Variables (P:nat->nat->point) (masks:nat->Z).
Definition expected i j := (encoded flat (ptr i) j =? compress (P i j)) &&
 negb(Z.testbit (masks i) (Z.of_nat j)).
Fixpoint packed n hi := match n with O=>hi | S i=>packed i (push hi (expected i)) end.

Hypotheses (F:checked k=true) (K:forall op,verified k op=true) (Bytes:byte_memory flat).
Variable total:nat.
Hypotheses (Points:forall i,(i<total)%nat -> valid_chunk(words i)(P i))
 (Small:forall i,(i<total)%nat -> small i=Some(masks i) /\ 0<=masks i<256).

Local Lemma coordinates i j : (i<total)%nat -> (j<8)%nat ->
 split_field(xx i j) /\ split_field(yy i j) /\ split_field(zz i j) /\
 value(zz i j)<>0%fp /\ value(xx i j)=(x(P i j)*value(zz i j))%fp /\
 value(yy i j)=(y(P i j)*value(zz i j))%fp.
Proof.
 intros I J. destruct(Points i I) as [B Rep]. specialize(Rep j J).
 split;[intros d D;specialize(B (0+d)%nat j ltac:(lia) J);unfold xx,coord;lia|].
 split;[intros d D;specialize(B (5+d)%nat j ltac:(lia) J);unfold yy,coord;lia|].
 split;[intros d D;specialize(B (10+d)%nat j ltac:(lia) J);unfold zz,coord;lia|]. exact Rep.
Qed.
Local Lemma prefix_ok i j : (i<total)%nat -> (j<8)%nat ->
 split_field(prefix i j) /\ value(prefix i j)<>0%fp.
Proof.
 intros I J;induction i as [|t IH];destruct(coordinates _ _ I J) as [_ [_ [Zr [NZ _]]]].
 - auto.
 - destruct(IH ltac:(lia)) as [B N]. destruct(mul_ok _ _ _ (K Multiply) Zr B) as [D [_ E]].
   split;[apply bounded_split,D|]. change (value(mul k (zz (S t) j) (prefix t j))<>0%fp);rewrite E;now apply mul_nonzero.
Qed.
Local Lemma flag_correct i j : (i<total)%nat -> (j<8)%nat ->
 (flags i j=true <-> encoded flat (ptr i) j mod 2^255=GZnZ.val prime (y(P i j))).
Proof.
 intros I J. destruct(coordinates _ _ I J) as [_ [Y [Zr [NZ [_ E]]]]].
 unfold flags;rewrite y_matches_ok by assumption. rewrite E.
 replace ((y(P i j)*value(zz i j))/value(zz i j))%fp with (y(P i j)) by (field;exact NZ).
 reflexivity.
Qed.
Local Lemma score_correct i inv hi : (i<total)%nat ->
 (forall j,(j<8)%nat -> split_field(inv j) /\ value(inv j)=(1/value(zz i j))%fp) ->
 score i inv hi=Some(push hi (expected i)).
Proof.
 intros I Inv. destruct(Small i I) as [Run Range].
 assert (XP:forall j,(j<8)%nat -> parities(affine_x i inv) j=parity(x(P i j))).
 { intros j J. destruct(coordinates _ _ I J) as [X [_ [_ [NZ [V _]]]]].
   destruct(Inv j J) as [B E]. destruct(mul_ok _ _ _ (K Multiply) X B) as [D [_ A]].
   unfold parities. rewrite x_parity_ok.
   - unfold affine_x,vecmul. rewrite A,V,E. f_equal;field;exact NZ.
   - exact D.
   - intro No. destruct(Z.ltb_spec (affine_x i inv j 4%nat) (radix-1));auto.
     assert (Yes:existsb (fun l=>radix-1<=?affine_x i inv l 4%nat) (seq 0 8)=true).
     { apply existsb_exists;exists j;split;[apply in_seq;lia|apply Z.leb_le;lia]. } congruence. }
 unfold score,score_x;rewrite Run. set (m:=score_mask _ _ _).
 replace (if m =? 0 then Some(Z.shiftl hi 8) else option_map (append_mask hi m) (Some(masks i)))
   with (Some(append_mask hi m (masks i))) by (unfold append_mask;destruct(m=?0);reflexivity).
 unfold m;rewrite append_score by exact Range. unfold push. f_equal;f_equal.
 apply Z.bits_inj;intro l. destruct(Z_lt_ge_dec l 0);[rewrite !Z.testbit_neg_r by lia;reflexivity|].
 destruct(Z_lt_ge_dec l 8);[|rewrite !(above 8 (byte _)) by (auto using byte_range || lia);reflexivity].
 replace l with (Z.of_nat(Z.to_nat l)) by (rewrite Z2Nat.id;lia);rewrite !byte_bit by lia.
 set (j:=Z.to_nat l);assert (J:(j<8)%nat) by (unfold j;lia).
 rewrite XP by assumption. unfold expected. f_equal. apply Bool.eq_true_iff_eq.
 rewrite andb_true_iff, Bool.eqb_true_iff, flag_correct, Z.eqb_eq, encoding_equal by assumption.
 unfold signs. destruct(unpack_correct flat (ptr i) j Bytes J) as [_ [_ Sg]].
 rewrite Sg;intuition congruence.
Qed.
Local Lemma walk_correct n acc hi : (n<=total)%nat ->
 (forall i j,n=S i -> (j<8)%nat -> split_field(acc j) /\ value(acc j)=(1/value(prefix i j))%fp) ->
 backward n acc hi=Some(packed n hi).
Proof.
 revert acc hi;induction n as [|i IH];intros acc hi N A;[reflexivity|].
 assert (Step:forall t j,i=S t -> (j<8)%nat ->
    (split_field(vecmul (prefix t) acc j) /\ value(vecmul (prefix t) acc j)=(1/value(zz i j))%fp) /\
    (split_field(vecmul (zz i) acc j) /\ value(vecmul (zz i) acc j)=(1/value(prefix t j))%fp)).
 { intros t j Eq J. subst i. destruct(A (S t) j eq_refl J) as [B E].
   destruct(prefix_ok t j ltac:(lia) J) as [Pr NZp].
   destruct(coordinates (S t) j ltac:(lia) J) as [_ [_ [Zr [NZ _]]]].
   destruct(mul_ok _ _ _ (K Multiply) Pr B) as [D [_ V]].
   destruct(mul_ok _ _ _ (K Multiply) Zr B) as [D' [_ V']].
   destruct(mul_ok _ _ _ (K Multiply) Zr Pr) as [_ [_ W]].
   change (value(acc j)=(1/value(mul k (zz (S t) j) (prefix t j)))%fp) in E.
   rewrite W in E. unfold vecmul. split;split;auto using bounded_split;
     rewrite ?V,?V',E;field;auto. }
 cbn [backward packed]. rewrite score_correct.
 - apply IH;[lia|]. intros t j Eq J;exact(proj2(Step t j Eq J)).
 - lia.
 - intros j J;destruct i;[apply (A 0%nat j eq_refl J)|apply (proj1(Step i j eq_refl J))].
Qed.
Local Lemma zero_flags n : any_y n=0 -> forall i j,(i<n)%nat -> (j<8)%nat -> flags i j=false.
Proof.
 induction n as [|t IH];intros H i j I J;[lia|]. cbn [any_y] in H.
 apply Z.lor_eq_0_iff in H as [H L]. destruct(Nat.eq_dec i t) as [->|];[|apply IH;auto;lia].
 rewrite <-(byte_bit (flags t) j J), L;apply Z.testbit_0_l.
Qed.
Lemma batch_correct n : (n<=total)%nat -> returned n=Some(packed n 0).
Proof.
 intros N;unfold returned;destruct n as [|last];[reflexivity|]. destruct (Z.eqb_spec (any_y (S last)) 0) as [No|_].
 - assert (Empty:forall i j,(i<S last)%nat -> (j<8)%nat -> expected i j=false).
   { intros i j I J;unfold expected. destruct(Z.eqb_spec (encoded flat (ptr i) j) (compress (P i j))) as [E|];[|reflexivity].
     apply encoding_equal in E as [Y _];auto. apply (flag_correct i j ltac:(lia) J) in Y.
     rewrite (zero_flags _ No i j I J) in Y;discriminate. }
   assert (E:forall n,(n<=S last)%nat -> packed n 0=0).
   { induction n;intros R;[reflexivity|]. cbn [packed];rewrite push_zero;[apply IHn;lia|intros;apply Empty;lia]. }
   now rewrite E by lia.
 - apply walk_correct;[lia|]. intros i j Eq J;injection Eq as <-.
   destruct(prefix_ok last j ltac:(lia) J) as [B NZ];apply inverse_ok;auto.
Qed.
End Batch.

Lemma packed_bit flat enc P masks n hi i j : (i<n)%nat -> (j<8)%nat ->
 Z.testbit(packed flat enc P masks n hi)(8*Z.of_nat i+Z.of_nat j)=expected flat enc P masks i j.
Proof.
 revert hi i;induction n as [|t IH];intros hi i I J;[lia|].
 cbn [packed]. destruct(Nat.eq_dec i t) as [->|Ne];[|apply IH;lia].
 assert (Upper:forall n hi b,0<=b ->
   Z.testbit(packed flat enc P masks n hi)(8*Z.of_nat n+b)=Z.testbit hi b).
 { induction n;intros h b L;[reflexivity|].
   cbn [packed];rewrite Nat2Z.inj_succ.
   replace (8*Z.succ(Z.of_nat n)+b) with (8*Z.of_nat n+(8+b)) by ring.
   rewrite IHn,push_high by lia;reflexivity. }
 rewrite Upper,push_low by lia;reflexivity.
Qed.
Lemma packed_range flat enc P masks n : 0<=packed flat enc P masks n 0 < 2^(8*Z.of_nat n).
Proof.
 assert (Range:forall t h m,0<=m -> 0<=h<2^m ->
   0<=packed flat enc P masks t h<2^(8*Z.of_nat t+m)).
 { induction t as [|t IH];intros h m M H;[exact H|]. cbn [packed]. rewrite Nat2Z.inj_succ.
   replace (8*Z.succ(Z.of_nat t)+m) with (8*Z.of_nat t+(8+m)) by ring.
   apply IH;[lia|]. unfold push. set (b:=byte _). assert (B:0<=b<256) by apply byte_range.
   assert (D:Z.land (Z.shiftl h 8) b=0).
   { apply Z.bits_inj;intro i;destruct(Z_lt_ge_dec i 0);[rewrite !Z.testbit_neg_r by lia;reflexivity|].
     rewrite Z.land_spec,Z.shiftl_spec,Z.bits_0 by lia;destruct(Z_lt_ge_dec i 8).
     - rewrite Z.testbit_neg_r by lia;reflexivity.
     - rewrite (above 8 b) by lia;apply andb_false_r. }
   pose proof(Z.add_lor_land (Z.shiftl h 8) b) as E. rewrite D,Z.add_0_r in E.
   rewrite E,Z.shiftl_mul_pow2,Z.pow_add_r by lia;lia. }
 specialize(Range n 0 0 ltac:(lia) ltac:(cbn;lia));now rewrite Z.add_0_r in Range.
Qed.
