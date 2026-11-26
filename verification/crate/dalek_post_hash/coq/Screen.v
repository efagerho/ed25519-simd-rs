From Coq Require Import List ZArith Bool Lia.
From Machine Require Import memory.ByteMemory.
From Curve25519 Require Import Field.
From Curve25519.group Require Import PrimeField Affine.
From Ed25519Simd.Dalek Require Import Encoding.
From Ed25519Simd.Decode Require Import Unpack.
From Ed25519Simd.DalekPostHash Require Import Caller.
Import ListNotations. Local Open Scope Z_scope.

Definition word flat ptr j i := read_word flat (ptr+32*Z.of_nat j+8*i).
Definition rejects flat ptr j :=
 let w:=word flat ptr j in
 if w 0 <=? 1 then Z.lor (Z.lor ((2*w 3) mod 2^64) (w 2)) (w 1) =? 0
 else (2^64-20 <=? w 0) &&
 (Z.land (Z.land (Z.setbit (w 3) 63) (w 2)) (w 1) =? Z.ones 64).
Definition lane_screen flat ptr j :=
 let w:=word flat ptr j in
 if reaches Push ReadLow (w 0=?1) (w 0<?1) HighLow then
   reaches Push HighLow false (w 0<?2^64-20) HighUpper &&
   reaches Push HighUpper (Z.land (Z.land (Z.setbit (w 3) 63) (w 2)) (w 1)=?Z.ones 64) false NextEncoding
 else reaches Push LowUpper (Z.lor (Z.lor ((2*w 3) mod 2^64) (w 2)) (w 1)=?0) false LowNext.
Fixpoint walk fuel j flat ptr := match fuel with O=>false | S rem=>
 lane_screen flat ptr j && match next Push NextEncoding (32*Z.of_nat(S j)=?256) false with
 | Some(Local Screened)=>true | Some(Local ReadLow)=>walk rem (S j) flat ptr | _=>false end end.
Definition screen flat ptr :=
 let low:=(word flat ptr 0 0+20) mod 2^32 in
 reaches Push FirstWord (low=?21) (low<?21) StartScreen && walk 8 0 flat ptr.

Lemma walk_all flat ptr n j : (n+j=8)%nat ->
 walk n j flat ptr=true -> forall i,(j<=i<8)%nat -> rejects flat ptr i=true.
Proof.
 revert j;induction n;intros j H Run i I;[lia|].
 cbn [walk] in Run;apply andb_true_iff in Run as [Test More].
 destruct (Nat.eq_dec i j) as [->|N].
 - unfold lane_screen in Test;unfold rejects.
   set (w:=word flat ptr j) in *.
   assert (A:forall e b,reaches Push ReadLow e b HighLow=negb(e||b)) by (destruct e,b;reflexivity).
   assert (B:forall b,reaches Push HighLow false b HighUpper=negb b) by (destruct b;reflexivity).
   assert (C:forall e,reaches Push HighUpper e false NextEncoding=e) by (destruct e;reflexivity).
   assert (D:forall e,reaches Push LowUpper e false LowNext=e) by (destruct e;reflexivity).
   rewrite A,B,C,D in Test.
   replace ((w 0=?1)||(w 0<?1))%bool with (w 0<=?1) in Test by
     (destruct (Z.eqb_spec (w 0) 1),(Z.ltb_spec (w 0) 1),(Z.leb_spec (w 0) 1);try reflexivity;lia).
   replace (negb(w 0<?2^64-20)) with (2^64-20<=?w 0) in Test by
     (destruct(Z.ltb_spec (w 0) (2^64-20)),(Z.leb_spec (2^64-20) (w 0));try reflexivity;lia). destruct (w 0<=?1);exact Test.
 - assert ((32*Z.of_nat(S j)=?256)=false) by (apply Z.eqb_neq;lia).
   rewrite H0 in More;apply (IHn (S j) ltac:(lia) More i);lia.
Qed.

(* The pointer starts at RDX, advances 32 bytes, and stops at RDX+256.
   Each rejecting lane must pass the full four-qword test. *)
Definition screening_flow := forall eq below,
 next Push FirstWord eq below=Some(Local(if negb(eq||below) then Enqueue else StartScreen)) /\
 next Push StartScreen eq below=Some(Local ReadLow) /\
 next Push ReadLow eq below=Some(Local(if negb(eq||below) then HighLow else LowUpper)) /\
 next Push LowUpper eq below=Some(Local(if eq then LowNext else Enqueue)) /\
 next Push LowNext eq below=Some(Local NextEncoding) /\
 next Push HighLow eq below=Some(Local(if below then Enqueue else HighUpper)) /\
 next Push HighUpper eq below=Some(Local(if eq then NextEncoding else Enqueue)) /\
 next Push NextEncoding eq below=Some(Local(if eq then Screened else ReadLow)) /\
 next Push Screened eq below=Some(External Scatter).

Local Lemma read_join n m f a :
 read_le (n+m) f a=read_le n f a+256^Z.of_nat n * read_le m f (a+Z.of_nat n).
Proof.
 revert a;induction n;intro a;[cbn [Nat.add read_le Z.of_nat];rewrite Z.add_0_r;ring|].
 cbn [Nat.add read_le];rewrite IHn,Nat2Z.inj_succ,Z.pow_succ_r by lia.
 replace (a+1+Z.of_nat n) with (a+Z.succ(Z.of_nat n)) by lia;ring.
Qed.
Local Lemma packed_words flat ptr j :
 let w:=word flat ptr j in encoded flat ptr j=w 0+2^64*w 1+2^128*w 2+2^192*w 3.
Proof.
 intro w;unfold encoded. rewrite (read_join 8 24),(read_join 8 16),(read_join 8 8).
 unfold w,word,read_word. set (a:=ptr+32*Z.of_nat j).
 change (Z.of_nat 8) with 8. change (256^8) with (2^64).
 replace (a+8*0) with a by ring. replace (a+8*1) with (a+8) by ring.
 replace (a+8*2) with (a+8+8) by ring. replace (a+8*3) with (a+8+8+8) by ring.
 ring.
Qed.

Local Lemma land_full a b : 0<=a<2^64 -> 0<=b<2^64 ->
 Z.land a b=Z.ones 64 -> a=Z.ones 64 /\ b=Z.ones 64.
Proof.
 intros A B H. split;apply Z.bits_inj;intro i;
 destruct (Z_lt_ge_dec i 0);[now rewrite !Z.testbit_neg_r by lia| |now rewrite !Z.testbit_neg_r by lia|];
 destruct (Z_lt_ge_dec i 64).
 all: try (rewrite Z.ones_spec_low by lia;apply (f_equal (fun w=>Z.testbit w i)) in H;
   cbn beta in H;rewrite Z.land_spec,Z.ones_spec_low in H by lia;apply andb_true_iff in H;tauto).
 all: rewrite Z.ones_spec_high by lia;first [rewrite <-(Z.mod_small a (2^64) A) at 1|rewrite <-(Z.mod_small b (2^64) B) at 1];
 apply Z.mod_pow2_bits_high;lia.
Qed.

Local Lemma top_set w : 0<=w<2^64 -> Z.setbit w 63=w mod 2^63+2^63.
Proof.
 intro W. rewrite Z.setbit_spec'. set (lo:=w mod 2^63).
 assert (Dis:Z.land lo (2^63)=0).
 { apply Z.bits_inj;intro i;rewrite Z.land_spec,Z.bits_0.
   destruct (Z.eq_dec i 63) as [->|N].
   - unfold lo;rewrite Z.mod_pow2_bits_high by lia;reflexivity.
   - rewrite Z.pow2_bits_false by lia;apply Bool.andb_false_r. }
 rewrite <-(Z.add_lor_land lo (2^63)),Dis,Z.add_0_r.
 apply Z.bits_inj;intro i;rewrite !Z.lor_spec.
 destruct (Z_lt_ge_dec i 0);[rewrite !Z.testbit_neg_r by lia;reflexivity|].
 destruct (Z_lt_ge_dec i 63);[unfold lo;now rewrite Z.mod_pow2_bits_low by lia|].
 destruct (Z.eq_dec i 63) as [->|N];[now rewrite Z.pow2_bits_true,!Bool.orb_true_r by lia|].
 unfold lo;rewrite Z.mod_pow2_bits_high by lia.
 replace w with (w mod 2^64) at 1 by (apply Z.mod_small;lia).
 now rewrite Z.mod_pow2_bits_high by lia.
Qed.

Lemma screen_sound flat ptr : byte_memory flat -> screen flat ptr=true ->
 forall j,(j<8)%nat -> forall P, encoded flat ptr j=compression P -> multiple 8 P=identity.
Proof.
 intros Bytes Test j J P Eq. unfold screen in Test. apply andb_true_iff in Test as [_ All].
 pose proof(walk_all _ _ 8 0 eq_refl All j ltac:(lia)) as AllJ. clear All;rename AllJ into All.
 set (w:=word flat ptr j) in *. assert (W:forall i,0<=w i<2^64) by (intro;apply read_word_bound,Bytes).
 pose proof (W 0);pose proof (W 1);pose proof (W 2);pose proof (W 3).
 pose proof (Z.div_mod (w 3) (2^63) ltac:(lia)) as Top.
 pose proof (Z.mod_pos_bound (w 3) (2^63) ltac:(lia)) as Low.
 assert (Y:encoded flat ptr j mod 2^255=
  w 0+2^64*w 1+2^128*w 2+2^192*(w 3 mod 2^63)).
 { symmetry. apply Z.mod_unique with (q:=w 3/2^63);[left;lia|].
   rewrite packed_words;fold w;lia. }
 assert (Dec:forall U V:point, {U=V}+{U<>V}).
 { intros U V;destruct(fp_eq_dec (x U)(x V)),(fp_eq_dec (y U)(y V));
   first [left;apply point_ext;auto;fail|right;congruence]. }
 destruct (Dec (multiple 8 P) identity) as [I|N];[exact I|exfalso].
 pose proof (strict_encoding_y_range _ N) as Range. rewrite <-Eq,Y in Range.
 unfold rejects in All;fold w in All. destruct (w 0 <=? 1) eqn:Small.
 - apply Z.leb_le in Small;apply Z.eqb_eq in All.
   rewrite !Z.lor_eq_0_iff in All. destruct All as [[Hi Mid] Lo].
   pose proof (Z.div_mod (2*w 3) (2^64) ltac:(lia)).
   assert (w 3 mod 2^63=0) by lia. lia.
 - apply andb_true_iff in All as [Lo Hi];apply Z.leb_le in Lo;apply Z.eqb_eq in Hi.
   rewrite top_set in Hi by apply W. set (t:=w 3 mod 2^63+2^63) in *.
   assert (T:0<=t<2^64) by (unfold t;lia).
   assert (B:0<=Z.land t (w 2)<2^64).
   { rewrite <-(Z.mod_small (w 2) (2^64) (W 2)),<-Z.land_ones by lia.
     rewrite Z.land_assoc,Z.land_ones by lia;apply Z.mod_pos_bound;lia. }
   destruct(land_full _ _ B (W 1) Hi) as [Both Last].
   destruct(land_full _ _ T (W 2) Both) as [HT HM].
   change (Z.ones 64) with (2^64-1) in *. unfold t in HT;unfold prime in Range;lia.
Qed.
