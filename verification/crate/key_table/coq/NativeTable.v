From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls memory.ByteMemory.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Decode.
From Ed25519Simd.KeyTable Require Image Rows.
From Curve25519.group Require Import PrimeField.
Local Open Scope Z_scope.

Definition slot base j digit i :=
 base + 2720*Z.of_nat j + 160*(8+digit) + 8*Z.of_nat i.

Lemma identity_rep : represents_cache (scalar_cache false (fun i=>Image.identity_word (Z.of_nat i))) identity.
Proof.
 exists 1%fp;split;[discriminate|].
 change ((1=(1-0)*1) /\ (1=(1+0)*1) /\ (0=(1+1)*d*0*1*1) /\ residue 2=(1+1)*1)%fp.
 rewrite residue_two;repeat split;ring.
Qed.

Definition seed w j P:=represents_point true (point_values w j) P /\ Decode.value (Rows.coord w j 2)=1%fp.
Definition stored base d (pos:bool) m j i:=read_word m
 ((if pos then base+1280+160*d else base+1280-160*d)+2720*Z.of_nat j+8*Z.of_nat i).
Definition row_value base d sign m w j:=let v:=stored base d sign m j in
 (forall i,(i<20)%nat -> 0<=v i<2^52) /\ forall P,seed w j P ->
 represents_cache (scalar_cache false v) (if sign then scale d P else negative (scale d P)).
Definition prior_rows base d m w:=forall k sign j,1<=k<=d -> (j<8)%nat -> row_value base k sign m w j.
Definition center base m:=forall j i,(j<8)%nat -> (i<20)%nat ->
 stored base 0 true m j i=Image.identity_word (Z.of_nat i).
Definition contents base w m:=center base m /\ (cache_bounds false w -> prior_rows base 8 m w).

Lemma input_ext base w w' m : (forall n,(n<160)%nat -> w n=w' n) -> contents base w m -> contents base w' m.
Proof.
 intros E [Center Last];split;[exact Center|intros B].
 assert (W:cache_bounds false w).
 { intros i j I J;change (i<20)%nat in I;unfold cell;rewrite E by lia;apply B;assumption. }
 intros d sign j D J;destruct(Last W d sign j D J) as [Bounds Rep];split;[exact Bounds|].
 intros P [Pt Z1];apply Rep;split;[now rewrite (point_values_ext _ _ _ E J)|].
 rewrite <-Z1;unfold Decode.value;apply f_equal;exact (field_at_ext _ _ 10 j E ltac:(lia) J).
Qed.

Lemma cache_ext a b : (forall i,(i<20)%nat -> a i=b i) -> scalar_cache false a=scalar_cache false b.
Proof.
 intro E;unfold scalar_cache,cache_from_fields;f_equal;try match goal with |-Some _=Some _=>f_equal end;
 apply Radix51.limbs_ext;intros;apply E;lia.
Qed.

Lemma preserve base w before after :
 preserved (fun x=>base<=x<base+21760) before after -> contents base w before -> contents base w after.
Proof.
 intros Keep [Center Rows].
 assert (Eq:forall d sign j i,0<=d<=8 -> (j<8)%nat -> (i<20)%nat ->
   stored base d sign after j i=stored base d sign before j i).
 { intros d sign j i D J I;unfold stored;apply preserved_read with (outside:=fun x=>base<=x<base+21760);
    [exact Keep|intros b B;change (0<=b<8) in B;destruct sign;lia]. }
 split;[intros j i J I;rewrite Eq by lia;apply Center;assumption|].
 intros B d sign j D J;destruct(Rows B d sign j D J) as [Bound Rep].
 split;[intros i I;rewrite Eq by lia;apply Bound,I|].
 intros P S;rewrite (cache_ext _ _ (fun i I=>Eq d sign j i ltac:(lia) J I));apply Rep,S.
Qed.

(* The consumer indexes a lane-major array with the signed digit biased by 8. *)
Theorem signed_entry base w m j d : contents base w m -> cache_bounds false w ->
 (j<8)%nat -> -8<=d<=8 -> let row i:=read_word m (slot base j d i) in
 (forall i,(i<20)%nat -> 0<=row i<2^52) /\
 forall P,seed w j P -> represents_cache (scalar_cache false row) (scale d P).
Proof.
 intros [Center Rows] Bound J D row.
 assert (Slot:forall k sign, d=(if sign:bool then k else -k) ->
    forall i,row i=stored base k sign m j i).
 { intros k [] -> i;unfold row,stored,slot;f_equal;ring. }
 destruct (Z.eq_dec d 0) as [Zero|NZ].
 - assert (E:forall i,(i<20)%nat -> row i=Image.identity_word (Z.of_nat i)).
   { intros i N;rewrite (Slot 0 true Zero);apply Center;assumption. }
   split;[intros i N;rewrite E by exact N;do 20 (destruct i as [|i];[vm_compute;easy|]);lia|].
   intros P _;rewrite (cache_ext _ _ E),Zero;exact identity_rep.
 - set (k:=Z.abs d);set (sign:=(0<?d)).
   assert (Dg:d=(if sign then k else -k)) by
     (unfold sign,k;destruct(Z.ltb_spec 0 d);[rewrite Z.abs_eq by lia|rewrite Z.abs_neq by lia];lia).
   destruct(Rows Bound k sign j ltac:(unfold k;lia) J) as [B R].
   split;[intros i I;rewrite (Slot k sign Dg);apply B,I|].
   intros P S;rewrite (cache_ext _ _ (fun i _=>Slot k sign Dg i)).
   specialize(R P S);destruct sign;[now rewrite Dg|rewrite Dg;now rewrite <-SignedMultiple.negative_scale].
Qed.
