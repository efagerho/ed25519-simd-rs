From Coq Require Import List ZArith Lia Ring Field.
From Machine Require Import isa.Arithmetic execution.WordBounds.
From Curve25519 Require Import Radix51 Edwards.
From Curve25519.group Require Import PrimeField Affine Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Import Kernels Power Limbs Decode.
From Ed25519Simd.KeyTable Require Import Fields Pack Image.
Import ListNotations. Local Open Scope Z_scope.

Definition coord w j c i := cell w (5*c+i)%nat j.
Definition fields k w j c := compute k (coord w j) (field_op c).
Definition column k w j i := fields k w j (i/5)%nat (i mod 5)%nat.
Fixpoint eval (f:nat->nat->Z) word := match word with
 | Input i j=>f j i | Literal z=>z | Subtract z t=>vpsubq z (eval f t) | Unknown=>0 end.
Definition row k w pos j i := eval (column k w) (signed_word pos i j).
Definition staged k w n :=
 let i:=(n/8)%nat in let j:=(n mod 8)%nat in
 eval (column k w) (initial (reg_for i) j).
Definition kernels_ok k := verified k Multiply=true /\ forall op,checked k op=true.
Local Opaque mul linear_result.

Lemma field_bounds k w j c : kernels_ok k -> cache_bounds false w -> (j<8)%nat ->
 split_field (fields k w j c).
Proof.
 intros [M C] W J.
 assert (B:forall c,(c<4)%nat->split_field (coord w j c)).
 { intros n N i I. specialize(W (5*n+i)%nat j ltac:(cbn;lia) J);unfold coord;unfold split;lia. }
 destruct c as [|[|[|c]]];cbn [fields compute source rhs field_op linear_op];try (apply linear_ok;auto;apply B;lia).
 apply bounded_split. apply (proj1 (mul_ok _ _ _ M (B 3%nat ltac:(lia)) two_d_split)).
Qed.
Lemma stage_cell k w i j : (i<15)%nat -> (j<8)%nat ->
 cell (staged k w) i j=column k w j i.
Proof.
 intros I J;unfold cell,staged.
 replace ((i*8+j)/8)%nat with i by (apply Nat.div_unique with (r:=j);lia).
 replace ((i*8+j) mod 8)%nat with j by (apply Nat.mod_unique with (q:=i);lia).
 do 15 (destruct i as [|i];[reflexivity|]);lia.
Qed.
Lemma stage_bounds k w : kernels_ok k -> cache_bounds false w -> cache_bounds true (staged k w).
Proof.
 intros K W i j I J;rewrite stage_cell by assumption.
 pose proof(field_bounds k w j (i/5)%nat K W J (i mod 5)%nat (Nat.mod_upper_bound i 5 ltac:(lia))).
 unfold column,split in *;lia.
Qed.

Definition sign_field k w j (pos:bool) c : field := if pos then fields k w j c else
 match c with O=>fields k w j 1 | S O=>fields k w j 0
 | S(S O)=>neg_digits (fields k w j 2) | _=>fields k w j 3 end.
Lemma product_bound k w j : kernels_ok k -> cache_bounds false w -> (j<8)%nat ->
 bounded (fields k w j 2).
Proof.
 intros [M _] W J. apply mul_ok;auto using two_d_split.
 intros i I;specialize(W (15+i)%nat j ltac:(cbn;lia) J).
 change (0<=cell w (15+i)%nat j<=2^52-1);lia.
Qed.
Lemma neg_word h i : bounded h -> (i<5)%nat ->
 vpsubq (2*(radix-if Nat.eqb i 0 then 19 else 1)) (h i) = neg_digits h i.
Proof.
 intros B I;apply low64_id. pose proof(proj1(neg_digits_ok _ B) i I).
 unfold word64,neg_digits,split in *;lia.
Qed.
Lemma row_field k w j pos c i : kernels_ok k -> cache_bounds false w ->
 (j<8)%nat -> (c<4)%nat -> (i<5)%nat ->
 row k w pos j (5*c+i)%nat = sign_field k w j pos c i.
Proof.
 intros K W J H I. pose proof(product_bound _ _ _ K W J) as B. pose proof(neg_word _ i B I) as N.
 destruct pos,c as [|[|[|[|c]]]];try lia;
 do 5 (destruct i as [|i];[first [reflexivity|exact N]|]);lia.
Qed.
Lemma row_bounds k w pos j i : kernels_ok k -> cache_bounds false w -> (j<8)%nat -> (i<20)%nat ->
 0<=row k w pos j i<2^52.
Proof.
 intros K W J I. pose proof(Nat.div_mod i 5 ltac:(lia)) as E.
 pose proof(Nat.mod_upper_bound i 5 ltac:(lia)) as R.
 set (c:=(i/5)%nat) in *;set (l:=(i mod 5)%nat) in *.
 rewrite E, row_field by (auto;lia).
 assert (B:split_field (sign_field k w j pos c)).
 { destruct pos,c as [|[|[|c]]];cbn [sign_field];try (apply field_bounds;assumption).
   apply neg_digits_ok,product_bound;assumption. }
 specialize(B l R);unfold split in B;lia.
Qed.

Lemma row_rep k w j pos P : kernels_ok k -> cache_bounds false w -> (j<8)%nat ->
 represents_point true (point_values w j) P ->
 represents_cache (scalar_cache false (row k w pos j)) (if pos then P else negative P).
Proof.
 intros [M C] W J [[NZ [X Y]] T];specialize(T eq_refl).
 set (a:=coord w j).
 assert (B:forall c,(c<4)%nat->split_field (a c)).
 { intros c H i I. specialize(W (5*c+i)%nat j ltac:(cbn;lia) J);unfold a,coord,split;lia. }
 pose proof(proj2(linear_ok k Difference _ _ (C _) (B 1%nat ltac:(lia)) (B 0%nat ltac:(lia)))) as D.
 pose proof(proj2(linear_ok k Sum _ _ (C _) (B 1%nat ltac:(lia)) (B 0%nat ltac:(lia)))) as S.
 pose proof(proj2(linear_ok k Twice _ _ (C _) (B 2%nat ltac:(lia)) (B 2%nat ltac:(lia)))) as Z2.
 destruct(mul_ok k _ two_d M (B 3%nat ltac:(lia))
   two_d_split) as [TB [_ Td]].
 pose proof(proj2(neg_digits_ok _ TB)) as Neg.
 apply congruent_value in D,S,Z2,Neg. cbn [formula] in D,S,Z2.
 rewrite residue_sub in D;rewrite residue_add in S,Z2;rewrite residue_opp in Neg.
 change (value (a 2%nat)<>0%fp) in NZ.
 change (value (a 0%nat)=(x P*value(a 2%nat))%fp) in X.
 change (value (a 1%nat)=(y P*value(a 2%nat))%fp) in Y.
 change (value (a 3%nat)=(x P*y P*value(a 2%nat))%fp) in T.
 assert (E:forall c,(c<4)%nat->limbs (fun i=>row k w pos j (5*c+i)%nat)=limbs(sign_field k w j pos c)).
 { intros;apply limbs_ext;intros;apply row_field;auto;split;auto. }
 exists (value(a 2%nat));split;[exact NZ|].
 unfold scalar_cache,cache_from_fields;cbn [y_minus_x y_plus_x t2d doubled_z];rewrite !E by lia.
 unfold value,pack in *.
 pose proof two_d_value as D2;unfold value,pack in D2;rewrite D2 in Td.
 destruct pos;cbn [sign_field fields compute source rhs field_op linear_op negative x y];fold a;rewrite ?Neg,?D,?S,?Z2,?Td,?X,?Y,?T;
 repeat split;ring.
Qed.

Lemma staged_rep k w j P : kernels_ok k -> cache_bounds false w -> (j<8)%nat ->
 represents_point true (point_values w j) P -> value (coord w j 2)=1%fp ->
 represents_cache (cache_values true (staged k w) j) P.
Proof.
 intros K W J Rep Z1.
 destruct (row_rep k w j true P K W J Rep) as [z [NZ [M [S [T Z2]]]]].
 assert (E:forall c,(c<3)%nat -> word_coordinate (staged k w) j c =
   limbs (fun i=>row k w true j (5*c+i)%nat)).
 { intros c C;apply limbs_ext;intros i I;apply stage_cell;lia. }
 unfold scalar_cache,cache_from_fields in M,S,T,Z2;cbn [y_minus_x y_plus_x t2d doubled_z] in M,S,T,Z2.
 assert (V:limbs (fun i=>row k w true j (5*3+i)%nat)=limbs(fields k w j 3)).
 { apply limbs_ext;intros;apply (row_field k w j true 3%nat);auto. }
 rewrite V in Z2.
 assert (B:split_field (coord w j 2)).
 { intros i I;specialize(W (10+i)%nat j ltac:(cbn;lia) J);change (0<=cell w (10+i)%nat j<=2^52-1);lia. }
 pose proof(proj2(linear_ok k Twice _ _ (proj2 K Twice) B B)) as L.
 apply congruent_value in L;cbn [formula] in L;rewrite residue_add in L.
 change (residue(limbs(fields k w j 3))=(value(coord w j 2)+value(coord w j 2))%fp) in L.
 rewrite L,Z1 in Z2.
 exists z. unfold cache_values,cache_from_fields;cbn [y_minus_x y_plus_x t2d doubled_z].
 rewrite !E by lia;repeat split;auto.
 transitivity (((1+1)*z/(1+1))%fp);[field;discriminate|rewrite <-Z2;field;discriminate].
Qed.
