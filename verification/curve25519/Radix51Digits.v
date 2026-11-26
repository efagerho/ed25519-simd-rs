From Coq Require Import ZArith Bool Lia Ring Znumtheory.
From Curve25519 Require Import Field Radix51 Radix51Zero.
Local Open Scope Z_scope.

Definition five (a b c d e:Z) (i:nat) := match i with
 | O=>a | S O=>b | S(S O)=>c | S(S(S O))=>d | _=>e end.
Definition finite (f:nat->Z) := five (f 0%nat) (f 1%nat) (f 2%nat) (f 3%nat) (f 4%nat).
Lemma finite_at f i : (i<5)%nat -> finite f i=f i.
Proof. intros H;destruct i as [|[|[|[|[|i]]]]];try reflexivity;lia. Qed.
Lemma finite_eq f g : (forall i,(i<5)%nat -> f i=g i) -> finite f=finite g.
Proof. intro E;unfold finite;now rewrite !E by lia. Qed.
Definition pack := Radix51.limbs.
Definition bounded h := field_bound (fun _=>radix+2^22) h.
Lemma bounded_split h : bounded h -> split_field h.
Proof. intros H i I; specialize (H i I); unfold radix,split in *;lia. Qed.
Lemma bounded_value h : bounded h -> 0<=pack h<2*prime-1.
Proof.
 intro H. pose proof(H 0%nat ltac:(lia));pose proof(H 1%nat ltac:(lia));pose proof(H 2%nat ltac:(lia));
 pose proof(H 3%nat ltac:(lia));pose proof(H 4%nat ltac:(lia)).
 unfold pack,limbs,radix,prime in *;lia.
Qed.
Lemma positive_from_low h : bounded h -> 2<=h 0%nat -> 1<pack h.
Proof.
 intros B L; unfold pack,limbs. pose proof (B 1%nat ltac:(lia));pose proof (B 2%nat ltac:(lia));
 pose proof (B 3%nat ltac:(lia));pose proof (B 4%nat ltac:(lia));unfold radix;lia.
Qed.

Definition high_test h delta :=
 (Z.land (Z.land (h 1%nat) (h 2%nat)) (Z.land (h 3%nat) (h 4%nat)) =? radix-1) &&
 (h 0%nat =? radix-19+delta).

Lemma high_test_digits h delta : bounded h ->
 high_test h delta=true <->
 h 0%nat=radix-19+delta /\ h 1%nat=radix-1 /\ h 2%nat=radix-1 /\ h 3%nat=radix-1 /\ h 4%nat=radix-1.
Proof.
 intro B. unfold high_test. rewrite Bool.andb_true_iff,!Z.eqb_eq. split.
 - intros [H A]. apply Radix51Zero.factors in H as [L R].
   destruct (Radix51Zero.split_mask _ _ _ _ L eq_refl) as [B1 B2].
   destruct (Radix51Zero.split_mask _ _ _ _ R eq_refl) as [B3 B4].
   repeat split; auto; apply Radix51Zero.digit_low; auto;
     match goal with |- 0<=h ?i<_ => specialize (B i ltac:(lia));unfold radix in *;lia end.
 - intros [-> [-> [-> [-> ->]]]]. now rewrite !Z.land_diag.
Qed.
Lemma unique_digits h delta : bounded h -> -1<=delta<=1 -> pack h=prime+delta ->
 h 0%nat=radix-19+delta /\ h 1%nat=radix-1 /\ h 2%nat=radix-1 /\ h 3%nat=radix-1 /\ h 4%nat=radix-1.
Proof.
 intros B D V. pose proof(B 0%nat ltac:(lia));pose proof(B 1%nat ltac:(lia));pose proof(B 2%nat ltac:(lia));
 pose proof(B 3%nat ltac:(lia));pose proof(B 4%nat ltac:(lia)).
 unfold pack,limbs,prime,radix in *; simpl Z.pow in *.
 assert (A:h 0%nat=2^51-19+delta) by lia;rewrite A in V.
 assert (B1:h 1%nat=2^51-1) by lia;rewrite B1 in V.
 assert (B2:h 2%nat=2^51-1) by lia;rewrite B2 in V.
 assert (B3:h 3%nat=2^51-1) by lia;rewrite B3 in V.
 repeat split;lia.
Qed.
Lemma high_test_correct h delta : bounded h -> -1<=delta<=1 -> 1<pack h ->
 (high_test h delta=true <-> represents (pack h) delta).
Proof.
 intros B D L. rewrite high_test_digits by exact B. split.
 - intros [A [H [I [J K]]]]. exists 1. unfold pack,limbs. rewrite A,H,I,J,K. unfold radix,prime;ring.
 - intros [k E]. apply unique_digits;auto. pose proof (bounded_value _ B). unfold prime in *;lia.
Qed.
Definition parity_carry h :=
 let c:=(h 0%nat+19)/radix in let c:=(h 1%nat+c)/radix in
 let c:=(h 2%nat+c)/radix in let c:=(h 3%nat+c)/radix in (h 4%nat+c)/radix.
Definition canonical_odd h := Z.odd (Z.lxor (h 0%nat) (parity_carry h)).
Lemma canonical_odd_ok h : bounded h -> canonical_odd h=Z.odd (pack h mod prime).
Proof.
 intro B. pose proof (bounded_value _ B) as Range.
 set (c:=parity_carry h).
 assert (Fold:c=(pack h+19)/(2^255)).
 { unfold c,parity_carry,pack,limbs.
   set (R:=radix). assert (0<R) by (unfold R,radix;lia).
   pose proof (fun n=>Z.div_mod n R ltac:(lia)) as D.
   pose proof (fun n=>Z.mod_pos_bound n R ltac:(lia)) as M.
   set (a:=h 0%nat+19). set (b:=h 1%nat+a/R). set (e:=h 2%nat+b/R).
   set (f:=h 3%nat+e/R). set (g:=h 4%nat+f/R).
   pose proof (D a);pose proof (D b);pose proof (D e);pose proof (D f);pose proof (D g).
   pose proof (M a);pose proof (M b);pose proof (M e);pose proof (M f);pose proof (M g).
   apply Z.div_unique with (r:=a mod R+R*(b mod R+R*(e mod R+R*(f mod R+R*(g mod R))))).
   all: unfold g,f,e,b,a,R,radix in *; try left;lia. }
 assert (Odd:Z.odd (pack h)=Z.odd(h 0%nat)).
 { unfold pack,limbs. rewrite Z.odd_add,Z.odd_mul. change (xorb (Z.odd (h 0%nat)) false=Z.odd(h 0%nat)).
   apply Bool.xorb_false_r. }
 unfold canonical_odd;fold c.
 change (Z.testbit (Z.lxor (h 0%nat) c) 0=Z.odd (pack h mod prime)).
 rewrite Z.lxor_spec. change (xorb (Z.odd (h 0%nat)) (Z.odd c)=Z.odd (pack h mod prime)). rewrite <-Odd.
 destruct (Z_lt_ge_dec (pack h) prime) as [L|L].
 - assert (c=0) by (rewrite Fold; apply Z.div_small;unfold prime in *;lia).
   rewrite H,Z.mod_small by lia. apply Bool.xorb_false_r.
 - assert (c=1) by (rewrite Fold; symmetry;apply Z.div_unique with (r:=pack h-prime);unfold prime in *;[left|];lia).
   assert (pack h mod prime = pack h-prime) by
    (symmetry;apply Z.mod_unique with (q:=1);unfold prime in *;[left|];lia).
   rewrite H,H0,Z.odd_sub;reflexivity.
Qed.

Definition neg_digits h i := 2*(radix-if Nat.eqb i 0 then 19 else 1)-h i.
Lemma neg_digits_ok h : bounded h -> split_field (neg_digits h) /\
 represents (pack (neg_digits h)) (-pack h).
Proof.
 intro B;split.
 - intros i I;specialize (B i I);unfold neg_digits; destruct (Nat.eqb i 0);unfold radix,split in *;lia.
 - exists 2;unfold pack,limbs,neg_digits;cbn [Nat.eqb];unfold radix,prime;ring.
Qed.

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

Lemma low_digit_parity h : bounded h -> h 4%nat<radix-1 ->
 Z.odd(h 0%nat)=Z.odd(pack h mod prime).
Proof.
 intros B Fast. destruct(bounded_value _ B) as [Lo _].
 assert (Hi:pack h<prime).
 { pose proof(B 0%nat ltac:(lia));pose proof(B 1%nat ltac:(lia));pose proof(B 2%nat ltac:(lia));
   pose proof(B 3%nat ltac:(lia));unfold pack,limbs,prime,radix in *;lia. }
 rewrite Z.mod_small by lia.
 unfold pack,limbs;rewrite Z.odd_add,Z.odd_mul. symmetry;apply Bool.xorb_false_r.
Qed.

Definition sqrt_limbs := five 1718705420411056 234908883556509 2233514472574048 2117202627021982 765476049583133.
Lemma sqrt_bound : split_field sqrt_limbs.
Proof. intros [|[|[|[|i]]]] Lt; vm_compute;easy. Qed.
Lemma sqrt_m1_radix51 : pack sqrt_limbs = sqrt_m1.
Proof. reflexivity. Qed.
