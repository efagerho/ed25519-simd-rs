From Coq Require Import ZArith Bool Lia Ring Znumtheory.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.field51 Require Import Zero.
Local Open Scope Z_scope.

Definition five (a b c d e:Z) (i:nat) := match i with
 | O=>a | S O=>b | S(S O)=>c | S(S(S O))=>d | _=>e end.
Definition finite (f:nat->Z) := five (f 0%nat) (f 1%nat) (f 2%nat) (f 3%nat) (f 4%nat).
Lemma finite_at f i : (i<5)%nat -> finite f i=f i.
Proof. intros H;destruct i as [|[|[|[|[|i]]]]];try reflexivity;lia. Qed.
Lemma finite_eq f g : (forall i,(i<5)%nat -> f i=g i) -> finite f=finite g.
Proof. intro E;unfold finite;now rewrite !E by lia. Qed.
Definition pack := Radix51.limbs.
Definition carry (h:nat->Z) i := h i mod radix +
 match i with O=>19*(h 4%nat/radix) | S j=>h j/radix end.
Lemma carry_value h : represents (pack(carry h)) (pack h).
Proof.
 exists (-(h 4%nat/radix)). unfold carry,pack,limbs.
 pose proof (fun i=>Z.div_mod (h i) radix ltac:(unfold radix;discriminate)) as D.
 pose proof (D 0%nat);pose proof (D 1%nat);pose proof (D 2%nat);
 pose proof (D 3%nat);pose proof (D 4%nat).
 unfold radix,prime in *; lia.
Qed.

Definition bounded h := field_bound (fun _=>radix+2^22) h.
Lemma bounded_split h : bounded h -> split_field h.
Proof. intros H i I; specialize (H i I); unfold radix,split in *;lia. Qed.
Lemma bounded_value h : bounded h -> 0<=pack h<2*prime-1.
Proof.
 intro H. pose proof(H 0%nat ltac:(lia));pose proof(H 1%nat ltac:(lia));pose proof(H 2%nat ltac:(lia));
 pose proof(H 3%nat ltac:(lia));pose proof(H 4%nat ltac:(lia)).
 unfold pack,limbs,radix,prime in *;lia.
Qed.
Definition scaled_digit h i := 121666*(h i-if Nat.eqb i 0 then 1 else 0).
Definition u_digits h := finite (carry (scaled_digit h)).
Definition biased_digit h i := h i + 1024*(radix-if Nat.eqb i 0 then 19 else 1) - u_digits h i.
Definition v_digits h := finite (carry (biased_digit h)).

Lemma scaled_bounds h : bounded h -> 2<=h 0%nat ->
 bounded (u_digits h) /\ bounded (v_digits h).
Proof.
 intros B L.
 assert (Range:forall i,(i<5)%nat -> 0<=scaled_digit h i<=121666*(radix+2^22)).
 { intros i I. specialize (B i I). unfold scaled_digit. destruct (Nat.eqb_spec i 0);subst;lia. }
 assert (Step:forall f m, (forall i,(i<5)%nat -> 0<=f i<=m) -> 0<=m ->
    forall i,(i<5)%nat -> 0<=carry f i<=radix-1+19*(m/radix)).
 { intros f m F M i I. unfold carry. pose proof(Z.mod_pos_bound (f i) radix ltac:(unfold radix;lia)).
   assert (D:forall j,(j<5)%nat->0<=f j/radix<=m/radix).
   { intros j J. specialize(F j J). split;[apply Z.div_pos|apply Z.div_le_mono];unfold radix in *;lia. }
   destruct i as [|j];[specialize (D 4%nat ltac:(lia))| specialize(D j ltac:(lia))];lia. }
 assert (U:bounded(u_digits h)).
 { intros i I. pose proof (Step _ _ Range ltac:(unfold radix;lia) i I).
   change (0<=carry (scaled_digit h) i<=radix-1+19*121666) in H. unfold u_digits;rewrite finite_at by exact I;lia. }
 split;[exact U|].
 assert (Diff:forall i,(i<5)%nat -> 0<=biased_digit h i<=1025*radix+2^22).
 { intros i I. specialize(B i I);specialize(U i I);unfold biased_digit.
   destruct (Nat.eqb i 0);unfold radix in *;lia. }
 intros i I. pose proof (Step _ _ Diff ltac:(unfold radix;lia) i I).
 change (0<=carry (biased_digit h) i<=radix-1+19*1025) in H. unfold v_digits;rewrite finite_at by exact I;lia.
Qed.
Lemma scaled_values h :
 represents (pack(u_digits h)) (121666*(pack h-1)) /\
 represents (pack(v_digits h)) (pack h-pack(u_digits h)).
Proof.
 split; eapply ctrans; [apply carry_value| |apply carry_value|].
 - exists 0; unfold pack,limbs,scaled_digit;cbn [Nat.eqb];ring.
 - exists 1024; unfold pack,limbs,biased_digit;cbn [Nat.eqb]. unfold radix,prime;ring.
Qed.

Definition high_test h delta :=
 (Z.land (Z.land (h 1%nat) (h 2%nat)) (Z.land (h 3%nat) (h 4%nat)) =? radix-1) &&
 (h 0%nat =? radix-19+delta).

Lemma high_test_digits h delta : bounded h ->
 high_test h delta=true <->
 h 0%nat=radix-19+delta /\ h 1%nat=radix-1 /\ h 2%nat=radix-1 /\ h 3%nat=radix-1 /\ h 4%nat=radix-1.
Proof.
 intro B. unfold high_test. rewrite Bool.andb_true_iff,!Z.eqb_eq. split.
 - intros [H A]. apply Zero.factors in H as [L R].
   destruct (Zero.split_mask _ _ _ _ L eq_refl) as [B1 B2].
   destruct (Zero.split_mask _ _ _ _ R eq_refl) as [B3 B4].
   repeat split; auto; apply Zero.digit_low; auto;
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
Lemma u_test_correct h : bounded h -> 2<=h 0%nat ->
 (high_test (u_digits h) 0=true <-> represents (pack(u_digits h)) 0).
Proof.
 intros B L. destruct (scaled_bounds _ B L) as [U _].
 split.
 - rewrite high_test_digits by exact U. intros [A [H [I [J K]]]].
   exists 1. unfold pack,limbs. rewrite A,H,I,J,K;reflexivity.
 - intro Zero. destruct (scaled_values h) as [V _].
   assert (One:represents (pack h) 1).
   { destruct Zero as [z Zr],V as [j Eq].
     assert (C:Z.gcd 121666 prime=1) by reflexivity.
     assert (Div:(prime | 121666*(pack h-1))) by (exists (z-j);lia).
     apply Gauss in Div;[|apply Zgcd_1_rel_prime;rewrite Z.gcd_comm;exact C].
     destruct Div as [n E];exists n;lia. }
   assert (P:1<pack h).
   { unfold pack,limbs. pose proof(B 1%nat ltac:(lia));pose proof(B 2%nat ltac:(lia));
     pose proof(B 3%nat ltac:(lia));pose proof(B 4%nat ltac:(lia));unfold radix in *;lia. }
   apply (proj2 (high_test_correct _ 1 B ltac:(lia) P)) in One.
   apply high_test_digits in One as [A [H [I [J K]]]];[|exact B].
   unfold high_test,u_digits,finite,five,carry,scaled_digit;rewrite A,H,I,J,K;reflexivity.
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
