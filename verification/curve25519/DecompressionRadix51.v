From Coq Require Import ZArith Lia Ring Znumtheory.
From Curve25519 Require Import Field Radix51 DeferredCarry Radix51Digits.
Local Open Scope Z_scope.

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
   assert (P:1<pack h) by (apply positive_from_low; assumption).
   apply (proj2 (high_test_correct _ 1 B ltac:(lia) P)) in One.
   apply high_test_digits in One as [A [H [I [J K]]]];[|exact B].
   unfold high_test,u_digits,finite,five,carry,scaled_digit;rewrite A,H,I,J,K;reflexivity.
Qed.

Lemma setup_digits h y : represents (pack h) (y*y) ->
 let u := 121666*(y*y-1) in
 represents (pack(u_digits h)) u /\ represents (pack(v_digits h)) (y*y-u).
Proof.
 intros YY u. destruct (scaled_values h) as [U V].
 assert (N : represents (pack(u_digits h)) u).
 { eapply ctrans; [exact U|]. apply ctimes; [apply crefl|]. now apply cminus; [|apply crefl]. }
 split; [exact N|]. eapply ctrans; [exact V|]. now apply cminus.
Qed.
