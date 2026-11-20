From Coq Require Import List ZArith Lia Bool Ring.
From Machine Require Import execution.MaskTrace execution.CircuitFacts.
From ProofArithmetic Require Import Expressions.
From Curve25519 Require Import Field Radix51 Edwards Torsion.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.field51 Require Import Arithmetic Check RootMasks.
From Ed25519Simd.SmallOrder Require Import Audit Schedule.
Import ListNotations. Local Open Scope Z_scope.

Local Definition environment p j (w:nat->Z) k :=
 if Nat.ltb k 64 then cell p k j else w (k-64)%nat.
Local Lemma sources p j ini w : (j<8)%nat -> bounded p ->
  source_ok used (environment p j w) (operand j (inputs p j) ini w).
Proof.
 intros J B. split; [|split].
 - intros a H. destruct a as [z|b i|r|i|a]; try discriminate; try reflexivity.
   + cbn [supported_arg used] in H. apply andb_true_iff in H as [Base I].
     apply Nat.eqb_eq in Base; subst. apply Nat.ltb_lt in I.
     unfold atom, environment. cbn [val Nat.eqb Nat.add].
     now rewrite (proj2 (Nat.ltb_lt i 64) ltac:(lia)).
   + unfold atom, environment. cbn [val].
     rewrite (proj2 (Nat.ltb_ge (64+i) 64) ltac:(lia)).
     now replace (64+i-64)%nat with i by lia.
 - intros b i H. unfold used in H. apply andb_true_iff in H as [_ I].
   apply Nat.ltb_lt in I. apply B; assumption.
 - reflexivity.
Qed.

Local Lemma exact_spec env v : source_ok used env v -> satisfies v O long ->
 bit_spec (v (Wire 201)) (torsion_roots (val env px) (val env py)).
Proof.
 intros S G. assert (Empty : state_ok env v (fun _=>None)) by (intros i a H;discriminate).
 pose proof (verify_sound used _ _ _ _ _ _ S Empty G exact_arithmetic) as Cuts.
 unfold plan in Cuts.
 inversion_clear Cuts as [|? ? IY Cuts']. inversion_clear Cuts' as [|? ? X Cuts].
 inversion_clear Cuts as [|? ? Sum Cuts']. inversion_clear Cuts' as [|? ? Diff Rest].
 cbn [snd] in IY,X,Sum,Diff.
 destruct exact_shape as [_ [ZI [ZX [ZS [ZD [O1 [O2 O3]]]]]]].
 let c := match type of IY with claim _ ?c => c end in
 pose proof (zero_gate_result used _ _ _ _ c S G ZI IY eq_refl) as BI.
 let c := match type of X with claim _ ?c => c end in
 pose proof (zero_gate_result used _ _ _ _ c S G ZX X eq_refl) as BX.
 let c := match type of Sum with claim _ ?c => c end in
 pose proof (zero_gate_result used _ _ _ _ c S G ZS Sum eq_refl) as BS.
 let c := match type of Diff with claim _ ?c => c end in
 pose proof (zero_gate_result used _ _ _ _ c S G ZD Diff eq_refl) as BD.
 change (v(Wire 135)=bit_of_zero(val env iy)) in BI.
 change (v(Wire 141)=bit_of_zero(val env xx)) in BX.
 change (v(Wire 193)=bit_of_zero(val env total)) in BS.
 change (v(Wire 200)=bit_of_zero(val env diff)) in BD.
 pose proof (G _ _ O1) as A; pose proof (G _ _ O2) as B; pose proof (G _ _ O3) as D.
 cbn [Nat.add denote] in A,B,D. rewrite D,B,A,BI,BX,BS,BD.
 destruct IY as [IY _], X as [X _], Sum as [Sum _], Diff as [Diff _].
 cbn [base target] in *. fold iy xx total diff in *.
 change (represents (val env iy) (sqrt_m1 * val env py)) in IY.
 change (represents (val env total) (val env iy + val env xx)) in Sum.
 assert (Minus : represents (val env diff) (val env iy - val env xx)).
 { replace (val env iy - val env xx) with (val env (minus iy xx))
    by (cbn [minus val]; ring). exact Diff. }
 pose proof (ctrans _ _ _ Sum (cplus _ _ _ _ IY X)) as Sum'.
 pose proof (ctrans _ _ _ Minus (cminus _ _ _ _ IY X)) as Diff'.
 exact (four_zero_bits _ _ _ _ _ _ IY X Sum' Diff').
Qed.

Theorem exact_lane p initial j : (j<8)%nat -> bounded p ->
 bit_spec (value j long (inputs p j) (initial j) (Wire 201))
   (torsion_roots (cx (point_values p j)) (cy (point_values p j))).
Proof.
 intros J B. apply (exact_spec (environment p j (evaluate j long O (inputs p j) (initial j) (fun _=>0)))).
 - now apply sources.
 - apply evaluated_gates, (proj1 exact_shape).
Qed.
