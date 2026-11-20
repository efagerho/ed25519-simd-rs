From Coq Require Import List ZArith Lia Ring Bool.
From Machine Require Import execution.MaskTrace execution.CircuitFacts.
From ProofArithmetic Require Import Expressions.
From Curve25519 Require Import Field Radix51 Edwards Torsion.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Torsion Require Import Audit Schedule Masks.
From Ed25519Simd.field51 Require Import Arithmetic Check.
Import ListNotations. Local Open Scope Z_scope.

Definition environment p r j (w:nat->Z) k :=
 if Nat.ltb k 32 then cell p k j else if Nat.ltb k 64 then cell r (k-32)%nat j else w (k-64)%nat.
Lemma sources lane p r ini w : (lane<8)%nat -> input_bounds p r ->
 source_ok input_used (environment p r lane w) (operand lane (inputs p r lane) ini w).
Proof.
 intros J Bounds;split; [|split].
 - intros a H;destruct a as [n|b i|k|i|a];try discriminate;cbn [atom operand val];try reflexivity.
   + cbn [supported_arg input_used] in H;apply andb_true_iff in H as [B I]; apply Nat.ltb_lt in I.
     unfold environment,inputs;apply orb_true_iff in B as [B|B].
     * apply Nat.eqb_eq in B;subst b;cbn [Nat.eqb];simpl Nat.add. rewrite (proj2(Nat.ltb_lt i 32) ltac:(lia));reflexivity.
     * apply andb_true_iff in B as [B _]; apply Nat.eqb_eq in B;subst b;cbn [Nat.eqb].
       rewrite (proj2(Nat.ltb_ge (32+i) 32) ltac:(lia)),(proj2(Nat.ltb_lt (32+i) 64) ltac:(lia)).
       replace (32+i-32)%nat with i by lia;reflexivity.
   + unfold environment. rewrite (proj2(Nat.ltb_ge (64+i) 32) ltac:(lia)), (proj2(Nat.ltb_ge (64+i) 64) ltac:(lia)).
     now replace (64+i-64)%nat with i by lia.
 - intros b i H;unfold input_used in H;apply andb_true_iff in H as [B I];apply Nat.ltb_lt in I.
   destruct(Bounds i lane I J) as [P R]. apply orb_true_iff in B as [B|B].
   + apply Nat.eqb_eq in B;subst b;exact P.
   + apply andb_true_iff in B as [B D]; apply Nat.eqb_eq in B;subst b;apply R.
     apply orb_true_iff in D;rewrite Nat.ltb_lt,Nat.leb_le in D;exact D.
 - reflexivity.
Qed.

Definition qpoint env := Coordinates (val env px) (val env py) (val env pz) (val env pt).
Definition rpoint env := Coordinates (val env rx) (val env ry) 1 (val env rt).
Local Lemma val_minus env a b : val env (minus a b)=val env a-val env b.
Proof. cbn [minus val];ring. Qed.

Ltac cut_head facts name := pose proof (Forall_inv facts) as name; cbv beta iota delta [snd] in name; apply Forall_inv_tail in facts.
Ltac use_congruence := first [apply crefl | assumption |
  apply cplus;use_congruence |apply cminus;use_congruence |apply ctimes;use_congruence].
Local Lemma empty_ok env v : state_ok env v (fun _=>None).
Proof. intros i s H;discriminate. Qed.
Local Lemma early_spec env v : source_ok input_used env v -> satisfies v O short ->
 bit_spec (v(Wire 165)) (torsion_determinant (qpoint env) (rpoint env) mod prime=0).
Proof.
 intros S G. pose proof (verify_sound input_used _ _ _ _ _ _ S (empty_ok env v) G early_checked) as Cs.
 pose proof (Forall_inv Cs) as C. change (claim env early_cut) in C.
 pose proof (zero_gate_result input_used _ _ _ _ early_cut S G early_shape C eq_refl) as E.
 change (v(Wire 165)=bit_of_zero(val env det)) in E. rewrite E;apply zero_spec.
 destruct C as [D _]. change (represents (val env det) (val env (minus (Times px ry) (Times py rx)))) in D.
 rewrite val_minus in D; exact D.
Qed.

Local Lemma full_spec env v : source_ok input_used env v -> satisfies v O long ->
 bit_spec (v(Wire 822)) (torsion_check (qpoint env) (rpoint env)).
Proof.
 intros S G. pose proof (verify_sound input_used _ _ _ _ _ _ S (empty_ok env v) G scheduled_arithmetic) as Cs.
 unfold plan in Cs.
 cut_head Cs D. cut_head Cs A. cut_head Cs B. cut_head Cs H. cut_head Cs TT.
 cut_head Cs Gsum. cut_head Cs Minus. cut_head Cs X. cut_head Cs Y.
 cut_head Cs IY. cut_head Cs Sum. cut_head Cs Diff.
 destruct long_shapes as [ZI [ZX [ZS [ZD [O1 [O2 O3]]]]]].
 let c:=match type of IY with claim _ ?c => c end in
 pose proof (zero_gate_result input_used _ _ _ _ c S G ZI IY eq_refl) as BI.
 let c:=match type of X with claim _ ?c => c end in
 pose proof (zero_gate_result input_used _ _ _ _ c S G ZX X eq_refl) as BX.
 let c:=match type of Sum with claim _ ?c => c end in
 pose proof (zero_gate_result input_used _ _ _ _ c S G ZS Sum eq_refl) as BS.
 let c:=match type of Diff with claim _ ?c => c end in
 pose proof (zero_gate_result input_used _ _ _ _ c S G ZD Diff eq_refl) as BD.
 change (v(Wire 756)=bit_of_zero(val env iy)) in BI.
 change (v(Wire 762)=bit_of_zero(val env xx)) in BX.
 change (v(Wire 814)=bit_of_zero(val env sum)) in BS.
 change (v(Wire 821)=bit_of_zero(val env diff)) in BD.
 pose proof(G _ _ O1) as Or1;pose proof(G _ _ O2) as Or2;pose proof(G _ _ O3) as Or3.
 cbn [Nat.add denote] in Or1,Or2,Or3. rewrite Or3,Or2,Or1,BI,BX,BS,BD.
 destruct D as [D _], A as [A _], B as [B _], H as [H _], TT as [TT _],
  Gsum as [Gsum _], Minus as [Minus _], X as [X _], Y as [Y _], IY as [IY _],
  Sum as [Sum _], Diff as [Diff _].
 cbn [base target snd] in D,A,B,H,TT,Gsum,Minus,X,Y,IY,Sum,Diff.
 fold det in D; fold dy in A; fold sy in B; fold h in H; fold tt in TT;
 fold g in Gsum; fold f in Minus; fold xx in X; fold yy in Y; fold iy in IY;
 fold sum in Sum; fold diff in Diff.
 rewrite !val_minus in D,A,Minus,Diff.
 cbn [val] in D,A,B,H,TT,Gsum,Minus,X,Y,IY,Sum,Diff.
 set (e:=val env px*val env ry-val env py*val env rx) in *.
 set (hx:=(val env py-val env px)*(val env ry+val env rx)+e).
 set (z:=121666*val env pz). set (t:=121665*(val env pt*val env rt)).
 set (u:=e*(z-t)). set (s:=sqrt_m1*((z+t)*hx)).
 assert (Hh:represents (val env h) hx) by (eapply ctrans;[exact H|unfold hx;use_congruence]).
 assert (Ff:represents (val env f) (z-t)) by (eapply ctrans;[exact Minus|unfold z,t;use_congruence]).
 assert (Gg:represents (val env g) (z+t)) by (eapply ctrans;[exact Gsum|unfold z,t;use_congruence]).
 assert (Xu:represents (val env xx) u) by (eapply ctrans;[exact X|unfold u;use_congruence]).
 assert (Yv:represents (val env yy) ((z+t)*hx)) by (eapply ctrans;[exact Y|use_congruence]).
 assert (Is:represents (val env iy) s) by (eapply ctrans;[exact IY|unfold s;use_congruence]).
 assert (Su:represents (val env sum) (s+u)) by (eapply ctrans;[exact Sum|use_congruence]).
 assert (Di:represents (val env diff) (s-u)) by (eapply ctrans;[exact Diff|use_congruence]).
 exact (four_zero_bits _ _ _ _ _ _ Is Xu Su Di).
Qed.

Theorem early_lane p r initial j : (j<8)%nat -> input_bounds p r ->
 bit_spec (value j short (inputs p r j) (initial j) (Wire 165))
          (torsion_determinant (point_values p j) (point_values r j) mod prime=0).
Proof.
 intros J B. apply (early_spec (environment p r j (evaluate j short O (inputs p r j) (initial j) (fun _=>0)))).
 - now apply sources.
 - apply evaluated_gates,(proj1 ordered_paths).
Qed.
Theorem full_lane p r initial j : (j<8)%nat -> input_bounds p r ->
 bit_spec (value j long (inputs p r j) (initial j) (Wire 822))
          (torsion_check (point_values p j) (point_values r j)).
Proof.
 intros J B. apply (full_spec (environment p r j (evaluate j long O (inputs p r j) (initial j) (fun _=>0)))).
 - now apply sources.
 - apply evaluated_gates,(proj2 ordered_paths).
Qed.
