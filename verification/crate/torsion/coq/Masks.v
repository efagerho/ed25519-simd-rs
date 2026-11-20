From Coq Require Import List ZArith Bool Lia.
From Curve25519 Require Import Field Radix51.
From Machine Require Import isa.Instructions execution.MaskTrace execution.CircuitFacts.
From ProofArithmetic Require Import Expressions.
From Ed25519Simd.Torsion Require Import Zero Arithmetic Check Schedule.
Import ListNotations. Local Open Scope Z_scope.

Local Open Scope nat_scope.
Definition zero_gates base start := let r j:=Wire(slot base j) in
 [AddQ (r 0) (Lit 18); AndQ (r 1) (r 2); AndQ (r 3) (r 4);
  AndQ (Wire start) (Wire(start+1)); AndQ (Wire(start+3)) (Wire(start+2));
  EqQ (Wire(start+4)) (Lit(radix-1))].
Definition slice n len (gs:circuit) := firstn len (skipn n gs).
Lemma slice_facts v gs n len : satisfies v O gs -> satisfies v n (slice n len gs).
Proof.
 intros G i g H. apply (G (n+i)). unfold slice in H.
 rewrite <- (firstn_skipn n gs). apply nth_error_In in H as I.
 assert (n <= length gs).
 { destruct (le_dec n (length gs));auto. rewrite skipn_all2 in I by lia;destruct len;contradiction. }
 rewrite nth_error_app2, length_firstn,Nat.min_l by (rewrite ?length_firstn;lia).
 replace (n+i-n) with i by lia. rewrite <- (firstn_skipn len (skipn n gs)).
 rewrite nth_error_app1; [exact H|apply nth_error_Some;congruence].
Qed.

Local Open Scope Z_scope.
Definition bit_of_zero z := if z mod prime =? 0 then 1 else 0.
Lemma zero_gate_result env v gs n c : source_ok env v -> satisfies v O gs ->
 slice n 6 gs = zero_gates (base c) n -> claim env c -> needs_positive (witness c)=true ->
 v(Wire(n+5)) = bit_of_zero (val env (field_expr(base c))).
Proof.
 intros [Src [_ LitOK]] G Seq [Field [B Pos]] Needs. specialize (Pos Needs).
 pose proof (slice_facts _ _ n 6 G) as S; rewrite Seq in S.
 pose proof (S 0%nat _ eq_refl) as A. pose proof(S 1%nat _ eq_refl) as BC.
 pose proof (S 2%nat _ eq_refl) as DE. pose proof(S 3%nat _ eq_refl) as ABC.
 pose proof (S 4%nat _ eq_refl) as ABCDE. pose proof(S 5%nat _ eq_refl) as EQ.
 cbn [denote] in A,BC,DE,ABC,ABCDE,EQ.
 rewrite Nat.add_0_r in A. rewrite EQ,ABCDE,ABC,BC,DE,A,!LitOK.
 unfold Logic.vpandq,Arithmetic.vpaddq,X86.low64; rewrite Z.land_ones by lia.
 assert (Words : forall j,v(Wire(slot(base c) j))=env (64+slot(base c) j)%nat).
 { intro j; symmetry;exact (Src (Wire(slot(base c) j)) eq_refl). }
 rewrite !Words;unfold field_expr,pack_expr,pack_f,var in *; cbn [val] in *.
 set (a:=env (64+slot(base c) 0)%nat) in *;set (b:=env (64+slot(base c) 1)%nat) in *.
 set (d2:=env (64+slot(base c) 2)%nat) in *;set (d3:=env (64+slot(base c) 3)%nat) in *.
 set (d4:=env (64+slot(base c) 4)%nat) in *.
 pose proof(B 0%nat ltac:(lia)) as Ba;pose proof(B 1%nat ltac:(lia)) as Bb;
 pose proof(B 2%nat ltac:(lia)) as Bc;pose proof(B 3%nat ltac:(lia)) as Bd;
 pose proof(B 4%nat ltac:(lia)) as Be. fold a in Ba;fold b in Bb;fold d2 in Bc;fold d3 in Bd;fold d4 in Be.
 rewrite Z.mod_small by (unfold limit,radix in Ba;lia).
 fold (zero_bits a b d2 d3 d4). fold (packed a b d2 d3 d4) in *.
 assert (H : zero_bits a b d2 d3 d4=radix-1 <-> packed a b d2 d3 d4 mod prime=0).
 { apply zero_bits_correct; unfold packed,limit,radix,prime in *;lia. }
 unfold bit_of_zero. destruct (Z.eqb_spec (zero_bits a b d2 d3 d4) (radix-1)),
  (Z.eqb_spec (packed a b d2 d3 d4 mod prime) 0); tauto || congruence.
Qed.

Definition early_cut := Cut 155 (minus (Times px ry) (Times py rx)) FirstPositive.
Lemma early_checked : verify [(160%nat,early_cut)] short O (fun _=>None)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma ordered_paths : ordered O short=true /\ ordered O long=true.
Proof. vm_compute;auto. Qed.
Lemma early_shape : slice 160 6 short = zero_gates 155 160.
Proof. vm_compute;reflexivity. Qed.
Lemma long_shapes :
 slice 751 6 long=zero_gates 746 751 /\ slice 757 6 long=zero_gates 562 757 /\
 slice 809 6 long=zero_gates 789 809 /\ slice 816 6 long=zero_gates 804 816 /\
 nth_error long 763=Some(OrK (Wire 756)(Wire 762)) /\
 nth_error long 815=Some(OrK (Wire 763)(Wire 814)) /\
 nth_error long 822=Some(OrK (Wire 815)(Wire 821)).
Proof. vm_compute;repeat split. Qed.
