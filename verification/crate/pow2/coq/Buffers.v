From Coq Require Import ZArith List Lia.
Require Import Pow2Caller.
Require Import FieldSpec Lane Chain.
Open Scope Z_scope.

Lemma get_output sq mul c a b scratch i j : (j<8)%nat ->
 cell (execute8 sq mul c a b scratch) i j =
 execute sq mul c (input_lane a b j) (scratch j) i.
Proof. intros J. unfold cell at 1; unfold execute8.
 assert (j=((i*8+j) mod 8)%nat) as <- by (apply Nat.mod_unique with (q:=i);lia).
 assert (i=((i*8+j)/8)%nat) as <- by (apply Nat.div_unique with (r:=j);lia).
 reflexivity. Qed.
Lemma packed_output sq mul c a b scratch i j : (j<8)%nat ->
 field_at (execute8 sq mul c a b scratch) i j =
 pack (execute sq mul c (input_lane a b j) (scratch j)) i.
Proof. intro J; unfold field_at,pack,limbs; repeat rewrite get_output by assumption; reflexivity. Qed.
Theorem buffers_correct sq mul c :
 check_kernel true sq=true -> check_kernel false mul=true -> check_chain c=true ->
 forall a b scratch, pow2_spec a b (execute8 sq mul c a b scratch).
Proof.
 intros Q M T a b scratch H side j J.
 assert (B:bounded Raw (input_lane a b j)).
 { intros i I. unfold cell in H. unfold input_lane; destruct (Nat.ltb i 5) eqn:L.
   - apply Nat.ltb_lt in L. specialize (H i j L J). cbn [limit]; unfold imax;lia.
   - apply Nat.ltb_ge in L. specialize (H (i-5)%nat j ltac:(lia) J).
     cbn [limit]; unfold imax;lia. }
 pose proof (pow2_correct _ _ _ Q M T _ (scratch j) B) as [R E].
 destruct side; cbn zeta; split.
 - intros i I. rewrite get_output by auto. specialize (R (5+i)%nat ltac:(lia)).
   do 5 (destruct i as [|i];[exact R|]);lia.
 - rewrite packed_output by auto. apply (E 5%nat);auto.
 - intros i I. rewrite get_output by auto. specialize (R i ltac:(lia)).
   do 5 (destruct i as [|i];[exact R|]);lia.
 - rewrite packed_output by auto. apply (E 0%nat);auto.
Qed.
