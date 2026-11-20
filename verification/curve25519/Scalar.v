From Coq Require Import List ZArith Lia Ring.
Import ListNotations. Open Scope Z_scope.

Definition L : Z := 2^252 + 27742317777372353535851937790883648493.
Lemma L_positive : 0<L. Proof. unfold L;lia. Qed.
Definition canonical_scalar x := 0 <= x < L.
Lemma canonical_residue n : canonical_scalar (n mod L).
Proof. apply Z.mod_pos_bound, L_positive. Qed.

Lemma canonical x : 0<=x<2*L ->
 (if x<?L then x else x-L)=x mod L.
Proof.
 intros Bounds;pose proof L_positive;destruct(x<?L)eqn:E.
 - apply Z.ltb_lt in E;rewrite Z.mod_small by lia;reflexivity.
 - apply Z.ltb_ge in E;apply Z.mod_unique with(q:=1);[left;lia|ring].
Qed.
