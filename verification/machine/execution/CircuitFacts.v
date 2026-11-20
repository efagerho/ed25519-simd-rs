From Coq Require Import List Bool Arith Lia ZArith.
From Machine Require Import isa.Instructions execution.MaskTrace.
Import ListNotations. Local Open Scope nat_scope.

(* Every supported instruction with a ZMM destination from the common
   instruction set computes exactly its shared lane semantics. *)
Lemma lower_vector_correct read regs dst op e (v : arg -> Z) mem :
  (forall base disp a, read base disp = Some a -> v a = mem base disp) ->
  v (Lit 0) = 0%Z ->
  lower_vector read regs dst op = Some e ->
  match e with Existing a => v a | Compute g => denote v g end =
  bits mem (fun r => v (regs r)) dst op.
Proof.
  intros Load Zero. destruct op; cbn [lower_vector]; try discriminate;
    try (intros [= <-]; reflexivity).
  - destruct (read base disp) as [a|] eqn:E; [|discriminate].
    intros [= <-]. apply (Load _ _ _ E).
  - destruct (Nat.eqb_spec a b) as [->|N]; [|discriminate].
    intros [= <-]. cbn [bits]. unfold Logic.vpxorq. now rewrite Z.lxor_nilpotent.
Qed.

Fixpoint earlier (n:nat) a := match a with Wire i=>Nat.ltb i n
 | UpperCleared p=>earlier n p | _=>true end.
Definition arguments g := match g with
 | AddQ a b | SubQ a b | MulQ a b | AndQ a b | EqQ a b | OrK a b=>[a;b]
 | ShiftQ a _=>[a] | MaddQ _ acc a b=>[acc;a;b] end.
Fixpoint ordered n gs := match gs with []=>true | g::t=>
 forallb (earlier n) (arguments g) && ordered (S n) t end.

Lemma evaluate_preserves lane gs n inputs initial w i : i<n ->
 evaluate lane gs n inputs initial w i = w i.
Proof.
 revert n w; induction gs as [|g gs IH]; intros n w H; [reflexivity|].
 cbn [evaluate]; rewrite IH by lia. unfold put.
 destruct (Nat.eqb_spec n i); [lia|reflexivity].
Qed.

Local Lemma operand_ext lane inp ini w w' n a :
 (forall i,i<n -> w i=w' i) -> earlier n a=true ->
 operand lane inp ini w a=operand lane inp ini w' a.
Proof.
 intros E; induction a; cbn [earlier operand]; auto. rewrite Nat.ltb_lt; apply E.
 destruct (lane <? 2); auto.
Qed.

Definition satisfies v n gs := forall i g, nth_error gs i=Some g ->
 v (Wire (n+i)) = denote v g.

Lemma evaluated_gates lane gs n inp ini w : ordered n gs=true ->
 satisfies (operand lane inp ini (evaluate lane gs n inp ini w)) n gs.
Proof.
 revert n w; induction gs as [|g gs IH]; intros n w H i h L.
 - destruct i; discriminate.
 - cbn [ordered] in H; apply Bool.andb_true_iff in H as [Refs Rest].
   cbn [evaluate]. destruct i as [|i].
   + inversion L; subst h. rewrite Nat.add_0_r. cbn [operand].
     rewrite evaluate_preserves by lia. unfold put at 1; rewrite Nat.eqb_refl.
     set (w' := put w n (denote (operand lane inp ini w) g)).
     assert (E : forall a, In a (arguments g) ->
        operand lane inp ini w a=operand lane inp ini (evaluate lane gs (S n) inp ini w') a).
     { intros a A. apply (operand_ext _ _ _ _ _ n).
       - intros j J. rewrite evaluate_preserves by lia. unfold w',put.
         destruct (Nat.eqb_spec n j); [lia|reflexivity].
       - now apply forallb_forall with (x:=a) in Refs. }
     destruct g; cbn [denote]; f_equal; try (apply E; simpl; auto).
     all: try (rewrite !E by (simpl;auto); reflexivity).
   + replace (n+S i) with (S n+i) by lia. apply IH; assumption.
Qed.

Lemma mask_word_bits n f : (forall j,j<n -> f j=0%Z \/ f j=1%Z) ->
 (0 <= mask_word n f < 2^Z.of_nat n)%Z /\
 forall j, j<n -> (Z.testbit (mask_word n f) (Z.of_nat j)=true <-> f j=1%Z).
Proof.
 induction n; intro H; [cbn; split; [lia|lia]|].
 destruct (IHn ltac:(intros;apply H;lia)) as [Range Bits].
 cbn [mask_word]; rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
 destruct (H n ltac:(lia)) as [A|A]; rewrite A; rewrite ?Z.mul_0_l,?Z.mul_1_l,?Z.add_0_r.
 - split; [lia|]. intros j J. destruct (Nat.eq_dec j n) as [->|N]; [|apply Bits;lia].
   assert (Z.testbit (mask_word n f) (Z.of_nat n)=false).
   { rewrite Z.testbit_false by lia. rewrite Z.div_small by lia. reflexivity. }
   rewrite H0,A. intuition discriminate.
 - split; [lia|]. intros j J.
   replace (mask_word n f + 2^Z.of_nat n)%Z with
    (1*2^Z.of_nat n + mask_word n f)%Z by ring.
   destruct (Nat.eq_dec j n) as [->|N].
   + rewrite Z.testbit_true by lia. rewrite Z.div_add_l, Z.div_small by lia.
     rewrite A. reflexivity.
   + rewrite <- (Z.mod_pow2_bits_low _ (Z.of_nat n)) by lia.
     rewrite Z.add_comm, Z.mod_add, Z.mod_small by lia. apply Bits; lia.
Qed.
