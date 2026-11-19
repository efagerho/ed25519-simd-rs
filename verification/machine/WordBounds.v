From Coq Require Import ZArith List Bool Lia.
From Machine Require Import Instructions Blocks MemoryTrace.
Import ListNotations.
Open Scope Z_scope.

(* Canonical representatives of architectural qwords. Symbolic pointers and
   PCs remain separate from integer operands; their byte interpretation lives
   in FlatMemory. Only the eight architectural lanes are constrained. *)
Definition word64 x := 0 <= x < 2^64.
Definition scalar_words v := match v with Int n => word64 n | _ => True end.
Definition gpr_words (regs : nat -> scalar) := forall r, scalar_words (regs r).
Definition data_words d :=
 (forall j r, (j < 8)%nat -> word64 (zmm d j r)) /\
 (forall a j, (j < 8)%nat -> word64 (memory d a j)).
Definition state_words (s : state) := gpr_words (gpr (fst s)) /\ data_words (snd s).

Lemma mod64_word x : word64 (x mod 2^64).
Proof. apply Z.mod_pos_bound; reflexivity. Qed.
Lemma mod32_word x : word64 (x mod 2^32).
Proof. pose proof (Z.mod_pos_bound x (2^32) ltac:(reflexivity)); unfold word64; lia. Qed.
Lemma low64_word x : word64 (X86.low64 x).
Proof. unfold X86.low64; rewrite Z.land_ones by lia; apply mod64_word. Qed.
Lemma low64_id x : word64 x -> X86.low64 x = x.
Proof. unfold word64,X86.low64; rewrite Z.land_ones by lia; apply Z.mod_small. Qed.

Lemma xor_word a b : word64 a -> word64 b -> word64 (Z.lxor a b).
Proof.
 intros A B. assert (E : X86.low64 (Z.lxor a b) = Z.lxor (X86.low64 a) (X86.low64 b)).
 { apply Z.bits_inj; intro k. unfold X86.low64. rewrite !Z.land_spec,!Z.lxor_spec,!Z.land_spec.
   destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones 64) k); reflexivity. }
 rewrite (low64_id _ A),(low64_id _ B) in E. rewrite <-E; apply low64_word.
Qed.
Lemma and_word a b : word64 b -> word64 (Z.land a b).
Proof.
 intro B. rewrite <-(low64_id _ B). unfold X86.low64. rewrite Z.land_assoc.
 apply low64_word.
Qed.
Lemma shr_word a n : word64 a -> word64 (Shift.vpsrlq a n).
Proof.
 intros [A B]. unfold Shift.vpsrlq,word64. rewrite Z.shiftr_div_pow2 by lia.
 assert (P : 0 < 2^Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
 split; [apply Z.div_pos; lia|].
 assert (a / 2^Z.of_nat n <= a) by (apply Z.div_le_upper_bound; nia). lia.
Qed.

Lemma bits_words load regs dst op :
 (forall b d, word64 (load b d)) -> (forall r, word64 (regs r)) ->
 word64 (bits load regs dst op).
Proof.
 intros L R. destruct op; cbn [bits];
 try apply low64_word; try apply R; try apply L;
 try (apply xor_word; apply R); try (apply and_word; apply R);
 try (apply shr_word; apply R).
Qed.
Lemma run_words load code regs :
 (forall b d, word64 (load b d)) -> (forall r, word64 (regs r)) ->
 forall r, word64 (run load code regs r).
Proof.
 intros L. revert regs. induction code as [|[dst op] rest IH]; intros regs R; [exact R|].
 cbn [run]. apply IH. intro r; unfold put. destruct (Nat.eqb dst r); auto using bits_words.
Qed.

Definition effect_words e := match e with Broadcast _ n => word64 n | _ => True end.
Lemma effect_preserves_words p e d :
 effect_words e -> data_words d -> data_words (apply_effect p d e).
Proof.
 intros E [R M]. destruct e; split; intros; cbn [apply_effect register_write zmm memory];
 try (unfold put; destruct (Nat.eqb _ _)); auto.
 - destruct (ptr_eq _ _); auto.
 - destruct (Nat.ltb _ _ && Nat.leb _ _); [unfold word64; lia|auto].
 - apply run_words; [|auto]. intros b disp. unfold effective_load.
   destruct (find _ _) as [[base a]|]; [apply M; assumption|unfold word64; lia].
Qed.
Lemma effects_preserve_words p es d :
 Forall effect_words es -> data_words d -> data_words (effects p es d).
Proof.
 intro E; revert d; induction E; intros d D; [exact D|].
 apply IHE, effect_preserves_words; assumption.
Qed.

Lemma put_gpr_words regs r v :
 gpr_words regs -> scalar_words v -> gpr_words (put regs r v).
Proof. intros R V k; unfold put. destruct (Nat.eqb r k); auto. Qed.

Lemma op_preserves_words p l c op mid es :
 gpr_words (gpr c) -> exec_op p l c op = Some (mid,es) ->
 gpr_words (gpr mid) /\ Forall effect_words es.
Proof.
 intro R. destruct op; cbn [exec_op];
 repeat match goal with |- context [match ?v with _ => _ end] => destruct v eqn:? end;
 intro H; try discriminate; inversion H; subst; cbn [gpr set_gpr]; split;
 try exact R; try (constructor; [|constructor]); try constructor;
 try (apply put_gpr_words; [exact R|]); cbn [scalar_words effect_words];
 auto using mod32_word,mod64_word.
 all: match goal with H : gpr ?c 0%nat = Int ?n |- _ =>
   specialize (R 0%nat); rewrite H in R; cbn [scalar_words] in R; unfold word64 in R; lia end.
Qed.
Lemma body_preserves_words p l c ops mid es :
 gpr_words (gpr c) -> exec_body p l c ops = Some (mid,es) ->
 gpr_words (gpr mid) /\ Forall effect_words es.
Proof.
 revert c mid es; induction ops as [|op rest IH]; intros c mid es R H; cbn [exec_body] in H.
 - inversion H; subst; split; auto; constructor.
 - destruct (exec_op p l c op) as [[next head]|] eqn:O; try discriminate.
   destruct (exec_body p l next rest) as [[last tail]|] eqn:B; try discriminate.
   inversion H; subst. destruct (op_preserves_words _ _ _ _ _ _ R O) as [N E].
   destruct (IH _ _ _ N B) as [F T]. split; [exact F|now apply Forall_app].
Qed.
Lemma transfer_preserves_words l c next e last :
 gpr_words (gpr c) -> transfer l c next e = Some last -> gpr_words (gpr last).
Proof.
 intro R. destruct e; cbn [transfer];
 repeat match goal with |- context [match ?v with _ => _ end] => destruct v eqn:? end;
 intro H; try discriminate; inversion H; subst; cbn [gpr];
 auto.
 all: repeat apply put_gpr_words; cbn [scalar_words]; auto using mod64_word.
 all: unfold stack_word;apply mod64_word.
Qed.
Theorem step_preserves_words p l s t :
 state_words s -> step p l s = Some t -> state_words t.
Proof.
 destruct s as [c d]. intros [R D]. unfold step,dispatch; cbn [fst snd].
 destruct (rip c) as [pc | | saved]; try discriminate.
 destruct (lookup (sections p) pc) as [b|]; [|discriminate].
 unfold block_control. destruct (exec_body p l c (body b)) as [[mid es]|] eqn:B; [|discriminate].
 destruct (transfer l mid (after p b) (terminator b)) as [last|] eqn:T; [|discriminate].
 intros [= <-]. destruct (body_preserves_words _ _ _ _ _ _ R B) as [M E].
 split; [eapply transfer_preserves_words; eassumption|now apply effects_preserve_words].
Qed.
Theorem execution_preserves_words p l s t :
 reaches p l s t -> state_words s -> state_words t.
Proof. intro R; induction R; intro W; auto; apply IHR; eapply step_preserves_words; eassumption. Qed.

Lemma path_preserves_words fuel p l c last es :
 gpr_words (gpr c) -> path fuel p l c = Some (last,es) ->
 gpr_words (gpr last) /\ Forall effect_words es.
Proof.
 revert c last es; induction fuel as [|n IH]; intros c last es W H;
 cbn [path] in H; destruct (rip c) eqn:PC; try discriminate;
 try (inversion H; subst; split; [exact W|constructor]).
 unfold dispatch in H; rewrite PC in H.
 destruct (lookup (sections p) address) as [b|]; [|discriminate].
 unfold block_control in H.
 destruct (exec_body p l c (body b)) as [[mid ops]|] eqn:B; [|discriminate].
 destruct (transfer l mid (after p b) (terminator b)) as [next|] eqn:T; [|discriminate].
 destruct (path n p l next) as [[fin tail]|] eqn:P; [|discriminate].
 inversion H; subst. destruct (body_preserves_words _ _ _ _ _ _ W B) as [M O].
 destruct (IH _ _ _ (transfer_preserves_words _ _ _ _ _ M T) P) as [L E].
 split; [exact L|now apply Forall_app].
Qed.

Theorem recorded_prefix_words fuel p l c last es d pre tail :
 record_path fuel p l c = Some (last,es) -> state_words (c,d) -> es = pre ++ tail ->
 data_words (effects p (data_effects pre) d).
Proof.
 intros R [G D] E. destruct (record_path_sound _ _ _ _ _ _ R) as [P _].
 destruct (path_preserves_words _ _ _ _ _ _ G P) as [_ W].
 rewrite E in W. unfold data_effects in W; rewrite flat_map_app in W.
 apply Forall_app in W as [W _]. now apply effects_preserve_words.
Qed.
