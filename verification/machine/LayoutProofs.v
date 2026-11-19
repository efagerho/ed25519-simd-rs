From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Instructions ProgramLayout.
Import ListNotations.
Open Scope Z_scope.

Definition section_bytes p s := match s with
 | Code b => block_bytes p b | Padding bytes => bytes end.
Definition section_image p ss := flat_map (section_bytes p) ss.
Definition static_targets p b := let n:=after p b in match terminator b with
 | Ret => [] | CallRel32 d | JneRel8 d => [n+d;n] | _ => [n] end.

Lemma lookup_member ss addr b : lookup ss addr=Some b ->
 In (Code b) ss /\ start b=addr.
Proof.
 induction ss as [|s ss IH];[discriminate|].
 destruct s as [head|bytes];cbn [lookup].
 2: { intros H;destruct(IH H)as[M E];split;[now right|exact E]. }
 destruct (start head=?addr) eqn:E.
 - intros [= <-];apply Z.eqb_eq in E;split;[now left|exact E].
 - intro H;destruct(IH H)as[M E'];split;[now right|exact E'].
Qed.

Lemma layout_member p pc ss b : layout_ok p pc ss=true -> In (Code b) ss ->
 pc<=start b /\ start b<after p b /\
 Forall (fun op=>valid_op p op=true) (body b) /\ valid_exit p b=true.
Proof.
 revert pc;induction ss as [|s ss IH];intros pc H Member;[contradiction|].
 destruct s as [head|bytes];cbn [layout_ok] in H;
 repeat rewrite andb_true_iff in H.
 - destruct H as [[[[Start Size] Ops] Targets] Tail].
   apply Z.eqb_eq in Start;apply Z.ltb_lt in Size.
   destruct Member as [E|Member].
   + injection E as <-;repeat split;try lia;auto.
     now rewrite Forall_forall,<-forallb_forall.
   + destruct(IH _ Tail Member)as[L Rest];split;[lia|exact Rest].
 - destruct H as [Bytes Tail];destruct Member as [E|Member];[discriminate|].
   destruct(IH _ Tail Member)as[L Rest];split;[lia|exact Rest].
Qed.

Lemma layout_binding p pc ss b : layout_ok p pc ss=true -> In (Code b) ss ->
 exists pre post, section_image p ss=pre++block_bytes p b++post /\
 start b=pc+Z.of_nat(length pre).
Proof.
 revert pc;induction ss as [|s ss IH];intros pc H Member;[contradiction|].
 destruct s as [head|bytes];cbn [layout_ok] in H;
 repeat rewrite andb_true_iff in H.
 - destruct H as [[[[Start Size] Ops] Targets] Tail];apply Z.eqb_eq in Start.
   destruct Member as [E|Member].
   + injection E as <-;exists [],(section_image p ss);cbn;split;[reflexivity|lia].
   + destruct(IH _ Tail Member)as[pre[post[Bytes Position]]].
     exists(block_bytes p head++pre),post;split.
     * cbn [section_image flat_map section_bytes];fold(section_image p ss).
       rewrite Bytes;now rewrite !app_assoc.
     * rewrite length_app,Nat2Z.inj_add;unfold after in Position;lia.
 - destruct H as [Valid Tail];destruct Member as [E|Member];[discriminate|].
   destruct(IH _ Tail Member)as[pre[post[Bytes Position]]].
   exists(bytes++pre),post;split.
   + cbn [section_image flat_map section_bytes];fold(section_image p ss).
     rewrite Bytes;now rewrite !app_assoc.
   + rewrite length_app,Nat2Z.inj_add;lia.
Qed.

Lemma layout_fetch p pc ss b : layout_ok p pc ss=true -> In (Code b) ss ->
 lookup ss (start b)=Some b.
Proof.
 revert pc;induction ss as [|s ss IH];intros pc H Member;[contradiction|].
 destruct s as [head|bytes];cbn [layout_ok] in H;
 repeat rewrite andb_true_iff in H.
 - destruct H as [[[[Start Size] Ops] Targets] Tail];apply Z.eqb_eq in Start;apply Z.ltb_lt in Size.
   cbn [lookup];destruct Member as [E|Member].
   + injection E as <-;now rewrite Z.eqb_refl.
   + destruct(start head=?start b)eqn:E;[|now apply(IH _ Tail)].
     apply Z.eqb_eq in E;pose proof(layout_member _ _ _ _ Tail Member)as[L _];lia.
 - destruct H as [Valid Tail];destruct Member as [E|Member];[discriminate|].
   now apply(IH _ Tail).
Qed.

Lemma layout_separation p pc ss a b : layout_ok p pc ss=true ->
 In(Code a)ss -> In(Code b)ss -> a<>b ->
 after p a<=start b \/ after p b<=start a.
Proof.
 revert pc;induction ss as [|s ss IH];intros pc H A B Different;[contradiction|].
 destruct s as [head|bytes];cbn [layout_ok] in H;
 repeat rewrite andb_true_iff in H.
 - destruct H as [[[[Start Size] Ops] Targets] Tail].
   destruct A as [E|A],B as[F|B].
   + congruence.
   + injection E as <-;left;exact(proj1(layout_member _ _ _ _ Tail B)).
   + injection F as <-;right;exact(proj1(layout_member _ _ _ _ Tail A)).
   + now apply(IH _ Tail).
 - destruct H as [Valid Tail];destruct A as[E|A],B as[F|B];try discriminate.
   now apply(IH _ Tail).
Qed.

Lemma starts_block_sound p addr : starts_block p addr=true ->
 exists b, lookup (sections p) addr=Some b.
Proof. unfold starts_block;destruct(lookup (sections p) addr);[eauto|discriminate]. Qed.
Lemma exit_targets p b : valid_exit p b=true ->
 Forall (fun addr=>exists target,lookup(sections p)addr=Some target) (static_targets p b).
Proof.
 unfold valid_exit,static_targets;destruct(terminator b);intro H;
 repeat rewrite andb_true_iff in H;repeat constructor;
 apply starts_block_sound;tauto.
Qed.
Lemma resolved_body p ops : Forall (fun op=>valid_op p op=true) ops ->
 forall id,In(VectorCode id)ops ->exists code,
 lookup_fragment p id=Some code /\ Forall (fun i=>encodable i=true) code.
Proof.
 rewrite Forall_forall;intros Ops id Member;specialize(Ops _ Member).
 cbn [valid_op] in Ops;destruct(lookup_fragment p id)as[code|]eqn:F;[|discriminate].
 exists code;split;[reflexivity|now rewrite Forall_forall,<-forallb_forall].
Qed.

(* Semantic facts consumed by auditors, rather than only a successful Boolean
   check. Instruction encodings still require independent ISA validation. *)
Record program_layout p : Prop := {
 layout_entry : exists b, lookup(sections p)0=Some b;
 layout_bytes : forall b,In(Code b)(sections p) -> exists pre post,
   image p=pre++block_bytes p b++post /\ start b=Z.of_nat(length pre);
 layout_nonempty : forall b,In(Code b)(sections p) -> start b<after p b;
 layout_operands : forall b,In(Code b)(sections p) -> Forall(fun op=>valid_op p op=true)(body b);
 layout_lookup : forall b,In(Code b)(sections p) -> lookup(sections p)(start b)=Some b;
 layout_disjoint : forall a b,In(Code a)(sections p) -> In(Code b)(sections p) -> a<>b ->
   after p a<=start b \/ after p b<=start a;
 layout_fragments : forall b id,In(Code b)(sections p) -> In(VectorCode id)(body b) ->
   exists code,lookup_fragment p id=Some code /\ Forall(fun i=>encodable i=true)code;
 layout_targets : forall b,In(Code b)(sections p) ->
   Forall(fun addr=>exists target,lookup(sections p)addr=Some target)(static_targets p b)
}.
Theorem valid_program_sound p : valid_program p=true -> program_layout p.
Proof.
 unfold valid_program;rewrite andb_true_iff;intros[Entry Layout];constructor.
 - now apply starts_block_sound.
 - intros b B;destruct(layout_binding _ _ _ _ Layout B)as[pre[post[Bytes Position]]].
   exists pre,post;split;[exact Bytes|lia].
 - intros b B;exact(proj1(proj2(layout_member _ _ _ _ Layout B))).
 - intros b B;exact(proj1(proj2(proj2(layout_member _ _ _ _ Layout B)))).
 - intros b B;now apply(layout_fetch _ _ _ _ Layout).
 - intros a b A B D;exact(layout_separation _ _ _ _ _ Layout A B D).
 - intros b id B I;eapply resolved_body;[|exact I].
   exact(proj1(proj2(proj2(layout_member _ _ _ _ Layout B)))).
 - intros b B;apply exit_targets;exact(proj2(proj2(proj2(layout_member _ _ _ _ Layout B)))).
Qed.
