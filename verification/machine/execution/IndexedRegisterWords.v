From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.IndexedLoad execution.LinkedCalls execution.IndexedLoads execution.ProjectionWords.
From Machine Require execution.Packed.
Local Open Scope nat_scope.

Definition words st:=(forall r,indexed (gp st r)=true) /\
  forall r j,j<8 -> indexed (vec st r j)=true.
Lemma update {A} (old:nat->A) r x (P:A->Prop) : (forall i,P(old i)) -> P x ->
 forall i,P(Packed.update old r x i).
Proof. intros H X i;unfold Packed.update;destruct (_=?_)%nat;auto. Qed.
Lemma unpack_range high j : j<8 -> 2*(j/2)+(if high:bool then 1 else 0)<8.
Proof. intros J;assert (j/2<4) by (apply Nat.div_lt_upper_bound;lia);destruct high;lia. Qed.
Lemma shuffle_range imm j : 2*(imm/4^(j/2) mod 4)+j mod 2<8.
Proof. pose proof(Nat.mod_upper_bound (imm/4^(j/2)) 4 ltac:(lia));pose proof(Nat.mod_upper_bound j 2 ltac:(lia));lia. Qed.

Lemma step_words st op : words st -> words (step st op).
Proof.
 intros [G V];destruct op;split;cbn [step vec gp words];try exact G;try exact V.
 all: try solve [apply (update _ _ _ (fun t=>indexed t=true));[exact G|reflexivity]].
 all: try solve [apply (update _ _ _ (fun t=>indexed t=true));[exact G|match goal with b:bool|-_=>destruct b;reflexivity end]].
 all: apply (update _ _ _ (fun f=>forall j,j<8 -> indexed(f j)=true));[exact V|intros j J].
 - unfold Packed.unpack_source;apply V,unpack_range,J.
 - unfold Packed.shuffle_source;apply V,shuffle_range.
 - destruct (j<?4);reflexivity.
 - reflexivity.
 - destruct (Bool.eqb _ _);[reflexivity|apply V,J].
Qed.

Theorem execute_words ops s : well_formed s -> well_formed (execute ops s).
Proof.
 intro W;assert (K:words (summary ops)).
 { unfold summary;assert (Start:words initial).
   { split;[reflexivity|intros r j J;change ((j<?8)=true);apply Nat.ltb_lt,J]. }
   revert Start;generalize initial;induction ops as [|op tail IH];intros st S;[exact S|apply IH,step_words,S]. }
 destruct K as [G V];split;[intro r;apply indexed_ok;auto|split;[intros j r J;apply indexed_ok;auto|apply W]].
Qed.
