From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks execution.WordBounds execution.Lane memory.VectorBuffer.
From Curve25519 Require Import Field Radix51 Edwards.
From Ed25519Simd Require Import Wide51 PointFrame.
From Ed25519Simd.Double4 Require Program Round Double4Spec Logical.
From Ed25519Simd.CachedAdd Require Program Control CachedAddSpec Logical CachedAddABI.
From Ed25519Simd.Point Require Import Double Add DoublePath AddPath Outputs RawBounds Normalize.
Import ListNotations. Local Open Scope Z_scope.

From Ed25519Simd Require Export PointResults.
Definition add_spec m := addition_spec (deferred m) (full m) (affine m).
Definition output p es d := words_at (memory (effects p es d)) point.

Lemma lane_limb p es d j c i : (j<8)%nat ->
  cell (output p es d) (5*c+i)%nat j=field c (lane_effects p j es (view d j)) i.
Proof. intro J;unfold output;rewrite cell_words_at by exact J;apply (proj2 (view_effects p d j (view d j) es ltac:(split;reflexivity))). Qed.
Lemma lane_data d j : data_words d ->(j<8)%nat ->lane_words(view d j).
Proof. intros [R M] J;split;intro k;[apply R|apply M];exact J. Qed.

Section Transfer.
Variables (defer:bool) (p q:Blocks.program) (es fs:list effect).
Hypothesis equal_rows : forall j s n,(n<20)%nat ->
  cells (normalized defer j (lane_effects p j es s)) (point_row n)=cells (lane_effects q j fs s) (point_row n).
Hypothesis folded : forall j s, lane_words s ->defer=true -> raw_bounds (lane_effects p j es s).
Hypothesis words : Forall effect_words es.
Lemma ordinary_limb d j c i : (j<8)%nat ->(c<4)%nat ->(i<5)%nat -> (defer=false \/ (2<=c)%nat) ->
  cell (output p es d) (5*c+i)%nat j=cell(output q fs d) (5*c+i)%nat j.
Proof.
  intros J C I Unchanged;rewrite !lane_limb by exact J;rewrite <- (finish_other defer _ j _ _ C I Unchanged).
  apply equal_rows;lia.
Qed.
Theorem transfer_result d target :
  data_words d ->point_result false (output q fs d) target ->point_result defer (output p es d) target.
Proof.
  intros W Ref j c J C. destruct (Ref j c J C) as [B V].
  pose proof (lane_data d j W J) as Input.
  set (s:=lane_effects p j es (view d j)).
  assert (F:defer=true ->raw_bounds s) by (apply folded,Input).
  split.
  - unfold bounds_for. destruct (defer && Nat.ltb c 2) eqn:H.
    + apply andb_true_iff in H as [D L];apply Nat.ltb_lt in L.
      intros i I;rewrite lane_limb by exact J;apply (F D c L i I).
    + intros i I;rewrite ordinary_limb by
        (auto || (apply andb_false_iff in H;destruct H as [D|L];[now left|right;now apply Nat.ltb_ge])).
      apply B,I.
  - assert (N:limbs (field c (normalized defer j s))=word_coordinate (output q fs d) j c).
    { apply limbs_ext;intros i I;rewrite lane_limb by exact J;apply equal_rows;lia. }
    assert (P:word_coordinate (output p es d) j c=limbs(field c s)) by (apply limbs_ext;intros;apply lane_limb,J).
    rewrite P, <-V, <-N; symmetry;apply represents_mod, finish_value;auto.
    apply lane_effects_words;assumption.
Qed.
End Transfer.

Definition word_event e := match e with Broadcast _ n=>(0<=?n)&&(n<?2^64) | _=>true end.
Lemma events_words es : forallb word_event es=true ->Forall effect_words es.
Proof. intro H;apply Forall_forall;intros e E;apply forallb_forall with(x:=e) in H;auto.
  destruct e;try exact I;apply andb_true_iff in H as[L U];split;[now apply Z.leb_le|now apply Z.ltb_lt]. Qed.
Lemma double_words priv : Forall effect_words (double_effects priv).
Proof. apply events_words;destruct priv;vm_compute;reflexivity. Qed.
Lemma add_words m : Forall effect_words (add_effects m).
Proof. apply events_words;destruct m as [[] []|];vm_compute;reflexivity. Qed.
Lemma double_fold priv j s : lane_words s ->priv=true ->raw_bounds (lane_effects Double.program j (double_effects priv) s).
Proof. intros W -> c C i I;apply folded_rows_sound;auto using double_bounds_checked;lia. Qed.
Lemma add_fold m j s : lane_words s ->deferred m=true ->raw_bounds (lane_effects Add.program j (add_effects m) s).
Proof. intros W D c C i I;destruct m;try discriminate;apply folded_rows_sound;auto using add_bounds_checked;lia. Qed.

Theorem doubling_correct priv d : data_words d ->
  double_spec priv (words_at (memory d) point) (output Double.program (double_effects priv) d).
Proof.
  intros W B. eapply transfer_result; eauto using double_rows,double_fold,double_words.
  exact (Double4.Logical.arithmetic_contract d W B).
Qed.
Theorem addition_correct m d : data_words d ->
  add_spec m (words_at(memory d)point) (words_at(memory d)CachedAddABI.cached)
    (output Add.program (add_effects m) d).
Proof.
  intros W;destruct (CachedAdd.Logical.arithmetic_contract (full m) (affine m) d W) as [Z V];split.
  - intros F i j I J. change (cell (output Add.program (add_effects m) d) (5*3+i)%nat j=0).
    erewrite ordinary_limb; [apply Z;assumption|apply add_rows|exact J|lia|exact I|right;lia].
  - intros B. eapply transfer_result; eauto using add_rows,add_fold,add_words. exact (V B).
Qed.
