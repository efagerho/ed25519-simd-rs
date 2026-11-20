From Coq Require Import List ZArith Bool.
From Machine Require Import isa.Instructions execution.Blocks.
Import ListNotations.
Open Scope Z_scope.

(* Execute one SIMD instruction, resolving its load against the current GPRs
   and reading its operands from the current data state. *)
Definition readable l c (bd : nat * Z) :=
 match pointer_at c (fst bd) (snd bd) with
 | Some a => vector_ok l a false | None => false end.
Definition direct_load c s j b disp :=
 match pointer_at c b disp with Some a => memory s a j | None => 0 end.
Definition vector_step l c (i : instruction) s :=
 let '(dst,op) := i in
 if forallb (readable l c) (load_operands [i]) then
   Some (register_write s dst (fun j => bits (direct_load c s j) (zmm s j) dst op))
 else None.

Definition bind {A B} (r : option A) (f : A -> option B) :=
 match r with Some x => f x | None => None end.
Fixpoint sequence {I A} (f : I -> A -> option A) (xs : list I) (s : A) :=
 match xs with [] => Some s | x::tail => bind (f x s) (sequence f tail) end.

Lemma sequence_app {I A} (f : I -> A -> option A) xs ys s :
 sequence f (xs ++ ys) s = bind (sequence f xs s) (sequence f ys).
Proof.
 revert s; induction xs as [|x xs IH]; intro s; cbn; auto.
 destruct (f x s); cbn; auto.
Qed.

(* This is the batched update performed by the Evaluate effect. *)
Definition evaluate bases code s :=
 Data (fun j => run (effective_load s bases j) code (zmm s j)) (memory s).

Lemma capture_lookup c regs b :
 find (fun entry => Nat.eqb (fst entry) b) (capture c regs) =
 if in_dec Nat.eq_dec b regs then option_map (fun a => (b,a)) (pointer_at c b 0) else None.
Proof.
 induction regs as [|r rs IH]; [reflexivity|].
 cbn [capture flat_map]. destruct (Nat.eq_dec r b) as [->|D].
 - destruct (in_dec Nat.eq_dec b (b::rs)) as [_|N]; [|exfalso; apply N; now left].
   destruct (pointer_at c b 0) eqn:P; cbn; [now rewrite Nat.eqb_refl|].
   fold (capture c rs). rewrite IH. now destruct (in_dec Nat.eq_dec b rs).
 - destruct (pointer_at c r 0); cbn [app find fst].
   + rewrite (proj2 (Nat.eqb_neq r b) D).
     fold (capture c rs). rewrite IH. destruct (in_dec Nat.eq_dec b rs), (in_dec Nat.eq_dec b (r::rs)); simpl in *; intuition.
   + fold (capture c rs). rewrite IH. destruct (in_dec Nat.eq_dec b rs), (in_dec Nat.eq_dec b (r::rs)); simpl in *; intuition.
Qed.

Definition covers c bases loads :=
 forall b d, In (b,d) loads -> forall s,
 (fun j => effective_load s bases j b d) = (fun j => direct_load c s j b d).

Lemma capture_covers c loads :
 covers c (capture c (nodup Nat.eq_dec (map fst loads))) loads.
Proof.
 intros b d H s. unfold effective_load, direct_load. rewrite capture_lookup.
 destruct (in_dec Nat.eq_dec b (nodup Nat.eq_dec (map fst loads))) as [_|N].
 - unfold pointer_at. destruct (Blocks.gpr c b) as [|[r off]|]; cbn; auto.
   unfold offset; cbn. now rewrite Z.add_0_r.
 - exfalso. apply N, nodup_In. exact (in_map (@fst nat Z) _ _ H).
Qed.

Lemma vector_sequence l c code bases s :
 covers c bases (load_operands code) ->
 sequence (vector_step l c) code s =
 if forallb (readable l c) (load_operands code)
 then Some (evaluate bases code s) else None.
Proof.
 revert s; induction code as [|[dst op] rest IH]; intros s C.
 - destruct s; reflexivity.
 - change (load_operands ((dst,op)::rest)) with
     (match op with Load b d | MaddMem _ _ b d => [(b,d)] | _ => [] end ++ load_operands rest) in *.
   set (head := match op with Load b d | MaddMem _ _ b d => [(b,d)] | _ => [] end) in *.
   assert (T : covers c bases (load_operands rest)).
   { intros b d H. apply C, in_or_app. now right. }
   assert (V : (fun j => bits (direct_load c s j) (zmm s j) dst op) =
               (fun j => bits (effective_load s bases j) (zmm s j) dst op)).
   { destruct op; try reflexivity.
     - symmetry. apply C. now left.
     - unfold bits. symmetry. exact (f_equal
       (fun f => fun j => IFMA.madd52 high (zmm s j dst) (zmm s j a) (f j))
       (C base disp ltac:(now left) s)). }
   cbn [sequence vector_step].
   change (load_operands [(dst,op)]) with (head ++ []).
   rewrite app_nil_r, forallb_app.
   destruct (forallb (readable l c) head); cbn [andb bind]; auto.
   rewrite V, IH by exact T. destruct (forallb (readable l c) (load_operands rest)); reflexivity.
Qed.
