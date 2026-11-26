From Coq Require Import List.

Inductive slot := Root | A | B.
Inductive step := Save (s:slot) | Product (s:slot) | Squares (count:nat).
Record state (T:Type) := State { current:T; slot_root:T; slot_a:T; slot_b:T }.
Arguments State {T}. Arguments current {T}. Arguments slot_root {T}. Arguments slot_a {T}. Arguments slot_b {T}.
Definition get {T} (st:state T) s := match s with Root=>slot_root st | A=>slot_a st | B=>slot_b st end.
Definition advance {T} (mul:T->T->T) (sqr:T->T) st cmd :=
 let root:=slot_root st in let x:=current st in let a:=slot_a st in let b:=slot_b st in
 match cmd with
 | Save A=>State x root x b | Save B=>State x root a x | Save Root=>State x x a b
 | Product s=>State (mul x (get st s)) root a b
 | Squares n=>State (Nat.iter n sqr x) root a b end.
Definition evaluate {T} (mul:T->T->T) (sqr:T->T) root scratch ops :=
 fold_left (advance mul sqr) ops (State root root scratch scratch).

Lemma evaluate_sound {T U} (rel:T->U->Prop) mul1 sq1 mul2 sq2 :
 (forall a b x y, rel x a -> rel y b -> rel (mul1 x y) (mul2 a b)) ->
 (forall a x, rel x a -> rel (sq1 x) (sq2 a)) ->
 forall ops x a scratch unknown, rel x a -> rel scratch unknown ->
 rel (current(evaluate mul1 sq1 x scratch ops)) (current(evaluate mul2 sq2 a unknown ops)).
Proof.
 intros M S ops x a scratch unknown X U0. unfold evaluate.
 set (pair:=fun (f:state T) (e:state U)=>rel(current f)(current e) /\
   rel(slot_root f)(slot_root e) /\ rel(slot_a f)(slot_a e) /\ rel(slot_b f)(slot_b e)).
 enough (H:forall f e, pair f e -> pair (fold_left (advance mul1 sq1) ops f)
    (fold_left (advance mul2 sq2) ops e)) by (apply H; repeat split; assumption).
 induction ops as [|cmd tail IH]; intros f e R; [exact R|]. apply IH.
 destruct f as [v r b c],e as [n t h i]; destruct R as [V [R [B C]]].
 destruct cmd as [s|s|k]; try destruct s; cbn [advance get current slot_root slot_a slot_b] in *;
 unfold pair; cbn; repeat split; auto.
 induction k; cbn; auto.
Qed.
