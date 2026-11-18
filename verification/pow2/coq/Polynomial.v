From Coq Require Import ZArith List Lia Ring.
Require Import FieldSpec.
Import ListNotations.
Open Scope Z_scope.

(* Quotients are atoms in ring identities, with their actual integer meaning.
   Rem is expanded by Euclidean division even when the dividend is symbolic. *)
Inductive expr :=
| C (z:Z) | V (i:nat) | Plus (x y:expr) | Times (x y:expr)
| Quot (x:expr) (d:Z) | Rem (x:expr) (d:Z).
Fixpoint val (env:nat -> Z) (e:expr) : Z :=
  match e with
  | C z => z | V i => env i | Plus x y => val env x + val env y
  | Times x y => val env x * val env y
  | Quot x d => val env x / d | Rem x d => val env x mod d end.
Definition expr_dec (a b:expr) : {a=b}+{a<>b}.
Proof. decide equality; first [apply Z.eq_dec | apply Nat.eq_dec]. Defined.
Definition mono := list expr.
Definition polynomial := list (mono * Z).
Fixpoint monval env (m:mono) := match m with
  | [] => 1 | x::xs => val env x * monval env xs end.
Fixpoint polyval env (p:polynomial) := match p with
  | [] => 0 | (m,c)::ps => c * monval env m + polyval env ps end.
Lemma monapp env a b : monval env (a++b) = monval env a * monval env b.
Proof. induction a; cbn [monval app]; rewrite ?IHa; ring. Qed.
Lemma monrev env a : monval env (rev a) = monval env a.
Proof. induction a; cbn [monval rev]; auto. rewrite monapp,IHa; cbn [monval]; ring. Qed.
Definition meq a b :=
  if list_eq_dec expr_dec a b then true else
  if list_eq_dec expr_dec (rev a) b then true else false.
Lemma meq_ok env a b : meq a b = true -> monval env a = monval env b.
Proof. unfold meq; repeat destruct list_eq_dec; intros; subst; auto using eq_sym,monrev; discriminate. Qed.

Fixpoint insert (m:mono) (c:Z) (p:polynomial) : polynomial :=
  match p with
  | [] => [(m,c)] | (n,d)::xs =>
      if meq m n then (n,c+d)::xs else (n,d)::insert m c xs end.
Lemma insert_ok env m c p : polyval env (insert m c p) = c*monval env m + polyval env p.
Proof. induction p as [|[n d] xs IH]; cbn [polyval insert]; [ring|].
 destruct (meq m n) eqn:E; cbn [polyval]; [rewrite (meq_ok env _ _ E)|rewrite IH]; ring. Qed.
Fixpoint addpoly (p q:polynomial) := match p with
 | [] => q | (m,c)::ps => insert m c (addpoly ps q) end.
Lemma add_ok env p q : polyval env (addpoly p q) = polyval env p + polyval env q.
Proof. induction p as [|[m c] p IH]; cbn [polyval addpoly]; [ring|rewrite insert_ok,IH; ring]. Qed.
Definition scale (m:mono) (c:Z) (q:polynomial) : polynomial :=
  map (fun t => (m++fst t,c * snd t)) q.
Lemma scale_ok env m c q : polyval env (scale m c q) = c*monval env m*polyval env q.
Proof. induction q as [|[n d] q IH]; cbn [polyval scale map fst snd]; [ring|rewrite monapp; unfold scale in IH; rewrite IH; ring]. Qed.
Fixpoint mulpoly (p q:polynomial) := match p with
 | [] => [] | (m,c)::ps => addpoly (scale m c q) (mulpoly ps q) end.
Lemma mul_ok env p q : polyval env (mulpoly p q) = polyval env p * polyval env q.
Proof. induction p as [|[m c] p IH]; cbn [polyval mulpoly]; [ring|rewrite add_ok,scale_ok,IH; ring]. Qed.
Fixpoint norm (e:expr) : polynomial :=
 match e with
 | C c => [([],c)] | Plus a b => addpoly (norm a) (norm b)
 | Times a b => mulpoly (norm a) (norm b)
 | Rem x d => if Z.eqb d 0 then [([e],1)]
              else insert [Quot x d] (-d) (norm x)
 | _ => [([e],1)] end.
Lemma norm_ok env e : polyval env (norm e) = val env e.
Proof. induction e; cbn [norm]; try (cbn [polyval monval val]; ring).
 - rewrite add_ok,IHe1,IHe2; reflexivity.
 - rewrite mul_ok,IHe1,IHe2; reflexivity.
 - destruct (Z.eqb d 0) eqn:E; [cbn [polyval monval val];ring|].
   apply Z.eqb_neq in E. rewrite insert_ok,IHe. cbn [monval val].
   pose proof (Z.div_mod (val env e) d E); lia.
Qed.
Definition zero_test (p:polynomial) := forallb (fun t => Z.eqb (snd t mod prime) 0) p.
Lemma zero_ok env p : zero_test p = true -> represents (polyval env p) 0.
Proof. induction p as [|[m c] p IH]; [intros;apply crefl|].
 cbn [zero_test forallb] in *; rewrite Bool.andb_true_iff; intros [H T].
 apply Z.eqb_eq in H; cbn [snd] in H. specialize (IH T) as [k E].
 exists ((c/prime)*monval env m+k); cbn [polyval].
 pose proof (Z.div_mod c prime ltac:(vm_compute;discriminate)); cbn [snd] in H.
 rewrite E. assert (F : c = (c/prime)*prime) by nia. transitivity (((c/prime)*prime)*monval env m + (0+k*prime)); [rewrite <- F; reflexivity|ring].
Qed.
Definition congruent a b := zero_test (norm (Plus a (Times (C (-1)) b))).
Lemma congruent_ok env a b : congruent a b = true -> represents (val env a) (val env b).
Proof. intro H; apply (zero_ok env) in H. rewrite norm_ok in H.
 destruct H as [k E]; exists k; cbn [val] in E; lia. Qed.
