From Coq Require Import ZArith List Bool Lia Ring.
From ProofArithmetic Require Export Expressions.
Import ListNotations. Open Scope Z_scope.

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
Definition exact_zero (p:polynomial) := forallb(fun t=>Z.eqb(snd t)0)p.
Lemma exact_zero_sound env p : exact_zero p=true ->polyval env p=0.
Proof. induction p as[|[m c]tail IH];cbn [exact_zero forallb polyval];[auto|].
 rewrite andb_true_iff;intros[C T];apply Z.eqb_eq in C;cbn in C;subst c;rewrite(IH T);ring. Qed.
Definition equal_expr a b := exact_zero(norm(Plus a(Times(C(-1))b))).
Lemma equal_expr_sound env a b : equal_expr a b=true ->val env a=val env b.
Proof. intro E;apply(exact_zero_sound env)in E;rewrite norm_ok in E;cbn [val]in E;lia. Qed.

(* Modulus-independent divisibility, specialized to the field by its wrapper. *)
Definition congruence modulus x y := exists k, x=y+k*modulus.
Definition zero_test modulus (p:polynomial) :=
 forallb (fun t=>Z.eqb(snd t mod modulus)0) p.
Lemma zero_ok modulus env p : modulus<>0 -> zero_test modulus p=true ->
 congruence modulus (polyval env p) 0.
Proof.
 intros Nonzero; induction p as [|[m c] p IH]; [intros;exists 0;reflexivity|].
 cbn [zero_test forallb] in *; rewrite Bool.andb_true_iff; intros [H T].
 apply Z.eqb_eq in H; cbn [snd] in H. specialize (IH T) as [k E].
 exists ((c/modulus)*monval env m+k); cbn [polyval].
 pose proof (Z.div_mod c modulus Nonzero); cbn [snd] in H.
 rewrite E. assert (F:c=(c/modulus)*modulus) by lia.
 transitivity (((c/modulus)*modulus)*monval env m+(0+k*modulus));
 [rewrite <-F;reflexivity|ring].
Qed.
Definition congruent modulus a b := zero_test modulus (norm (Plus a (Times (C (-1)) b))).
Lemma congruent_ok modulus env a b : modulus<>0 -> congruent modulus a b=true ->
 congruence modulus (val env a) (val env b).
Proof.
 intros Nonzero H; apply (zero_ok modulus env _ Nonzero) in H; rewrite norm_ok in H.
 destruct H as [k E];exists k;cbn [val] in E;lia.
Qed.
