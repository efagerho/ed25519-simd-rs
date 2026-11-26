From Coq Require Import List Field.
From Curve25519.group Require Import PrimeField.
Import ListNotations.
Local Open Scope fp_scope.

(* The input is ordered from the last factor back to the first. Each saved
   pair holds a factor and the product of the factors preceding it. *)
Fixpoint prefixes (zs : list fp) : fp * list (fp * fp) :=
 match zs with
 | [] => (1, [])
 | z :: earlier =>
     let '(p, saved) := prefixes earlier in (z*p, (z,p) :: saved)
 end.

Fixpoint backward (acc : fp) (saved : list (fp * fp)) : list fp :=
 match saved with
 | [] => []
 | (z,p) :: earlier => (p*acc) :: backward (z*acc) earlier
 end.

Definition batch_inverse zs :=
 match zs with
 | [] => []
 | _ => let '(p, saved) := prefixes zs in backward (1/p) saved
 end.

Lemma inverse_step z p acc : z <> 0 -> p <> 0 -> acc = 1/(z*p) ->
 p*acc = 1/z /\ z*acc = 1/p.
Proof. intros Z P ->; split; field; auto. Qed.

Theorem batch_inverse_correct zs : Forall (fun z => z <> 0) zs ->
 batch_inverse zs = map (fun z => 1/z) zs.
Proof.
 intro NZ. assert (H : let '(p, saved) := prefixes zs in
   p <> 0 /\ backward (1/p) saved = map (fun z => 1/z) zs).
 { induction NZ as [|z zs Z _ IH]; [split; [discriminate|reflexivity]|].
   cbn [prefixes]. destruct (prefixes zs) as [p saved]. destruct IH as [P IH].
   destruct (inverse_step z p _ Z P eq_refl) as [Out Next].
   split; [now apply mul_nonzero|]. cbn [backward map]. now rewrite Out, Next, IH. }
 destruct zs; [reflexivity|]. unfold batch_inverse.
 destruct (prefixes (_ :: _)); exact (proj2 H).
Qed.
