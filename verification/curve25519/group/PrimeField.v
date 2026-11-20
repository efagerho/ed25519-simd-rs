From Coq Require Import ZArith Znumtheory List Field Lia.
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat Euler Zp.
From Coqprime.Z Require Import ZCAux.
From Coqprime.elliptic Require GZnZ.
From Curve25519 Require Field.
Import ListNotations.
Local Notation p := Field.prime.

(* Pocklington witnesses for 2^255-19 (Fiat Cryptography, Spec/Curve25519.v).
   The certificate is checked with Coqprime and ordinary kernel conversion. *)
Lemma modulus_prime : prime p.
Proof.
 refine (Pocklington_refl (Pock_certif _ 2
   [(74058212732561358302231226437062788676166966415465897661863160754340907,1); (2,2)] 1)
   [Pock_certif 74058212732561358302231226437062788676166966415465897661863160754340907 2
     [(31757755568855353,1); (57467,1); (353,1); (2,1)] 2028478494862525422475606;
    Pock_certif 31757755568855353 10 [(223,1); (107,1); (3,1); (2,3)] 539560;
    Pock_certif 57467 2 [(59,1); (2,1)] 14;
    Pock_certif 353 3 [(2,5)] 1; Pock_certif 223 3 [(3,1); (2,1)] 1;
    Pock_certif 107 2 [(53,1); (2,1)] 1; Pock_certif 59 2 [(29,1); (2,1)] 1;
    Pock_certif 53 2 [(2,2)] 4; Pock_certif 29 2 [(2,2)] 1;
    Proof_certif 3 prime_3; Proof_certif 2 prime_2] _)%positive.
 vm_compute. reflexivity.
Qed.

Notation fp := (GZnZ.znz Field.prime).
Definition residue (z:Z) : fp := GZnZ.mkznz p _ (GZnZ.modz p z).
Declare Scope fp_scope.
Delimit Scope fp_scope with fp.
Notation "0" := (GZnZ.zero p) : fp_scope.
Notation "1" := (GZnZ.one p) : fp_scope.
Infix "+" := (GZnZ.add p) : fp_scope.
Infix "*" := (GZnZ.mul p) : fp_scope.
Infix "-" := (GZnZ.sub p) : fp_scope.
Notation "- x" := (GZnZ.opp p x) : fp_scope.
Infix "/" := (GZnZ.div p) : fp_scope.
Local Open Scope fp_scope.
Add Field fp_field : (GZnZ.FZpZ p modulus_prime).

Lemma residue_eq x y : eqm p x y -> residue x = residue y.
Proof. apply GZnZ.zirr. Qed.
Lemma residue_add x y : residue (x+y)%Z = residue x + residue y.
Proof. apply GZnZ.zirr, Zplus_mod. Qed.
Lemma residue_sub x y : residue (x-y)%Z = residue x - residue y.
Proof. apply GZnZ.zirr, Zminus_mod. Qed.
Lemma residue_mul x y : residue (x*y)%Z = residue x * residue y.
Proof. apply GZnZ.zirr, Zmult_mod. Qed.
Lemma residue_opp x : residue (-x)%Z = - residue x.
Proof.
 replace (-x)%Z with (0-x)%Z by ring. rewrite residue_sub.
 change (0-residue x = -residue x). ring.
Qed.
Lemma residue_two : residue 2 = 1+1. Proof. apply GZnZ.zirr; reflexivity. Qed.
Lemma fp_eq_dec (x y:fp) : {x=y}+{x<>y}.
Proof.
 destruct (Z.eq_dec (GZnZ.val _ x) (GZnZ.val _ y)).
 - left; destruct x,y; now apply GZnZ.zirr.
 - right; congruence.
Qed.
Lemma mul_nonzero (x y:fp) : x<>0 -> y<>0 -> x*y<>0.
Proof.
 intros X Y H. apply Y. transitivity ((x*y)/x); [field; exact X|].
 rewrite H. field; exact X.
Qed.

Definition d := (- residue 121665) / residue 121666.
Local Opaque phi.
Lemma nonsquare_by_euler (c:fp) : GZnZ.val p c <> 0%Z ->
 Zpow_mod (GZnZ.val p c) ((p-1)/2) p <> 1%Z -> forall x:fp, x*x <> c.
Proof.
 intros Nonzero Euler x Square.
 set (v := GZnZ.val p x).
 assert (Range : (0 <= v < p)%Z).
 { pose proof (Z.mod_pos_bound v p ltac:(unfold Field.prime;lia)) as H.
   unfold v in *. now rewrite <- (GZnZ.inZnZ _ x) in H. }
 assert (S : ((v*v) mod p)%Z = GZnZ.val p c) by exact (f_equal (GZnZ.val p) Square).
 assert (Positive : (0 < v)%Z).
 { destruct (Z.eq_dec v 0) as [Zero|]; [exfalso; apply Nonzero; rewrite <- S,Zero; reflexivity|lia]. }
 pose proof (phi_power_is_1 v p ltac:(unfold Field.prime;lia)
   (rel_prime_le_prime v p modulus_prime ltac:(lia))) as Fermat.
 rewrite (prime_phi_n_minus_1 p modulus_prime) in Fermat.
 set (half := ((p-1)/2)%Z).
 assert (Half : (0<=half)%Z) by (vm_compute; discriminate).
 replace (p-1)%Z with (2*half)%Z in Fermat by reflexivity.
 rewrite (Z.pow_mul_r v 2 half) in Fermat by lia.
 replace (v^2)%Z with (v*v)%Z in Fermat by ring.
 rewrite Zpower_mod in Fermat by (unfold Field.prime;lia).
 rewrite S, <- Zpow_mod_Zpower_correct in Fermat by (unfold Field.prime;lia).
 exact (Euler Fermat).
Qed.
Lemma d_nonsquare (x:fp) : x*x <> d.
Proof. apply nonsquare_by_euler; vm_compute; discriminate. Qed.
