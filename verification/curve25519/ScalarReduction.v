From Coq Require Import ZArith Lia.
From ProofArithmetic Require Montgomery.
From Curve25519 Require Export Scalar.
Local Open Scope Z_scope.

Definition B : Z := 2^52.
Definition W : Z := 2^64.
Definition R : Z := B^5.
Lemma B_positive : 0<B. Proof. unfold B;lia. Qed.
Lemma W_positive : 0<W. Proof. unfold W;lia. Qed.

Definition l0 : Z := 0x2631a5cf5d3ed.
Definition l1 : Z := 0xdea2f79cd6581.
Definition l2 : Z := 0x14def9.
Definition l4 : Z := 0x100000000000.
Definition factor : Z := 0x51da312547e1b.
Definition quotient := Montgomery.cancellation_digit B factor.
Lemma modulus_limbs : L=l0+B*(l1+B*(l2+B*(0+B*l4))).
Proof. vm_compute;reflexivity. Qed.
Lemma inverse_checked : (factor*l0+1)mod B=0.
Proof. vm_compute;reflexivity. Qed.
Lemma quotient_bound x : 0<=quotient x<B.
Proof. apply Z.mod_pos_bound,B_positive. Qed.
Lemma low_cancel x : (x+quotient x*l0) mod B=0.
Proof. apply Montgomery.low_cancel; auto using B_positive,inverse_checked. Qed.
Lemma low_carry x : 0<=x -> B*((x+B-1)/B)=x+(quotient x*l0)mod B.
Proof. intros _. apply Montgomery.cancelled_carry; auto using B_positive,low_cancel. Qed.

(* Cancellation of Montgomery scaling is proved with an explicit Bezout
   witness, checked as an integer identity by Coq. *)
Definition inverseR : Z := 5706410653605570882457795059301885719620630590890452783038400561109479083972.
Definition bezoutR : Z := 1460841127323026145909195535181282744217281446807063794674545094323019697126939.
Lemma inverse_R : R*inverseR=1+L*bezoutR.
Proof. vm_compute;reflexivity. Qed.
Lemma montgomery_residue a b u q :
 R*u=a*(R mod L)+b*((2^256*R)mod L)+q*L ->
 u mod L=(a+2^256*b)mod L.
Proof. apply (Montgomery.reduce_pair L R inverseR bezoutR); auto using L_positive,inverse_R. Qed.
Lemma montgomery_range a b u q :
 0<=a<2^256 ->0<=b<2^256 ->0<=q<R ->
 R*u=a*(R mod L)+b*((2^256*R)mod L)+q*L ->0<=u<2*L.
Proof.
 intros A D Q E.
 pose proof(canonical_residue R).
 pose proof(canonical_residue (2^256*R));unfold canonical_scalar in *.
 unfold R,B,L in *;nia.
Qed.
