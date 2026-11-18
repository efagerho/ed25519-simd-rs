From Coq Require Import ZArith List Lia Ring.
Import ListNotations.
Open Scope Z_scope.

Definition radix := 2^51.
Definition split := 2^52.
Definition word := 2^64.
Definition prime := 2^255-19.
Definition exponent := (prime-5)/8.
Definition limbs (get : nat -> Z) :=
  get 0%nat + radix * (get 1%nat + radix * (get 2%nat +
    radix * (get 3%nat + radix * get 4%nat))).
Definition represents (x y : Z) := exists k, x = y + k*prime.

Lemma crefl x : represents x x.
Proof. exists 0; ring. Qed.
Lemma csym x y : represents x y -> represents y x.
Proof. intros [k ->]; exists (-k); ring. Qed.
Lemma ctrans x y z : represents x y -> represents y z -> represents x z.
Proof. intros [j ->] [k ->]; exists (j+k); ring. Qed.
Lemma cplus x y u v : represents x y -> represents u v -> represents (x+u) (y+v).
Proof. intros [j ->] [k ->]; exists (j+k); ring. Qed.
Lemma ctimes x y u v : represents x y -> represents u v -> represents (x*u) (y*v).
Proof. intros [j ->] [k ->]; exists (j*v+k*y+j*k*prime); ring. Qed.
Lemma cut_p x : represents (x mod prime) x.
Proof. exists (-(x/prime)); pose proof (Z.div_mod x prime ltac:(vm_compute; discriminate)); lia. Qed.

(* The public interface uses unsigned, little-endian qwords. A and B
   each hold 40 qwords and the output holds 80, in limb-major order. *)
Definition cell (buf:nat -> Z) (i lane:nat) := buf (i*8+lane)%nat.
Definition field_at buf start lane := limbs (fun i=>cell buf (start+i)%nat lane).
Definition public_bound i := if Nat.eqb i 1 then radix+511 else radix-1.
Definition pow2_spec (a b out:nat -> Z) :=
 (forall i j, (i<5)%nat -> (j<8)%nat ->
  0<=cell a i j<split /\ 0<=cell b i j<split) ->
 forall (second:bool) j, (j<8)%nat ->
 let start:=if second then 5%nat else 0%nat in
 (forall i, (i<5)%nat -> 0<=cell out (start+i)%nat j<=public_bound i) /\
 field_at out start j mod prime =
 ((field_at (if second then b else a) 0%nat j)^exponent) mod prime.
