From Coq Require Import List ZArith Lia Ring.
Import ListNotations. Open Scope Z_scope.

Definition prime := 2^255-19.
Definition sqrt_ratio_exponent := (prime-5)/8.
Definition sqrt_m1 : Z :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752.
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

Lemma represents_mod x y : represents x y -> x mod prime=y mod prime.
Proof. intros[k E];rewrite E,Z.add_mod,Z.mul_mod;[|unfold prime;lia|unfold prime;lia].
 rewrite Z.mod_same,Z.mul_0_r,Z.mod_0_l,Z.add_0_r,Z.mod_mod by (unfold prime;lia);reflexivity.
Qed.
Lemma cminus x y u v : represents x y -> represents u v -> represents (x-u)(y-v).
Proof. intros[a A][b B];exists(a-b);rewrite A,B;ring. Qed.
Lemma cneg x y : represents x y -> represents(-x)(-y).
Proof. intros[k E];exists(-k);rewrite E;ring. Qed.
