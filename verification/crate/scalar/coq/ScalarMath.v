From Coq Require Import List ZArith Lia Ring.
Require Import ScalarSpec.
Import ListNotations. Open Scope Z_scope.
Definition l0 : Z := 0x2631a5cf5d3ed.
Definition l1 : Z := 0xdea2f79cd6581.
Definition l2 : Z := 0x14def9.
Definition l4 : Z := 0x100000000000.
Definition factor : Z := 0x51da312547e1b.
Definition quotient x := ((x mod B)*factor) mod B.
Lemma modulus_limbs : L=l0+B*(l1+B*(l2+B*(0+B*l4))).
Proof. vm_compute;reflexivity. Qed.
Lemma inverse_checked : (factor*l0+1)mod B=0.
Proof. vm_compute;reflexivity. Qed.
Lemma quotient_bound x : 0<=quotient x<B.
Proof. apply Z.mod_pos_bound,B_positive. Qed.
Lemma low_cancel x : (x+quotient x*l0)mod B=0.
Proof.
 assert(N:B<>0)by(pose proof B_positive;lia).
 apply (proj2(Z.mod_divide _ _ N)).
 let k:=eval vm_compute in ((factor*l0+1)/B) in
 exists (x*k-(x/B)*factor*l0-((x mod B*factor)/B)*l0).
 pose proof(Z.div_mod x B N).
 pose proof(Z.div_mod (x mod B*factor) B N).
 unfold quotient,B,factor,l0 in *;nia.
Qed.
(* The optimized carry is exact even when x is already a multiple of B. *)
Lemma low_carry x : 0<=x -> B*((x+B-1)/B)=x+(quotient x*l0)mod B.
Proof.
 intro X;pose proof B_positive as Pos;pose proof(low_cancel x)as Cancel.
 pose proof(Z.div_mod x B ltac:(lia)).
 pose proof(Z.div_mod (quotient x*l0) B ltac:(lia)).
 pose proof(Z.div_mod (x+quotient x*l0) B ltac:(lia)).
 pose proof(Z.div_mod (x+B-1) B ltac:(lia)).
 pose proof(Z.mod_pos_bound x B Pos).
 pose proof(Z.mod_pos_bound (quotient x*l0) B Pos).
 pose proof(Z.mod_pos_bound (x+B-1) B Pos).
 unfold B in *;destruct(Z.eq_dec(x mod 4503599627370496)0);lia.
Qed.
Lemma canonical x : 0<=x<2*L ->
 (if x<?L then x else x-L)=x mod L.
Proof.
 intros Bounds;pose proof L_positive;destruct(x<?L)eqn:E.
 - apply Z.ltb_lt in E;rewrite Z.mod_small by lia;reflexivity.
 - apply Z.ltb_ge in E;apply Z.mod_unique with(q:=1);[left;lia|ring].
Qed.

Lemma mod_word_B x : (x mod W)mod B=x mod B.
Proof.
 symmetry;apply Znumtheory.Zmod_div_mod;[apply B_positive|apply W_positive|].
 exists 4096;vm_compute;reflexivity.
Qed.
Definition join x y scale cutoff := ((x/cutoff+(y*scale mod W))mod W)mod B.
Lemma join_exact x y scale high cutoff :
 0<=x<W ->0<scale ->0<high ->0<cutoff ->scale*high=B ->cutoff*scale=W ->
 join x y scale cutoff=x/cutoff+(y mod high)*scale.
Proof.
 intros X S H C B0 W0;unfold join;rewrite mod_word_B.
 rewrite Z.add_mod by(pose proof B_positive;lia).
 rewrite mod_word_B;rewrite <-Z.add_mod by(pose proof B_positive;lia).
 assert(Q:0<=x/cutoff<scale).
 { split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia. }
 pose proof(Z.mod_pos_bound y high H).
 pose proof(Z.div_mod y high ltac:(lia)).
 symmetry;apply Z.mod_unique with(q:=y/high);[left;nia|nia].
Qed.
Definition chunks x0 x1 x2 x3 :=
 [x0 mod B;join x0 x1 (2^12)(2^52);join x1 x2(2^24)(2^40);
  join x2 x3(2^36)(2^28);x3/2^16].
Lemma chunks_correct x0 x1 x2 x3 :
 0<=x0<W ->0<=x1<W ->0<=x2<W ->0<=x3<W ->
 number B(chunks x0 x1 x2 x3)=number W[x0;x1;x2;x3].
Proof.
 intros A D E F;unfold chunks.
 rewrite(join_exact x0 x1 (2^12)(2^40)(2^52))by(unfold B,W in *;lia).
 rewrite(join_exact x1 x2 (2^24)(2^28)(2^40))by(unfold B,W in *;lia).
 rewrite(join_exact x2 x3 (2^36)(2^16)(2^28))by(unfold B,W in *;lia).
 pose proof(Z.div_mod x0 B ltac:(pose proof B_positive;lia)).
 pose proof(Z.div_mod x1 (2^40)ltac:(lia)).
 pose proof(Z.div_mod x2 (2^28)ltac:(lia)).
 pose proof(Z.div_mod x3 (2^16)ltac:(lia)).
 cbn [number];unfold B,W in *;lia.
Qed.

(* Cancellation of Montgomery scaling is proved with an explicit Bezout
   witness, checked as an integer identity by Coq. *)
Definition inverseR : Z := 5706410653605570882457795059301885719620630590890452783038400561109479083972.
Definition bezoutR : Z := 1460841127323026145909195535181282744217281446807063794674545094323019697126939.
Lemma inverse_R : R*inverseR=1+L*bezoutR.
Proof. vm_compute;reflexivity. Qed.
Lemma montgomery_residue a b u q :
 R*u=a*(R mod L)+b*((2^256*R)mod L)+q*L ->
 u mod L=(a+2^256*b)mod L.
Proof.
 intro Eq;pose proof inverse_R as Inv;pose proof L_positive as Pos.
 pose proof(Z.div_mod R L ltac:(lia)).
 pose proof(Z.div_mod (2^256*R) L ltac:(lia)).
 assert(D0:R mod L=R-L*(R/L))by lia.
 assert(D1:(2^256*R)mod L=2^256*R-L*((2^256*R)/L))by lia.
 rewrite D0,D1 in Eq.
 set(h:=a+2^256*b).
 assert(E:R*(u-h)=L*(q-a*(R/L)-b*((2^256*R)/L)))by(unfold h;nia).
 pose proof(f_equal(fun z=>z*inverseR)E)as G.
 change(R*(u-h)*inverseR=L*(q-a*(R/L)-b*((2^256*R)/L))*inverseR)in G.
 replace(R*(u-h)*inverseR)with((u-h)*(R*inverseR))in G by ring.
 rewrite Inv in G.
 assert(F:u=h+(q*inverseR-a*(R/L)*inverseR-b*((2^256*R)/L)*inverseR-(u-h)*bezoutR)*L)by nia.
 rewrite F;apply Z.mod_add;lia.
Qed.
Lemma montgomery_range a b u q :
 0<=a<2^256 ->0<=b<2^256 ->0<=q<R ->
 R*u=a*(R mod L)+b*((2^256*R)mod L)+q*L ->0<=u<2*L.
Proof.
 intros A D Q E.
 pose proof(Z.mod_pos_bound R L L_positive).
 pose proof(Z.mod_pos_bound (2^256*R) L L_positive).
 unfold R,B,L in *;nia.
Qed.
