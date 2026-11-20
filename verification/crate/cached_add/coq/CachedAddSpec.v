From Coq Require Import List ZArith Bool Lia Ring.
Require Import FieldSpec.
Import ListNotations. Open Scope Z_scope.
(* An independent arithmetic contract: no curve membership or cache consistency assumptions. *)
Definition addition (full affine:bool)(point cached:nat->Z)c :=
 let a:=(point 1%nat-point 0%nat)*cached 0%nat in
 let b:=(point 1%nat+point 0%nat)*cached 1%nat in
 let cc:=point 3%nat*cached 2%nat in
 let d:=if affine then 2*point 2%nat else point 2%nat*cached 3%nat in
 let e:=b-a in let f:=d-cc in let g:=d+cc in let h:=b+a in
 match c with 0%nat=>e*f | 1%nat=>g*h | 2%nat=>f*g | _=>if full then e*h else 0 end.
Definition coordinate words j c := field_at words (5*c)%nat j.
Definition output_bound i := if Nat.eqb i 1 then 2^52-1 else 2^51-1.
Definition input_bounds (affine:bool) before cached :=
 (forall i j,(i<20)%nat ->(j<8)%nat ->0<=cell before i j<split) /\
 (forall i j,(i<(if affine then 15 else 20))%nat ->(j<8)%nat ->0<=cell cached i j<split).
Definition cached_add_spec full affine before cached after :=
 (* Omitting T writes literal zero, not only a representative congruent to zero. *)
 (full=false ->forall i j,(i<5)%nat ->(j<8)%nat ->cell after(15+i)%nat j=0) /\
 (input_bounds affine before cached ->forall j c,(j<8)%nat ->(c<4)%nat ->
 (forall i,(i<5)%nat ->0<=cell after(5*c+i)%nat j<=output_bound i) /\
 coordinate after j c mod prime=addition full affine(coordinate before j)(coordinate cached j)c mod prime).
Lemma represents_mod x y : represents x y ->x mod prime=y mod prime.
Proof. intros[k E];rewrite E,Z.add_mod,Z.mul_mod;[|unfold prime;lia|unfold prime;lia].
 rewrite Z.mod_same,Z.mul_0_r,Z.mod_0_l,Z.add_0_r,Z.mod_mod by(unfold prime;lia);reflexivity. Qed.
Lemma cminus x y u v : represents x y ->represents u v ->represents(x-u)(y-v).
Proof. intros[a A][b B];exists(a-b);rewrite A,B;ring. Qed.
Lemma coordinate_ext a b j c : (forall k,(k<160)%nat ->a k=b k) ->(c<4)%nat ->(j<8)%nat ->
 coordinate a j c=coordinate b j c.
Proof. intros E C J;unfold coordinate,field_at,limbs,cell;repeat rewrite E by lia;reflexivity. Qed.
Lemma cached_coordinate_ext (affine:bool) a b j c :
 (forall k,(k<(if affine then 120 else 160))%nat ->a k=b k) ->
 (c<(if affine then 3 else 4))%nat ->(j<8)%nat ->coordinate a j c=coordinate b j c.
Proof. intros E C J;unfold coordinate,field_at,limbs,cell;destruct affine;repeat rewrite E by lia;reflexivity. Qed.
Lemma addition_ext full (affine:bool) p q p' q' c :
 (forall c,(c<4)%nat ->p c=p' c) ->
 (forall c,(c<(if affine then 3 else 4))%nat ->q c=q' c) ->
 addition full affine p q c=addition full affine p' q' c.
Proof. intros P Q;unfold addition;destruct affine;repeat rewrite P by lia;repeat rewrite Q by lia;reflexivity. Qed.
Lemma spec_ext full (affine:bool) before cached after before' cached' after' :
 (forall k,(k<160)%nat ->before' k=before k) ->
 (forall k,(k<(if affine then 120 else 160))%nat ->cached' k=cached k) ->
 (forall k,(k<160)%nat ->after' k=after k) ->
 cached_add_spec full affine before cached after ->cached_add_spec full affine before' cached' after'.
Proof.
 intros In Cache Out[Zero Spec];split.
 - intros F i j I J;unfold cell;rewrite Out by lia;apply Zero;assumption.
 - intros[A B]j c J C.
   assert(Input:input_bounds affine before cached).
   { split;intros i lane I L;unfold cell in *.
     - rewrite <-In by lia;apply A;assumption.
     - rewrite <-Cache by (destruct affine;lia);apply B;assumption. }
   destruct(Spec Input j c J C)as[Bound Value];split.
   + intros i I;unfold cell;rewrite Out by lia;apply Bound;exact I.
   + rewrite(coordinate_ext _ _ _ _ Out C J).
     rewrite(addition_ext full affine (coordinate before' j)(coordinate cached' j)
       (coordinate before j)(coordinate cached j));[exact Value| |].
     * intros;apply coordinate_ext;assumption.
     * intros;apply(cached_coordinate_ext affine);assumption.
Qed.
