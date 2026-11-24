From Coq Require Import List ZArith Bool Lia.
From Machine Require Import memory.FlatMemory memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* Consecutive SIMD rows or active qwords within them. The producer supplies
   the value of each published byte. Extent and enablement are independent
   of both the old memory and the value being published. *)
Definition tiles (position:nat->Z) base width count enabled (value:bytes) :=
 map (fun i=>let a:=base+Z.of_nat width*Z.of_nat i in
             Store (position i) a width (fun k=>value (a+k)))
   (filter enabled (seq 0 count)).
Definition covered base width count enabled x :=
 base<=x<base+Z.of_nat width*Z.of_nat count /\ enabled (Z.to_nat((x-base)/Z.of_nat width))=true.

Lemma tile_footprint position base width count on value x : (0<width)%nat ->
 (exists w, In w (tiles position base width count on value) /\ touches w x) <->
 covered base width count on x.
Proof.
 intro W;unfold tiles,covered;split.
 - intros [w [I T]]. apply in_map_iff in I as [i [<- I]]. apply filter_In in I as [I On].
   apply in_seq in I;unfold touches in T;cbn [address size] in T.
   assert (Q:(x-base)/Z.of_nat width=Z.of_nat i).
   { symmetry;apply Z.div_unique_pos with (r:=x-(base+Z.of_nat width*Z.of_nat i));nia. }
   rewrite Q,Nat2Z.id;split;[nia|exact On].
 - intros [B On]. set (i:=Z.to_nat((x-base)/Z.of_nat width)) in *.
   assert (Q:Z.of_nat i=(x-base)/Z.of_nat width) by (unfold i;apply Z2Nat.id,Z.div_pos;lia).
   assert (I:(i<count)%nat).
   { apply Nat2Z.inj_lt;rewrite Q;apply Z.div_lt_upper_bound;nia. }
   eexists;split;[apply in_map_iff;exists i;split;[reflexivity|apply filter_In;split;[apply in_seq;lia|exact On]]|].
   unfold touches;cbn [address size]. rewrite Q.
   pose proof (Z.div_mod (x-base) (Z.of_nat width) ltac:(lia)).
   pose proof (Z.mod_pos_bound (x-base) (Z.of_nat width) ltac:(lia));nia.
Qed.

Lemma replay_value x v ws :
 (forall e, In e ws -> touches e x -> payload e (x-address e)=v) ->
 forall before, ((forall e, In e ws -> ~touches e x) -> before x=v) ->
 replay before ws x=v.
Proof.
 induction ws as [|e t IH];intros D m Other;[apply Other;intros ? []|].
 apply IH;[intros f I;apply D,in_cons,I|]. intro Tail.
 unfold commit,write_bytes;destruct ((address e<=?x)&&(x<?address e+Z.of_nat(size e))) eqn:Hit.
 - apply andb_true_iff in Hit as [L U];apply Z.leb_le in L;apply Z.ltb_lt in U.
   apply D;[left;reflexivity|split;assumption].
 - apply Other;intros f [<-|I];[|apply Tail,I].
   unfold touches;apply andb_false_iff in Hit as [No|No];[apply Z.leb_gt in No|apply Z.ltb_ge in No];lia.
Qed.
Lemma tiles_replay pos a w n on value before x : (0<w)%nat ->
 (~covered a w n on x -> value x=before x) ->
 replay before (tiles pos a w n on value) x=value x.
Proof.
 intros Size Other;apply replay_value.
 - intros e I T;apply in_map_iff in I as [i [<- _]];cbn [payload address];f_equal;ring.
 - intro Miss;symmetry;apply Other;intro H.
   apply (proj2 (tile_footprint pos a w n on value x Size)) in H as [f [I T]];exact (Miss f I T).
Qed.

Lemma tiles_confined pos a w n on v (region:Z->Prop) : (0<w)%nat ->
 (forall x,a<=x<a+Z.of_nat w*Z.of_nat n -> region x) ->
 confined region (tiles pos a w n on v).
Proof.
 intros W A;apply Forall_forall;intros e I x T;apply A.
 exact (proj1 (proj1 (tile_footprint pos a w n on v x W) (ex_intro _ e (conj I T)))).
Qed.
