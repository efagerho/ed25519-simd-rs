From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import Blocks Instructions WordBounds.
Require Import Program Double4ABI FieldSpec Kernels KernelInterface Round RoundArithmetic Double4Spec Preparation.
Import ListNotations. Open Scope Z_scope.
Local Opaque code.
Definition finish j (full:bool) s :=
 let xz:=call j MultiplyPair(scratch,640)s in
 let yt:=call j(if full then MultiplyPair else MultiplySingle)(scratch,960)(shuffle j(stage 5 full)xz) in
 shuffle j(stage 6 full)yt.
Definition round_result (full:bool) before after :=
 lane_words after /\ constants after /\
 forall coord,(coord<(if full then 4 else 3))%nat ->
 reduced(field after point(5*coord)) /\
 represents(limbs(field after point(5*coord)))(coordinate(doubling(lane_coordinates before))coord).
Lemma offset_field s region coord i :
 cells s(offset(region,64*Z.of_nat coord)(64*Z.of_nat i))=field s region coord i.
Proof. unfold offset,field;cbn [fst snd];rewrite Nat2Z.inj_add;f_equal;f_equal;ring. Qed.
Lemma reduced_split x : reduced x -> split_field x.
Proof. intros B i I;specialize(B i I);unfold output_bound in B;destruct(Nat.eqb _ _);unfold split,radix in *;lia. Qed.
Lemma finish_correct j full before s : prepared before s -> round_result full before(finish j full s).
Proof.
 intros[W[C[Fields[Regs Point]]]].
 destruct(Fields 0%nat ltac:(cbn [In];auto))as[E EV].
 destruct(Fields 5%nat ltac:(cbn [In];auto))as[G GV].
 destruct(Fields 10%nat ltac:(cbn [In];auto))as[F FV].
 destruct(Fields 15%nat ltac:(cbn [In];auto))as[H HV].
 assert(RE:split_field(rfield s 0)).
 { apply(field_bound_ext _ (field s scratch 0));[intros;symmetry;apply Regs;assumption|apply ready_split;exact E]. }
 assert(RG:split_field(rfield s 5)).
 { apply(field_bound_ext _ (field s scratch 5));[intros;symmetry;apply Regs;assumption|apply ready_split;exact G]. }
 assert(RF:split_field(fun i=>cells s(offset(scratch,640)(64*Z.of_nat i)))).
 { apply(field_bound_ext _ (field s scratch 10));[intros;symmetry;exact(offset_field s scratch 10 i)|apply ready_split;exact F]. }
 set(xz:=call j MultiplyPair(scratch,640)s).
 destruct(call_multiply j true (scratch,640)s W C RE RG RF 0 ltac:(cbn [In];auto))as[XB XV].
 destruct(call_multiply j true (scratch,640)s W C RE RG RF 5 ltac:(cbn [In];auto))as[ZB ZV].
 change(reduced(rfield xz 0))in XB;change(reduced(rfield xz 5))in ZB.
 assert(LE:limbs(rfield s 0)=limbs(field s scratch 0))by(apply limbs_ext;intros;apply Regs;assumption).
 assert(LG:limbs(rfield s 5)=limbs(field s scratch 5))by(apply limbs_ext;intros;apply Regs;assumption).
 assert(LF:limbs(fun i=>cells s(offset(scratch,640)(64*Z.of_nat i)))=limbs(field s scratch 10))by(apply limbs_ext;intros;apply(offset_field s scratch 10)).
 rewrite LE,LF in XV;rewrite LG,LF in ZV.
 pose proof(ctrans _ _ _ XV (ctimes _ _ _ _ EV FV))as Xmath.
 pose proof(ctrans _ _ _ ZV (ctimes _ _ _ _ GV FV))as Zmath.
 assert(Wxz:lane_words xz)by(apply call_words;exact W).
 assert(Cxz:constants xz)by(apply kernel_constants;exact C).
 set(yt_in:=shuffle j(stage 5 full)xz).
 assert(Wyti:lane_words yt_in)by(apply shuffle_words;exact Wxz).
 assert(Cyti:constants yt_in)by(apply stage_constants;exact Cxz).
 assert(YG:forall i,(i<5)%nat -> rfield yt_in 0 i=field s scratch 5 i).
 { intros i I;unfold yt_in;rewrite stage5_g by exact I. unfold xz;apply call_field. }
 assert(TE:full=true -> forall i,(i<5)%nat -> rfield yt_in 5 i=field s scratch 0 i).
 { intros Full i I;unfold yt_in;rewrite Full,stage5_e by exact I. unfold xz;apply call_field. }
 assert(YH:forall i,(i<5)%nat -> cells yt_in(offset(scratch,960)(64*Z.of_nat i))=field s scratch 15 i).
 { intros i I;rewrite(offset_field yt_in scratch 15). unfold yt_in;rewrite stage5_scratch. unfold xz;apply call_field. }
 assert(YGbound:split_field(rfield yt_in 0))by(apply(field_bound_ext _ (field s scratch 5));[intros;symmetry;apply YG;assumption|apply ready_split;exact G]).
 assert(YEbound:split_field(rfield yt_in 5)).
 { destruct full.
   - apply(field_bound_ext _ (field s scratch 0));[intros;symmetry;apply TE;auto|apply ready_split;exact E].
   - apply(field_bound_ext _ (rfield xz 5));[intros;symmetry;apply stage5_other;assumption|apply reduced_split;exact ZB]. }
 assert(YHbound:split_field(fun i=>cells yt_in(offset(scratch,960)(64*Z.of_nat i))))by
 (apply(field_bound_ext _ (field s scratch 15));[intros;symmetry;apply YH;assumption|apply ready_split;exact H]).
 set(yt:=call j(if full then MultiplyPair else MultiplySingle)(scratch,960)yt_in).
 destruct(call_multiply j full (scratch,960)yt_in Wyti Cyti YGbound YEbound YHbound 0
 ltac:(destruct full;cbn [In];auto))as[YB YV].
 rewrite(limbs_ext _ _ YG),(limbs_ext _ _ YH)in YV.
 pose proof(ctrans _ _ _ YV (ctimes _ _ _ _ GV HV))as Ymath.
 assert(Tresult:full=true -> reduced(rfield yt 5) /\ represents(limbs(rfield yt 5))
 (preparation_value(lane_coordinates before)0*preparation_value(lane_coordinates before)15)).
 { intro Full.
   destruct(call_multiply j full (scratch,960)yt_in Wyti Cyti YGbound YEbound YHbound 5
    ltac:(rewrite Full;cbn [In];auto))as[TB TV].
   split;[exact TB|]. rewrite(limbs_ext _ _ (TE Full)),(limbs_ext _ _ YH)in TV.
   eapply ctrans;[exact TV|apply ctimes;assumption]. }
 assert(Wyt:lane_words yt)by(apply call_words;exact Wyti).
 assert(Cyt:constants yt)by(apply kernel_constants;exact Cyti).
 change(round_result full before(shuffle j(stage 6 full)yt)).
 unfold round_result;split;[apply shuffle_words;exact Wyt|].
 split;[apply stage_constants;exact Cyt|].
 assert(OutX:forall i,(i<5)%nat -> field(shuffle j(stage 6 full)yt)point 0 i=rfield xz 0 i).
 { intros i I;cbn [stage];rewrite stage6_x by exact I. unfold yt;rewrite call_field.
   unfold yt_in;apply stage5_x;exact I. }
 assert(OutZ:forall i,(i<5)%nat -> field(shuffle j(stage 6 full)yt)point 10 i=rfield xz 5 i).
 { intros i I;cbn [stage];rewrite stage6_z by exact I. unfold yt;rewrite call_field.
   unfold yt_in;apply stage5_z;exact I. }
 intros coord K;destruct coord as[|[|[|[|coord]]]];
 try (destruct full;cbn in K;lia).
 all: cbn [Nat.mul Nat.add].
 - split;[apply(field_bound_ext _ (rfield xz 0));[intros;symmetry;apply OutX;assumption|exact XB]|].
   rewrite(limbs_ext _ _ OutX).
   eapply ctrans;[exact Xmath|]. unfold preparation_value,doubling,coordinate;cbn [cx cy cz ct].
   exists 0;ring.
 - split;[apply(field_bound_ext _ (rfield yt 0));[intros;symmetry;apply stage6_y;assumption|exact YB]|].
   cbn [Nat.mul Nat.add stage];rewrite(limbs_ext _ _ (stage6_y j full yt)).
   eapply ctrans;[exact Ymath|]. unfold preparation_value,doubling,coordinate;cbn [cx cy cz ct].
   exists 0;ring.
 - split;[apply(field_bound_ext _ (rfield xz 5));[intros;symmetry;apply OutZ;assumption|exact ZB]|].
   change(represents(limbs(field(shuffle j(stage 6 full)yt)point 10))(coordinate(doubling(lane_coordinates before))2)).
   rewrite(limbs_ext _ _ OutZ).
   eapply ctrans;[exact Zmath|]. unfold preparation_value,doubling,coordinate;cbn [cx cy cz ct].
   exists 0;ring.
 - assert(Full:full=true)by(destruct full;auto;cbn in K;lia).
   destruct(Tresult Full)as[TB TV]. subst full.
   split;[apply(field_bound_ext _ (rfield yt 5));[intros;symmetry;apply stage6_t;assumption|exact TB]|].
   cbn [Nat.mul Nat.add stage];rewrite(limbs_ext _ _ (stage6_t j yt)).
   eapply ctrans;[exact TV|]. unfold preparation_value,doubling,coordinate;cbn [cx cy cz ct].
   exists 0;ring.
Qed.
