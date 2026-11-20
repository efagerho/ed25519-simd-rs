From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import execution.Blocks isa.Instructions execution.WordBounds.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Double4 Require Import Program Double4ABI Kernels KernelInterface Round RoundArithmetic Double4Spec.
Import ListNotations. Open Scope Z_scope.
Local Opaque code.
Definition prepare j s :=
 let xy:=shuffle j(stage 0 false)s in
 let plus:=call j AddReduce (scratch,0)xy in
 let ab:=call j SquarePair (scratch,0)(shuffle j(stage 1 false)plus) in
 let cd:=call j SquarePair (scratch,0)(shuffle j(stage 2 false)ab) in
 let sub:=call j SubtractReduce (scratch,0)(shuffle j(stage 3 false)cd) in
 shuffle j(stage 4 false)sub.
Definition lane_coordinates s := Coordinates (limbs(field s point 0)) (limbs(field s point 5))
 (limbs(field s point 10)) (limbs(field s point 15)).
Definition preparation_value q coord :=
 let a:=cx q*cx q in let b:=cy q*cy q in let c:=cz q*cz q in
 let d:=(cx q+cy q)*(cx q+cy q) in
 match coord with 0%nat=>d-(a+b) | 5%nat=>b-a | 10%nat=>(b-a)-2*c | _=> -(a+b) end.
Definition prepared s out :=
 lane_words out /\ constants out /\
 (forall coord,In coord [0%nat;5%nat;10%nat;15%nat] ->
 ready(field out scratch coord) /\ represents(limbs(field out scratch coord))(preparation_value(lane_coordinates s)coord)) /\
 (forall i,(i<5)%nat -> rfield out 0 i=field out scratch 0 i /\ rfield out 5 i=field out scratch 5 i) /\
 (forall coord i, field out point coord i=field s point coord i).
Lemma prepare_correct j s : lane_words s -> constants s ->
 loose(field s point 0) -> loose(field s point 5) -> loose(field s point 10) ->
 prepared s (prepare j s).
Proof.
 intros W C X Y Zb.
 set(xy:=shuffle j(stage 0 false)s).
 assert(Wxy:lane_words xy) by(apply shuffle_words;exact W).
 assert(Cxy:constants xy) by(apply stage_constants;exact C).
 assert(Xxy:loose(rfield xy 0)) by(eapply loose_ext;[intros;symmetry;apply stage0_x;assumption|exact X]).
 assert(Yxy:loose(rfield xy 5)) by(eapply loose_ext;[intros;symmetry;apply stage0_y;assumption|exact Y]).
 assert(XY0:limbs(rfield xy 0)=limbs(field s point 0))by(apply limbs_ext,stage0_x).
 assert(XY5:limbs(rfield xy 5)=limbs(field s point 5))by(apply limbs_ext,stage0_y).
 set(plus:=call j AddReduce (scratch,0)xy).
 destruct(call_add j xy Wxy Cxy Xxy Yxy)as[Sum SumV].
 change(ready(rfield plus 10))in Sum.
 change(represents(limbs(rfield plus 10))(limbs(rfield xy 0)+limbs(rfield xy 5)))in SumV.
 assert(Wplus:lane_words plus)by(apply call_words;exact Wxy).
 assert(Cplus:constants plus)by(apply kernel_constants;exact Cxy).
 set(ab_in:=shuffle j(stage 1 false)plus).
 assert(Wabi:lane_words ab_in)by(apply shuffle_words;exact Wplus).
 assert(Cabi:constants ab_in)by(apply stage_constants;exact Cplus).
 assert(ABx:forall i,(i<5)%nat -> rfield ab_in 0 i=rfield xy 0 i).
 { intros i I;unfold ab_in,rfield,get,plus;rewrite stage1_registers,add_inputs by lia;reflexivity. }
 assert(ABy:forall i,(i<5)%nat -> rfield ab_in 5 i=rfield xy 5 i).
 { intros i I;unfold ab_in,rfield,get,plus;rewrite stage1_registers,add_inputs by lia;reflexivity. }
 assert(Xabi:loose(rfield ab_in 0))by(eapply loose_ext;[intros;symmetry;apply ABx;assumption|exact Xxy]).
 assert(Yabi:loose(rfield ab_in 5))by(eapply loose_ext;[intros;symmetry;apply ABy;assumption|exact Yxy]).
 set(ab:=call j SquarePair(scratch,0)ab_in).
 destruct(call_square j ab_in 0 Wabi Cabi Xabi Yabi (or_introl eq_refl))as[A AV].
 destruct(call_square j ab_in 5 Wabi Cabi Xabi Yabi (or_intror eq_refl))as[B BV].
 change(squared(rfield ab 0))in A;change(squared(rfield ab 5))in B.
 change(represents(limbs(rfield ab 0))(limbs(rfield ab_in 0)*limbs(rfield ab_in 0)))in AV.
 change(represents(limbs(rfield ab 5))(limbs(rfield ab_in 5)*limbs(rfield ab_in 5)))in BV.
 rewrite (limbs_ext _ _ ABx), XY0 in AV.
 rewrite (limbs_ext _ _ ABy), XY5 in BV.
 rewrite XY0,XY5 in SumV.
 assert(Wab:lane_words ab)by(apply call_words;exact Wabi).
 assert(Cab:constants ab)by(apply kernel_constants;exact Cabi).
 set(cd_in:=shuffle j(stage 2 false)ab).
 assert(Wcdi:lane_words cd_in)by(apply shuffle_words;exact Wab).
 assert(Ccdi:constants cd_in)by(apply stage_constants;exact Cab).
 assert(CDz:forall i,(i<5)%nat -> rfield cd_in 0 i=field s point 10 i).
 { intros i I;unfold cd_in;rewrite stage2_z by exact I.
   unfold ab;rewrite call_field. unfold ab_in;rewrite point_unchanged by lia.
   unfold plus;rewrite call_field. unfold xy;apply point_unchanged;lia. }
 assert(CDs:forall i,(i<5)%nat -> rfield cd_in 5 i=rfield plus 10 i).
 { intros i I;unfold cd_in;rewrite stage2_sum by exact I.
   unfold ab;rewrite call_field. apply stage1_sum;exact I. }
 assert(Zcdi:loose(rfield cd_in 0))by(eapply loose_ext;[intros;symmetry;apply CDz;assumption|exact Zb]).
 assert(Scdi:loose(rfield cd_in 5))by(eapply loose_ext;[intros;symmetry;apply CDs;assumption|apply ready_loose;exact Sum]).
 set(cd:=call j SquarePair(scratch,0)cd_in).
 destruct(call_square j cd_in 0 Wcdi Ccdi Zcdi Scdi (or_introl eq_refl))as[CC CV].
 destruct(call_square j cd_in 5 Wcdi Ccdi Zcdi Scdi (or_intror eq_refl))as[DD DV].
 change(squared(rfield cd 0))in CC;change(squared(rfield cd 5))in DD.
 change(represents(limbs(rfield cd 0))(limbs(rfield cd_in 0)*limbs(rfield cd_in 0)))in CV.
 change(represents(limbs(rfield cd 5))(limbs(rfield cd_in 5)*limbs(rfield cd_in 5)))in DV.
 rewrite (limbs_ext _ _ CDz) in CV;rewrite(limbs_ext _ _ CDs)in DV.
 pose proof(ctrans _ _ _ DV (ctimes _ _ _ _ SumV SumV))as Dmath.
 assert(Wcd:lane_words cd)by(apply call_words;exact Wcdi).
 assert(Ccd:constants cd)by(apply kernel_constants;exact Ccdi).
 set(sub_in:=shuffle j(stage 3 false)cd).
 assert(Wsi:lane_words sub_in)by(apply shuffle_words;exact Wcd).
 assert(Csi:constants sub_in)by(apply stage_constants;exact Ccd).
 assert(SC:squared(rfield sub_in 0)).
 { apply(field_bound_ext _ (rfield cd 0));[intros;symmetry;apply stage3_regs;lia|exact CC]. }
 assert(SD:squared(rfield sub_in 5)).
 { apply(field_bound_ext _ (rfield cd 5));[intros;symmetry;apply stage3_regs;lia|exact DD]. }
 assert(SA:forall i,(i<5)%nat -> field sub_in scratch 0 i=rfield ab 0 i).
 { intros i I;unfold sub_in,field;rewrite stage3_cells. change(field cd scratch 0 i=rfield ab 0 i).
   unfold cd;rewrite call_field. apply stage2_a;exact I. }
 assert(SB:forall i,(i<5)%nat -> field sub_in scratch 5 i=rfield ab 5 i).
 { intros i I;unfold sub_in,field;rewrite stage3_cells. change(field cd scratch 5 i=rfield ab 5 i).
   unfold cd;rewrite call_field. apply stage2_b;exact I. }
 assert(SAb:squared(field sub_in scratch 0))by(eapply field_bound_ext;[intros;symmetry;apply SA;assumption|exact A]).
 assert(SBb:squared(field sub_in scratch 5))by(eapply field_bound_ext;[intros;symmetry;apply SB;assumption|exact B]).
 destruct(stage3_bias j cd)as[Bias0 Bias1].
 set(sub:=call j SubtractReduce(scratch,0)sub_in).
 pose proof(fun start=>call_subtract j sub_in start Wsi Csi SC SD SAb SBb Bias0 Bias1)as Sub.
 assert(Wsub:lane_words sub)by(apply call_words;exact Wsi).
 assert(Csub:constants sub)by(apply kernel_constants;exact Csi).
 (* The four small polynomial identities below compose the proved kernels. *)
 assert(SubMath:forall start,In start [0%nat;5%nat;10%nat;15%nat] ->
 ready(rfield sub start) /\ represents(limbs(rfield sub start))
 (preparation_value(lane_coordinates s)(if Nat.eqb start 5 then 15 else if Nat.eqb start 10 then 5 else if Nat.eqb start 15 then 10 else 0))).
 { intros start Member;destruct(Sub start Member)as[Bounds V];split;[exact Bounds|].
   assert(MA:pack(fun i=>cells sub_in(scratch,64*Z.of_nat i))0=limbs(rfield ab 0))by(apply limbs_ext,SA).
   assert(MB:pack(fun i=>cells sub_in(scratch,64*Z.of_nat i))5=limbs(rfield ab 5))by(apply limbs_ext,SB).
   assert(RC:pack(registers sub_in)0=limbs(rfield cd 0)).
   { apply limbs_ext;intros i I;apply stage3_regs;lia. }
   assert(RD:pack(registers sub_in)5=limbs(rfield cd 5)).
   { apply limbs_ext;intros i I;apply stage3_regs;lia. }
   destruct Member as[<- | [<- | [<- | [<- | []]]]];
   cbn [target_value Nat.eqb] in V;rewrite ?MA,?MB,?RC,?RD in V;
   cbn [Nat.eqb preparation_value lane_coordinates cx cy cz].
   all: eapply ctrans;[exact V|].
   - apply cminus;[exact Dmath|apply cplus;assumption].
   - apply cneg,cplus;assumption.
   - apply cminus;assumption.
   - apply cminus;[apply cminus;assumption|apply ctimes;[apply crefl|exact CV]]. }
 change(prepared s (shuffle j(stage 4 false)sub)).
 unfold prepared;split;[apply shuffle_words;exact Wsub|].
 split;[apply stage_constants;exact Csub|]. split.
 - intros coord Member;destruct Member as[<- | [<- | [<- | [<- | []]]]];cbn [stage].
   + destruct(SubMath 0%nat ltac:(cbn [In];auto))as[Bnd V];split.
     * apply(field_bound_ext _ (rfield sub 0));[intros;symmetry;apply stage4_e;assumption|exact Bnd].
     * rewrite(limbs_ext _ _ (stage4_e j sub));exact V.
   + destruct(SubMath 10%nat ltac:(cbn [In];auto))as[Bnd V];split.
     * apply(field_bound_ext _ (rfield sub 10));[intros;symmetry;apply stage4_g;assumption|exact Bnd].
     * rewrite(limbs_ext _ _ (stage4_g j sub));exact V.
   + destruct(SubMath 15%nat ltac:(cbn [In];auto))as[Bnd V];split.
     * apply(field_bound_ext _ (rfield sub 15));[intros;symmetry;apply stage4_f;assumption|exact Bnd].
     * rewrite(limbs_ext _ _ (stage4_f j sub));exact V.
   + destruct(SubMath 5%nat ltac:(cbn [In];auto))as[Bnd V];split.
     * apply(field_bound_ext _ (rfield sub 5));[intros;symmetry;apply stage4_h;assumption|exact Bnd].
     * rewrite(limbs_ext _ _ (stage4_h j sub));exact V.
 - split.
   + intros i I;cbn [stage];split.
     * rewrite(stage4_x j sub i I),(stage4_e j sub i I);reflexivity.
     * rewrite(stage4_z j sub i I),(stage4_g j sub i I);reflexivity.
   + intros coord i. rewrite point_unchanged by lia.
     unfold sub;rewrite call_field. unfold sub_in;rewrite point_unchanged by lia.
     unfold cd;rewrite call_field. unfold cd_in;rewrite point_unchanged by lia.
     unfold ab;rewrite call_field. unfold ab_in;rewrite point_unchanged by lia.
     unfold plus;rewrite call_field. unfold xy;apply point_unchanged;lia.
Qed.
