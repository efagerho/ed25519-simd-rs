From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import execution.Blocks isa.Instructions execution.WordBounds.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.CachedAdd Require Import Program CachedAddABI Kernels Lane Control Bounds KernelCalls Calls Routing CachedAddSpec.
Import ListNotations. Open Scope Z_scope.
Local Opaque prefix_state.
Lemma affine_z j full s : Bounds.input_bounds true s ->forall i,(i<5)%nat ->
 R j full true 19 s 0 i=2*field s point 10 i.
Proof.
 intros B i I.
 assert(Input:0<=field s point 10 i<split).
 { specialize (B (point,64*Z.of_nat(10+i))).
   do 5 (destruct i as [|i]; [exact (B eq_refl)|]);lia. }
 unfold R;rewrite(prefix_segment j full true 0 19 s ltac:(lia)).
 destruct full;do 5(destruct i as[|i];[
 match type of Input with 0 <= ?v < split => change(Arithmetic.vpaddq v v=2*v) end;
 unfold Arithmetic.vpaddq,X86.low64;rewrite Z.land_ones by lia;
 rewrite Z.mod_small by(unfold split in Input;lia);ring|]);lia.
Qed.
Lemma affine_z_value j full s : Bounds.input_bounds true s ->
 limbs(R j full true 19 s 0)=2*limbs(field s point 10).
Proof. intro B;unfold limbs;repeat rewrite(affine_z j full s B)by lia;ring. Qed.
Definition lane_value s region c := limbs(field s region(5*c)).
Theorem arithmetic_coordinates j full affine s : lane_words s ->Bounds.input_bounds affine s ->
 forall c,(c<4)%nat ->represents(limbs(M j full affine 67 s point(5*c)))
 (coordinate (add full (point_from_fields(lane_value s point))
   (cache_from_fields affine(lane_value s cached))) c).
Proof.
 intros W Bounds.
 set(x:=limbs(field s point 0));set(y:=limbs(field s point 5));
 set(z:=limbs(field s point 10));set(t:=limbs(field s point 15)).
 set(q0:=limbs(field s cached 0));set(q1:=limbs(field s cached 5));
 set(q2:=limbs(field s cached 10));set(q3:=limbs(field s cached 15)).
 set(a:=(y-x)*q0);set(b:=(y+x)*q1);set(cc:=t*q2);
 set(d:=if affine then 2*z else z*q3).
 assert(Diff:represents(limbs(R j full affine 5 s 0))(y-x)).
 { pose proof(site_correct j full affine s AB 0 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j full affine 5 s 0))
    (limbs(M j full affine 4 s point 5)-limbs(M j full affine 4 s point 0)))in V.
   rewrite(limbs_ext _ _ (ab_x j full affine s)),(limbs_ext _ _ (ab_y j full affine s))in V;exact V. }
 assert(Sum:represents(limbs(R j full affine 5 s 5))(y+x)).
 { pose proof(site_correct j full affine s AB 5 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j full affine 5 s 5))
    (limbs(M j full affine 4 s point 5)+limbs(M j full affine 4 s point 0)))in V.
   rewrite(limbs_ext _ _ (ab_x j full affine s)),(limbs_ext _ _ (ab_y j full affine s))in V;exact V. }
 assert(A:represents(limbs(R j full affine 6 s 5))a).
 { pose proof(site_correct j full affine s ProductsAB 5 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j full affine 6 s 5))
    (limbs(R j full affine 5 s 0)*limbs(M j full affine 5 s cached 0)))in V.
   rewrite(limbs_ext _ _ (ab_right0 j full affine s))in V.
   eapply ctrans;[exact V|apply ctimes;[exact Diff|apply crefl]]. }
 assert(B:represents(limbs(R j full affine 6 s 0))b).
 { pose proof(site_correct j full affine s ProductsAB 0 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j full affine 6 s 0))
    (limbs(R j full affine 5 s 5)*limbs(M j full affine 5 s cached 5)))in V.
   rewrite(limbs_ext _ _ (ab_right5 j full affine s))in V.
   eapply ctrans;[exact V|apply ctimes;[exact Sum|apply crefl]]. }
 assert(CD:represents(limbs(R j full affine 19 s 5))cc /\
           represents(limbs(R j full affine 19 s 0))d).
 { destruct affine.
   - pose proof(site_correct j full true s ProductCD 0 W Bounds ltac:(cbn;auto))as V.
     change(represents(limbs(R j full true 18 s 0))
      (limbs(R j full true 17 s 0)*limbs(M j full true 17 s cached 10)))in V.
     rewrite(limbs_ext _ _ (cd_t j full true s)),(limbs_ext _ _ (cd_right10 j full true s))in V.
     split;[rewrite(limbs_ext _ _ (cd_affine_c j full s));exact V|].
     rewrite(affine_z_value j full s Bounds);apply crefl.
   - split.
     + pose proof(site_correct j full false s ProductCD 5 W Bounds ltac:(cbn;auto))as V.
       change(represents(limbs(R j full false 19 s 5))
        (limbs(R j full false 18 s 0)*limbs(M j full false 18 s cached 10)))in V.
       rewrite(limbs_ext _ _ (cd_t j full false s)),(limbs_ext _ _ (cd_right10 j full false s))in V;exact V.
     + pose proof(site_correct j full false s ProductCD 0 W Bounds ltac:(cbn;auto))as V.
       change(represents(limbs(R j full false 19 s 0))
        (limbs(R j full false 18 s 5)*limbs(M j full false 18 s cached 15)))in V.
       rewrite(limbs_ext _ _ (cd_z j full s)),(limbs_ext _ _ (cd_right15 j full s))in V;exact V. }
 destruct CD as[C D].
 assert(F:represents(limbs(R j full affine 20 s 0))(d-cc)).
 { pose proof(site_correct j full affine s FG 0 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j full affine 20 s 0))
    (limbs(R j full affine 19 s 0)-limbs(R j full affine 19 s 5)))in V.
   eapply ctrans;[exact V|apply cminus;assumption]. }
 assert(G:represents(limbs(R j full affine 20 s 10))(d+cc)).
 { pose proof(site_correct j full affine s FG 10 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j full affine 20 s 10))
    (limbs(R j full affine 19 s 0)+limbs(R j full affine 19 s 5)))in V.
   eapply ctrans;[exact V|apply cplus;assumption]. }
 assert(E:represents(limbs(R j full affine 31 s 0))(b-a)).
 { pose proof(site_correct j full affine s EH 0 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j full affine 31 s 0))
    (limbs(M j full affine 30 s scratch 5)-limbs(M j full affine 30 s scratch 0)))in V.
   rewrite(limbs_ext _ _ (eh_a j full affine s)),(limbs_ext _ _ (eh_b j full affine s))in V.
   eapply ctrans;[exact V|apply cminus;assumption]. }
 assert(H:represents(limbs(R j full affine 31 s 10))(b+a)).
 { pose proof(site_correct j full affine s EH 10 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j full affine 31 s 10))
    (limbs(M j full affine 30 s scratch 5)+limbs(M j full affine 30 s scratch 0)))in V.
   rewrite(limbs_ext _ _ (eh_a j full affine s)),(limbs_ext _ _ (eh_b j full affine s))in V.
   eapply ctrans;[exact V|apply cplus;assumption]. }
 assert(X:represents(limbs(R j full affine 43 s 0))((b-a)*(d-cc))).
 { pose proof(site_correct j full affine s XZ 0 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j full affine 43 s 0))
    (limbs(R j full affine 42 s 0)*limbs(M j full affine 42 s scratch 10)))in V.
   rewrite(limbs_ext _ _ (xz_e j full affine s)),(limbs_ext _ _ (xz_f j full affine s))in V.
   eapply ctrans;[exact V|apply ctimes;assumption]. }
 assert(Z:represents(limbs(R j full affine 43 s 5))((d-cc)*(d+cc))).
 { pose proof(site_correct j full affine s XZ 5 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j full affine 43 s 5))
    (limbs(R j full affine 42 s 5)*limbs(M j full affine 42 s scratch 10)))in V.
   rewrite(limbs_ext _ _ (xz_g j full affine s)),(limbs_ext _ _ (xz_f j full affine s))in V.
   rewrite Z.mul_comm;eapply ctrans;[exact V|apply ctimes;assumption]. }
 assert(Y:represents(limbs(R j full affine (if full then 56 else 55) s 0))((d+cc)*(b+a))).
 { pose proof(site_correct j full affine s YT 0 W Bounds ltac:(destruct full;cbn;auto))as V.
   assert(Value:represents(limbs(R j full affine (if full then 56 else 55)s 0))
    (limbs(R j full affine (if full then 55 else 54)s 0)*limbs(M j full affine (if full then 55 else 54)s scratch 5)))
    by(destruct full;exact V).
   rewrite(limbs_ext _ _ (yt_g j full affine s)),(limbs_ext _ _ (yt_h j full affine s))in Value.
   eapply ctrans;[exact Value|apply ctimes;assumption]. }
 assert (CarriedY : represents (limbs (R j full affine 56 s 0)) ((d+cc)*(b+a))).
 { destruct full; [exact Y|]. eapply ctrans; [|exact Y].
   apply (call_correct j false affine 55 s CarryY [] 0 W Bounds).
   - destruct affine; reflexivity.
   - destruct affine; vm_compute; reflexivity.
   - now left. }
 assert(T:full=true ->represents(limbs(R j full affine 56 s 5))((b-a)*(b+a))).
 { intro Full;subst full;pose proof(site_correct j true affine s YT 5 W Bounds ltac:(cbn;auto))as V.
   change(represents(limbs(R j true affine 56 s 5))
    (limbs(R j true affine 55 s 5)*limbs(M j true affine 55 s scratch 5)))in V.
   rewrite(limbs_ext _ _ (yt_e j affine s)),(limbs_ext _ _ (yt_h j true affine s))in V.
   eapply ctrans;[exact V|apply ctimes;assumption]. }
 intros c C0;destruct c as[|[|[|[|c]]]];try lia;cbn [Nat.mul Nat.add].
 - rewrite(limbs_ext _ _ (out_x j full affine s));destruct affine;exact X.
 - rewrite(limbs_ext _ _ (out_y j full affine s));destruct affine;exact CarriedY.
 - rewrite(limbs_ext _ _ (out_z j full affine s));destruct affine;exact Z.
 - destruct full.
   + rewrite(limbs_ext _ _ (out_t j affine s));destruct affine;exact(T eq_refl).
   + rewrite(limbs_ext _ _ (out_zero j affine s));apply crefl.
Qed.
