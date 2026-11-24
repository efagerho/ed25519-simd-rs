From Coq Require Import List ZArith Lia Bool.
From Ed25519Simd.Zip215 Require Schedule.
From Ed25519Simd.VerifyBatch Require Import Policy Routing Rows Prepare.
From Machine Require Import execution.LinkedCalls.
Local Open Scope nat_scope.

Definition count e := Z.to_nat (regs e 6%nat).
Definition position e := output_index (mem e) (regs e 7%nat).
Definition indices e :=
 (forall i,i<count e -> position e i<count e) /\
 (forall i j,i<count e -> j<count e -> position e i=position e j -> i=j).
Definition metadata c flags := Schedule.Lanes (live c) (index_of (entry c) (first c) (live c)) flags.

Lemma active_position c j : 0<live c<=8 -> j<live c ->
 Schedule.index (metadata c (fun _=>false)) j=position (entry c) (first c+j).
Proof. intros L J;unfold metadata,index_of,row_no,position;cbn [Schedule.index].
 rewrite source_lane_live by lia;reflexivity. Qed.
Lemma positions c flags : 0<live c<=8 -> first c+live c<=count(entry c) -> indices(entry c) ->
 Schedule.positions (metadata c flags) (count(entry c)).
Proof.
 intros L N [Bound _];split;[exact (proj2 L)|]. intros j J.
 change (Schedule.index (metadata c (fun _=>false)) j<count(entry c)).
 rewrite active_position by (cbn in J;lia). apply Bound;cbn [metadata Schedule.active] in J;lia.
Qed.

(* Preserve the previous physical byte at every untouched index, including
   when the caller supplied an uninitialized output buffer. *)
Definition store (out:nat->Z) index v i := if Nat.eqb i index then v else out i.
Fixpoint publish n j (meta:Schedule.lanes) mask out := match n with
 | O=>out | S t=>let flag:=Schedule.eligible meta j && Z.testbit mask (Z.of_nat j) in
   publish t (S j) meta mask (store out (Schedule.index meta j) (Z.b2z flag)) end.
Definition scoring c flags mask out result :=
 let meta:=metadata c flags in exists bits,
 Schedule.scatter meta (count (entry c)) mask (fun i=>Z.eqb (out i) 1)=Some bits /\
 result=publish (live c) 0 meta mask out.

Lemma scatter_total c flags mask out : 0<live c<=8 -> first c+live c<=count(entry c) -> indices(entry c) ->
 exists result,scoring c flags mask out result.
Proof.
 intros L N I. eexists;unfold scoring;eexists;split;[apply Schedule.scatter_lanes;
   [apply positions;assumption|intros;reflexivity]|reflexivity].
Qed.
Lemma publish_outside n j meta mask out i :
 (forall k,j<=k<j+n -> Schedule.index meta k<>i) -> publish n j meta mask out i=out i.
Proof.
 revert j out;induction n as [|n IH];intros j out H;[reflexivity|].
 cbn [publish]. rewrite IH by (intros;apply H;lia).
 unfold store;destruct (Nat.eqb_spec i (Schedule.index meta j));[subst;exfalso;apply (H j);lia|reflexivity].
Qed.
Lemma publish_at n j meta mask out k :
 j<=k<j+n ->
 (forall a b,j<=a<j+n -> j<=b<j+n -> Schedule.index meta a=Schedule.index meta b -> a=b) ->
 publish n j meta mask out (Schedule.index meta k)=
 Z.b2z (Schedule.eligible meta k && Z.testbit mask (Z.of_nat k)).
Proof.
 revert j out;induction n as [|n IH];intros j out K Unique;[lia|].
 cbn [publish];destruct (Nat.eq_dec k j) as [->|Later].
 - rewrite publish_outside. + unfold store;now rewrite Nat.eqb_refl.
   + intros a A Eq;apply Unique in Eq;lia.
 - apply IH;[lia|intros a b A B Eq;apply Unique;auto;lia].
Qed.

Definition prefix e policy n out := forall i,i<n ->
 exists v:bool,out (position e i)=Z.b2z v /\ (v=true <->signature_accepts policy (read_input (mem e) (regs e 7%nat) i)).
Lemma next_prefix c flags mask out result : 0<live c<=8 -> first c+live c<=count(entry c) ->
 indices(entry c) -> prefix (entry c) (mode c) (first c) out ->
 scoring c flags mask out result ->
 (forall j,j<live c -> ((flags j && Z.testbit mask (Z.of_nat j))%bool=true <->signature_accepts (mode c) (input_at c j))) ->
 prefix (entry c) (mode c) (first c+live c) result.
Proof.
 intros L N [_ Inj] Before [_ [_ ->]] Verdict i I.
 assert (Index:forall j,j<live c -> Schedule.index (metadata c flags) j=position(entry c)(first c+j)).
 { intros j J;exact (active_position c j L J). }
 destruct (Nat.lt_ge_cases i (first c)) as [Old|New].
 - rewrite publish_outside;[apply Before,Old|]. intros k K Eq;rewrite Index in Eq by lia.
   apply Inj in Eq;lia.
 - set (j:=i-first c). assert (J:j<live c) by (unfold j;lia). assert (E:first c+j=i) by (unfold j;lia).
   exists (flags j && Z.testbit mask (Z.of_nat j))%bool. split.
   + replace (position(entry c)i) with (Schedule.index (metadata c flags) j) by (rewrite Index,E;auto).
     apply publish_at;[lia|]. intros a b A B Eq;rewrite !Index in Eq by lia;apply Inj in Eq;lia.
   + specialize (Verdict j J). unfold input_at,original_row,row_no in Verdict.
     rewrite source_lane_live,E in Verdict by lia;exact Verdict.
Qed.

(* Rust allocates one bool per descriptor. Distinct in-range positions cover
   every byte of this allocation, even when the descriptors were sorted. *)
Lemma indices_cover e : indices e -> forall j,j<count e ->
 exists i,i<count e /\ position e i=j.
Proof.
 intros [Bounds Unique] j J. set (xs:=seq 0 (count e)).
 assert (InRange:forall i, In i xs <-> i<count e).
 { intros i;unfold xs;rewrite in_seq;lia. }
 assert (Mapped:forall l,incl l xs -> NoDup l -> NoDup (map (position e) l)).
 { intros l Incl N;induction N as [|i l Fresh N IH];cbn;constructor.
   - intro H;apply in_map_iff in H as [k [Eq K]]. apply Fresh.
     assert (k=i) by (apply Unique;[apply InRange,Incl;right|apply InRange,Incl;left|];auto).
     congruence.
   - apply IH;intros k K;apply Incl;right;assumption. }
 assert (Subset:incl (map (position e) xs) xs).
 { intros i H;apply in_map_iff in H as [k [<- K]]. apply InRange,Bounds,InRange,K. }
 assert (Cover:incl xs (map (position e) xs)).
 { apply NoDup_length_incl;[apply Mapped;[apply incl_refl|apply seq_NoDup]|rewrite map_length;lia|exact Subset]. }
 apply InRange in J;apply Cover in J;apply in_map_iff in J as [i [Eq I]].
 exists i;split;[apply InRange,I|exact Eq].
Qed.
