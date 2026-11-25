From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch
 memory.WriteTrace memory.FlatMemory memory.ByteMemory memory.MemoryGeometry abi.SysV.
From Machine Require abi.FramePointer.
From Curve25519 Require Import SignedRadix16 Scalar.
From ProofArithmetic Require Import Radix.
From Ed25519Simd.Radix16 Require Object.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require CandidateDigest.
Import ListNotations. Local Open Scope Z_scope.
Module D := Ed25519Simd.Radix16.Audit.
Local Notation pc := Radix16.LinkedBytes.wrapper_pc.
Local Notation helper := Radix16.LinkedBytes.reducer_pc.
Local Notation text := Radix16.LinkedBytes.symbol_bytes.
Local Notation code := Scalar.ObjectBytes.symbol_bytes.
Local Notation n := (D.size text).
Local Notation d := CandidateDigest.dst.

Lemma helper_image pol : In (helper,code) (children pol).
Proof. apply in_or_app;left;do 10 right;left;reflexivity. Qed.

(* Derive both nested stack slots and the entire output buffer from the
   production allocation. The reducer needs no additional placement premise. *)
Lemma frame e : Return.placement e ->
 sp e-16384<=d e-24 /\ d e+512<=Rows.frame e /\ Rows.frame e+512<=sp e /\
 (d e-8) mod 16=8.
Proof.
 intro P;unfold CandidateDigest.dst,CandidateDigest.top,ScoreFrame.buffer,FramePointer.bottom.
 pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Gap.
 pose proof(Z.div_mod (ScoreFrame.top e-48) 64 ltac:(lia)) as Q.
 repeat split;try (unfold ScoreFrame.top,Rows.frame,sp in *;lia).
 replace (ScoreFrame.top e-48-(ScoreFrame.top e-48) mod 64-1280-8-16-520-8)
  with (8+(4*((ScoreFrame.top e-48)/64)-115)*16) by lia.
 rewrite Z.mod_add by lia;reflexivity.
Qed.
Lemma layout pol bias e : Return.placement e -> loaded pol bias (mem e) (writable e) ->
 D.placement (d e-8) (d e) (Rows.frame e) (bias+pc) n (bias+helper) (D.size code).
Proof.
 intros P I;destruct(frame _ P) as [Low [Gap [High Al]]];destruct(stack_ok _ P) as [[S T] _].
 assert (Away:forall a bs,In (a,bs) (children pol) -> 0<D.size bs ->
   forall base len,sp e-16384<=base -> base+len<=sp e -> 0<len ->
   disjoint base len (bias+a) (D.size bs)).
 { intros a bs A B base len U V L;apply ScalarInputs.apart;[exact L|exact B|].
   intros x X Inside;apply (immutable _ _ _ _ I x);[left;exists a,bs;auto|left;unfold span;lia]. }
 constructor;try exact Al;try (unfold fits64,disjoint;lia).
 intros a len [E|[E|[]]];injection E as <- <-.
 all: split;[apply (symbols _ _ _ _ I);apply CandidateDigest.in_image || apply helper_image|].
 all: repeat apply conj;apply Away;try apply CandidateDigest.in_image;try apply helper_image;try lia;vm_compute;reflexivity.
Qed.

(* The trace argument identifies both the native return state and every store
   to the digest wrapper or the invoked Montgomery reducer. *)
Definition observed bias q t :=
 ip q=bias+pc /\ mapped (mem(machine q)) (ip q) text /\ mapped (mem(machine q)) (bias+helper) code /\
 D.run bias pc helper n (machine q) (ip t) (machine t) /\
 exists ws,D.traced bias pc helper n (machine q) (ip t) (machine t) ws /\ log t=log q++ws.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record returned pol bias e q t:Prop:=Returned {
 back:ip t=CandidateDigest.origin pol bias+29;
 writes:accounted e (writable e) t;
 stack:regs(machine t) 4%nat=d e;
 saved:forall r,In r sysv_saved -> regs(machine t) r=regs(machine q) r;
 outside:preserved (fun x=>~D.writable (d e-8) (d e) x) (mem(machine q)) (mem(machine t));
 words:well_formed(machine t);
 digits:forall j,(j<8)%nat ->
   let ds:=D.signed_digits (mem(machine t)) (d e) j in
   Forall (fun v=> -8<=v<8) ds /\ (HashLayout.eligible pol e j ->
    number 16 ds = little_endian (SHA512.Spec.sha512
     (r_bytes(HashLayout.row e j)++key_bytes(HashLayout.row e j)++message(HashLayout.row e j))) mod L);
 buffers:ScoreBuffers.data e (machine t)
}.

Theorem checked pol bias e p q : Return.placement e -> loaded pol bias (mem e) (writable e) ->
 CandidateEntry.entry pol bias e p -> CandidateDigest.entry pol bias e p q ->
 (exists t,observed bias q t) /\ (forall t,observed bias q t -> returned pol bias e q t).
Proof.
 intros P I E Q;pose proof(CandidateDigest.pc _ _ _ _ _ Q) as PC.
 pose proof(CandidateDigest.stack _ _ _ _ _ Q) as SP;pose proof(CandidateDigest.output _ _ _ _ _ Q) as DI.
 pose proof(CandidateDigest.input _ _ _ _ _ Q) as SI;pose proof(CandidateDigest.writes _ _ _ _ _ Q) as Acc.
 pose proof(CandidateDigest.words _ _ _ _ _ Q) as W.
 set (s:=machine q) in *;set (ret:=read_word (mem s) (regs s 4%nat)).
 assert (Pl:D.placement (regs s 4%nat) (regs s 7%nat) (regs s 6%nat) (bias+pc) n (bias+helper) (D.size code))
  by (rewrite SP,DI,SI;exact (layout _ _ _ P I)).
 pose proof Radix16.Object.assembled_digest_to_radix16_correct as Verified.
 destruct(D.run_correct _ _ _ _ Verified bias s Pl W) as [out [Run [Unique [Stack [Saved [M [Words Digits]]]]]]].
 fold ret in Run,Unique.
 destruct(D.write_footprint _ _ _ _ Verified bias s ret out Pl W Run) as [ws [Trace [Replay Conf]]].
 specialize(Conf ws [] (eq_sym(app_nil_r ws)));rewrite SP,DI in Conf,M.
 destruct(frame _ P) as [Low [Gap [High _]]].
 assert (Loan:forall x,D.writable (d e-8) (d e) x -> sp e-16384<=x<Rows.frame e) by (unfold D.writable;lia).
 assert (Safe:confined (writable e) ws).
 { eapply Forall_impl;[|exact Conf];intros w H x X;left;specialize(Loan x (H x X));unfold span,Rows.frame,sp in *;lia. }
 split.
 - exists (Cursor ret out None (log q++ws));unfold observed;cbn [ip machine log];rewrite PC.
   split;[reflexivity|];split;[exact (proj1(mapped_now _ _ _ I _ _ _ Acc (CandidateDigest.in_image pol)))|].
   split;[exact (proj1(mapped_now _ _ _ I _ _ _ Acc (helper_image pol)))|].
   split;[exact Run|exists ws;auto].
 - intros [target final cf events] [_ [_ [_ [R [actual [T Log]]]]]];cbn [ip machine log] in *.
   destruct(Unique _ _ R) as [-> ->];pose proof(D.trace_unique _ _ _ _ Verified bias s ret out actual ws T Trace) as ->;subst events.
   constructor.
   + unfold ret;rewrite SP;exact (CandidateDigest.link _ _ _ _ _ Q).
   + exact (append_accounted _ _ _ _ _ cf _ Acc Safe Replay).
   + cbn [machine];rewrite Stack,SP;ring.
   + exact Saved.
   + exact M.
   + exact Words.
   + intros j J;specialize(Digits j J);cbv zeta in Digits;rewrite DI,SI in Digits.
     split;[exact (proj1 Digits)|intro On];cbn [machine];rewrite (proj2 Digits),<-(CandidateEntry.digest _ _ _ _ E j J On);f_equal.
     unfold Scalar.ScalarSpec.lane_input;f_equal;apply map_ext_in;intros k K;unfold buffer_words.
     apply preserved_read with (outside:=CandidateEntry.retained e);[exact (CandidateDigest.parent _ _ _ _ _ Q)|].
     intros b B;right;change (0<=b<8) in B;lia.
   + eapply ScoreBuffers.keep;[|exact (CandidateEntry.buffers _ _ _ _ E)].
     intros x X;transitivity (mem s x).
     * apply M;intro A;specialize(Loan x A);destruct(scratch_stack _ P);unfold ScoreBuffers.region,span,Rows.frame,sp in *;lia.
     * apply (CandidateDigest.parent _ _ _ _ _ Q);destruct(scratch_stack _ P);unfold ScoreBuffers.region,CandidateEntry.retained,span,Rows.frame,sp in *;lia.
Qed.
End Iteration.
