From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls memory.FlatMemory memory.ByteMemory memory.MemoryGeometry.
From Ed25519Simd.PrepareChunk Require Object.
From Ed25519Simd.Sha512Challenge Require Object.
From Ed25519Simd.Zip215 Require Object.
From Ed25519Simd.DalekPostHash Require Object.
From Ed25519Simd.VerifyBatch Require Import Policy Image Control Scatter Loop Return LoadedImage EntryWrites CallWrites NestedRegions Prologue StageEntry RejectCall Audit TableCertificate ZipBytes DalekBytes.
From Ed25519Simd.VerifyBatch Require StrictAccept.
Local Open Scope Z_scope.

Lemma linked_calls pol : callees pol.
Proof.
 split;[exact PrepareChunk.Object.assembled_prepare_chunk_correct|].
 split;[exact Sha512Challenge.Object.assembled_sha512_challenge_correct|].
 destruct pol;[exact Zip215.Object.assembled_zip215_correct|].
 split;[exact DalekPostHash.Object.assembled_dalek_post_hash_correct|].
 vm_compute;split;reflexivity.
Qed.

Lemma grouped pol pc text : matches pc (destination pol) text ->
 forall bias e, admissible pol bias pc text e ->
 (exists ip final,execution pol bias pc text (bias+pc) e ip final) /\
 (forall ip final,execution pol bias pc text (bias+pc) e ip final -> returned pol e ip final).
Proof.
 intro Image.
 intros bias e [_ _ W SP Inputs _]. pose proof(entry_paths(count e)) as [Path [Choose _]].
 split.
 - destruct (Nat.eqb_spec (count e) 0) as [Zero|Live].
   + destruct(empty_return e) as [ip final] eqn:E. exists ip,final;eapply empty_path;eauto.
   + destruct(Inputs ltac:(lia)) as [_ [_ [_ [Maps [I P]]]]].
     pose proof(Tables.loaded _ _ static_tables_correct Maps) as T.
     destruct(Loop.progress e pol bias P T I (count e) 0%nat (fun i=>mem e(output e+Z.of_nat i))
       ltac:(lia) eq_refl) as [out Run].
     destruct(Return.resume e (fill e (fun _=>0) (fun _=>0) out) e) as [ip final] eqn:E.
     exists ip,final;eapply batch_path;try eassumption;unfold byte_memory;intros;lia.
 - intros ip final Run. inversion Run as [e' ip' f' Im Start E|
     e' ip' f' out stk scr noise Im Start Go Batch Stk Scr Noise E];subst.
   + rewrite Path in Start. destruct (Nat.eqb_spec (count e) 0) as [Zero|N];[|discriminate].
     pose proof(Return.empty e W SP) as ABI;rewrite E in ABI.
     destruct ABI as [Rip [Rax [Rsp [Saved Memory]]]].
     unfold returned;repeat apply conj;try assumption.
     * unfold preserved;rewrite Memory;auto.
     * rewrite Memory;apply W.
     * intros j J;lia.
     * intros i I;lia.
   + rewrite Path in Start. destruct (Nat.eqb_spec (count e) 0) as [Zero|N];[discriminate|].
     destruct(Inputs ltac:(lia)) as [Place [_ [_ [Maps [I P]]]]].
     pose proof(Tables.loaded _ _ static_tables_correct Maps) as T.
     pose proof(Return.finish e stk scr out noise Place) as ABI;rewrite E in ABI.
     destruct ABI as [Rip [Rax [Rsp [Saved [Out Outside]]]]].
     pose proof(Loop.sound e pol bias P T I _ _ _ _ Batch eq_refl
       ltac:(unfold prefix;intros;lia)) as Valid.
     assert (BoolOut:forall j,(j<count e)%nat -> out j=0 \/ out j=1).
     { intros j J. destruct (indices_cover e I j J) as [i [Bound <-]].
       destruct(Valid i Bound) as [[] [V _]];cbn in V;auto. }
     unfold returned;repeat apply conj;try assumption.
     * assert (M:byte_memory (fill e stk scr out)) by
         (apply all_bytes;auto;intros j J;destruct(BoolOut j J);lia).
       pose proof (f_equal (fun c=>mem (snd c)) E) as End.
       change (fill e stk scr out=mem final) in End;now rewrite <- End.
     * intros j J;rewrite Out by exact J;apply BoolOut,J.
     * intros i Bound;rewrite Out by (apply I;exact Bound);exact (Valid i Bound).
Qed.

Lemma scalar_from_entry pol pc text bias e c masks : admissible pol bias pc text e -> (0<count e)%nat ->
 StageEntry.physical (bias+pc) text (destination pol Prepare-pc) e ->
 exists stop, BatchScalar.observe pol bias (bias+pc) text e c masks=Some stop /\
              BatchScalar.post pol bias (bias+pc) e stop.
Proof.
 intros Input N Entry. apply BatchScalar.from_entry.
 - exact (proj1 (batch_inputs _ _ _ _ _ Input N)).
 - exact (callee_image _ _ _ _ _ Input N).
 - destruct pol;exact Entry.
Qed.

Definition rejected_inputs pol e:=forall j,(j<8)%nat -> (j<count e)%nat ->
 ~signature_accepts pol (read_input (mem e) (regs e 7%nat) j).

Definition active_chunk e:=exists j,(j<8)%nat /\ EligibleLanes.candidate e j.
Definition at_boundary pol bias pc e b:=let entry:=bias+pc in match b with
 | FirstDispatch.Completed q=>RejectExecution.post entry e (RejectExecution.BatchReturned q) /\ rejected_inputs pol e /\ ~HashLayout.active pol e
 | FirstDispatch.MoreChunks q=>RejectExecution.post entry e (RejectExecution.NextChunk q) /\ ~HashLayout.active pol e
 | FirstDispatch.HashReturned q r=>HashLayout.active pol e /\ NativeHash.returned pol bias entry e q r /\
    ScoreInputs.inputs pol e (LinkedRun.machine q) /\ well_formed(LinkedRun.machine q) end.
Lemma after_reject pol bias pc e r : rejected_inputs pol e -> ~HashLayout.active pol e -> RejectExecution.post (bias+pc) e r ->
 at_boundary pol bias pc e (FirstDispatch.after_reject r).
Proof. destruct r;cbn;auto. Qed.

Lemma dispatch_correct pol bias pc text e c ks : admissible pol bias pc text e -> StrictDispatch.bound pc text -> (0<count e)%nat ->
 first_chunk pol bias pc text e c ks ->
 exists b,FirstDispatch.run pol bias pc text e c ks=Some b /\ at_boundary pol bias pc e b.
Proof.
 intros Input Hash N.
 destruct(batch_inputs _ _ _ _ _ Input N) as [Place [_ [[_ Sep] _]]];pose proof(callee_image _ _ _ _ _ Input N) as Loaded.
 pose proof(decoder_aligned _ _ _ _ _ Input N) as Al;intros [s [Scalar [_ [Digits [Checked Rejected]]]]];destruct(Z.eqb_spec (regs(LinkedRun.machine s) 0%nat mod 2^32) 0) as [Z|Live].
 - destruct(Rejected Z) as [Invalid [r [End Post]]];exists(FirstDispatch.after_reject r);split;
   [eapply FirstDispatch.scalar_path;[exact Scalar|exact Z|exact End]|apply after_reject;[exact Invalid| |exact Post]].
   intros [j [J On]];destruct (HashLayout.candidate_of _ _ _ On) as [Canon _];destruct Digits as [Bound Bits];specialize(Bits j J).
   apply (proj2(proj1 Bits)) in Canon;rewrite Z.mod_small in Z by lia;rewrite Z,Z.bits_0 in Canon;discriminate.
 - destruct(Checked Live) as [d [Run [Decoder [Handoff Calls]]]];destruct Calls as [bank [t [Bank [Trace [Check [Frame Reject]]]]]].
   unfold FirstDispatch.run,BatchDecode.observe in *;rewrite Scalar in Run|-*;cbn [LinkedRun.bind] in Run|-*;
   rewrite (proj2(Z.eqb_neq _ _) Live) in Run|-*;rewrite Run;cbn [LinkedRun.bind];rewrite Bank;cbn [LinkedRun.bind];rewrite Trace;cbn [LinkedRun.bind].
   destruct(Z.eqb_spec (regs(LinkedRun.machine(EligibleLanes.stopped t)) 14%nat) 0) as [Zero|Yes].
   + destruct(Reject Zero) as [r [End Post]];rewrite End;exists(FirstDispatch.after_reject r);split;[reflexivity|].
     apply after_reject;[exact (EligibleLanes.zero_rejects _ _ _ _ _ (proj2 Check) Zero)|intros [j [J On]];apply (proj2(EligibleLanes.live_branch _ _ _ _ _ (proj2 Check)) ltac:(exists j;split;[exact J|apply (HashLayout.candidate_of _ _ _ On)])),Zero|exact Post].
   + assert (Enc:PreparedInputs.operands e (LinkedRun.machine(EligibleLanes.stopped t))).
     { eapply PreparedInputs.from_decoder;[exact Place|exact Digits|exact Handoff| |exact Check].
       destruct Decoder as [_ [_ [_ [_ [_ [_ [_ Data]]]]]]];exact Data. }
     destruct(PreparedReturn.from_eligible _ _ _ _ _ _ (TableMask.masks t) Place Loaded Al (proj2 Check) Frame (PreparedTables.input _ _ _ _ _ Place Check) Enc Yes) as [q [bank1 [Call Done]]].
     destruct(ReadyDispatch.checked pol bias pc text e q bank1 (proj1 Hash) Place Loaded (entry_range _ _ _ _ _ Input) (entry_text _ _ _ _ _ Input) Sep Done)
        as [v [kv [RunCall [Reached Child]]]];unfold ReadyDispatch.observe;rewrite Call;cbn [LinkedRun.bind];rewrite RunCall.
     assert (Active:=proj1(EligibleLanes.live_branch _ _ _ _ _ (proj2 Check)) Yes).
     destruct(batch_inputs _ _ _ _ _ Input N) as [_ [[_ Slices] [_ [Tables [Idx Entries]]]]].
     assert (Borrow:NativeHash.messages_immutable e).
     { intros j k J K;destruct(Slices _ (TailCopy.live_row e j N)) as [_ [_ [_ B]]];apply B;unfold NativeHash.field in K|-*;lia. }
     specialize (Entries 0%nat (count e) zero_loc N eq_refl zero_words).
     destruct pol.
     * destruct Active as [j [J On]];assert (LiveZip:HashLayout.active Zip215 e) by (exists j;split;[exact J|now apply HashLayout.candidate]).
       destruct(NativeHash.checked Zip215 _ _ _ _ _ Place Loaded N Entries Borrow LiveZip (HashLayout.zip_flags _ _ _ _ Done)
         (PreparedReturn.encodings _ _ _ _ _ Done) Child) as [r [HashRun HashPost]].
       eexists;split;[cbn [LinkedRun.bind fst snd FirstDispatch.continue FirstDispatch.hash_return];unfold FirstDispatch.hash_return;now rewrite HashRun|exact (conj LiveZip (conj HashPost (conj (ScoreInputs.at_hash _ _ _ _ _ _ Place (ScoreInputs.zip _ _ _ _ Done) Child) (HashEntry.words _ _ _ _ _ Child))))].
     * destruct(StrictReturn.from_entry _ _ _ _ _ kv Place Loaded Tables Done Child) as [out [k [FilterRun Post]]].
       destruct(StrictDispatch.checked bias pc text e v out k Hash Place Loaded (entry_range _ _ _ _ _ Input) (entry_text _ _ _ _ _ Input)
         Sep N Idx Post) as [exit [Path [_ Branch]]].
       cbn [LinkedRun.bind fst snd FirstDispatch.continue];rewrite FilterRun;cbn [LinkedRun.bind];rewrite Path.
       assert (Eq:StrictReturn.live e (LinkedRun.machine v) <-> HashLayout.active Dalek e).
       { split;intros [j [J H]];exists j;split;[exact J|apply (proj1(StrictReturn.strong_lane _ _ _ _ Post j J)),H|
          exact J|apply (proj2(StrictReturn.strong_lane _ _ _ _ Post j J)),H]. }
       destruct exit as [r|h];cbn [FirstDispatch.after_filter LinkedRun.bind] in *;destruct Branch as [Survives ChildRun].
       -- exists (FirstDispatch.after_reject r);split;[reflexivity|apply after_reject;[|tauto|exact ChildRun]].
          intros j J In Sig;apply Survives,Eq;exists j;split;[exact J|].
          apply Lane.accepted_eligible;unfold HashLayout.row;rewrite TailCopy.own_row by exact In;exact Sig.
       -- assert (LiveDalek:=proj1 Eq Survives).
          destruct(NativeHash.checked Dalek _ _ _ _ _ Place Loaded N Entries Borrow LiveDalek (HashLayout.strict_flags _ _ _ _ Post)
            (StrictReturn.encodings _ _ _ _ Post) ChildRun) as [r [HashRun HashPost]].
          eexists;split;[unfold FirstDispatch.hash_return;now rewrite HashRun|exact (conj LiveDalek (conj HashPost (conj (ScoreInputs.at_hash _ _ _ _ _ _ Place (ScoreInputs.dalek _ _ _ _ Post) ChildRun) (HashEntry.words _ _ _ _ _ ChildRun))))].
Qed.

Lemma rejected_return pol bias pc text e q : admissible pol bias pc text e -> (0<count e)%nat ->
 RejectExecution.post (bias+pc) e (RejectExecution.BatchReturned q) -> rejected_inputs pol e -> returned pol e (LinkedRun.ip q) (LinkedRun.machine q).
Proof.
 intros Caller Live Done Invalid;destruct Done as [Paid [[Status Outputs] [Bytes [Size [PC [SP Saved]]]]]].
 destruct(batch_inputs _ _ _ _ _ Caller Live) as [_ [_ [_ [_ [Idx _]]]]].
 unfold returned;repeat apply conj;try assumption.
 - intros x Outside;rewrite (proj2 Paid);apply (WriteTrace.frame _ _ (proj1 Paid)),Outside.
 - intros j J;destruct(indices_cover e Idx j J) as [i [I <-]];left;apply Outputs;lia.
 - intros i I;exists false;split;[apply Outputs;lia|split;[discriminate|intro A;exfalso;exact (Invalid i ltac:(lia) I A)]].
Qed.

Lemma rejected_verdict pol bias pc text e q : admissible pol bias pc text e -> (0<count e)%nat ->
 at_boundary pol bias pc e (FirstDispatch.Completed q) -> returned pol e (LinkedRun.ip q) (LinkedRun.machine q).
Proof. intros A N [Post [Invalid _]];exact (rejected_return _ _ _ _ _ _ A N Post Invalid). Qed.

Corollary single_policy_rejection pol pc text : batch_contract pol pc text ->
 forall bias e cf masks,admissible pol bias pc text e -> (0<count e<=8)%nat -> ~HashLayout.active pol e ->
 exists q,FirstDispatch.run pol bias pc text e cf masks=Some(FirstDispatch.Completed q) /\
 returned pol e (LinkedRun.ip q) (LinkedRun.machine q) /\ LinkedRun.accounted e (writable e) q /\
 forall i,(i<count e)%nat -> mem(LinkedRun.machine q)(output e+Z.of_nat(position e i))=0.
Proof.
 intros Main bias e cf masks A [N Size] Bad.
 destruct(dispatch_correct _ _ _ _ _ _ _ A (dispatch_code _ _ _ Main) N (machine_scalar_return _ _ _ Main _ _ cf masks A N))
    as [[q|q|q r] [Run Done]].
 - exists q;split;[exact Run|split;[exact (rejected_verdict _ _ _ _ _ _ A N Done)|]].
   destruct Done as [[Paid [[_ Zeros] _]] _];split;[exact Paid|intros i I;apply Zeros;lia].
 - destruct Done as [[_ [_ [_ [More _]]]] _];lia.
 - exfalso;apply Bad,(proj1 Done).
Qed.
Corollary single_ineligible_return pol pc text : batch_contract pol pc text ->
 forall bias e cf masks,admissible pol bias pc text e -> (0<count e<=8)%nat ->
 (forall j,(j<8)%nat -> ~EligibleLanes.candidate e j) ->
 exists q,FirstDispatch.run pol bias pc text e cf masks=Some(FirstDispatch.Completed q) /\
 returned pol e (LinkedRun.ip q) (LinkedRun.machine q) /\ LinkedRun.accounted e (writable e) q /\
 forall i,(i<count e)%nat -> mem(LinkedRun.machine q)(output e+Z.of_nat(position e i))=0.
Proof.
 intros Main bias e cf masks A Size Bad;apply single_policy_rejection;try assumption.
 intros [j [J H]];apply (Bad j J),(HashLayout.candidate_of _ _ _ H).
Qed.

Corollary eligible_hash_returns pol pc text : batch_contract pol pc text ->
 forall bias e c masks,admissible pol bias pc text e -> (0<count e)%nat -> HashLayout.active pol e ->
 exists q r,FirstDispatch.run pol bias pc text e c masks=Some(FirstDispatch.HashReturned q r) /\
   NativeHash.returned pol bias (bias+pc) e q r.
Proof.
 intros Main bias e c masks A N Live.
 destruct(dispatch_correct _ _ _ _ _ _ _ A (dispatch_code _ _ _ Main) N (machine_scalar_return _ _ _ Main _ _ c masks A N))
   as [[q|q|q r] [Run T]].
 - destruct T as [_ [_ None]];contradiction.
 - destruct T as [_ None];contradiction.
 - exists q,r;exact (conj Run (proj1(proj2 T))).
Qed.

Corollary eligible_zip_hash_returns pc text : batch_contract Zip215 pc text ->
 forall bias e c masks,admissible Zip215 bias pc text e -> (0<count e)%nat -> active_chunk e ->
 exists q r,FirstDispatch.run Zip215 bias pc text e c masks=Some(FirstDispatch.HashReturned q r) /\
   NativeHash.returned Zip215 bias (bias+pc) e q r.
Proof.
 intros Main bias e c masks A N [j [J On]];apply eligible_hash_returns;try assumption.
 exists j;split;[exact J|now apply HashLayout.candidate].
Qed.

Lemma score_handoff pol bias pc text e q r s c : admissible pol bias pc text e -> (0<count e)%nat ->
 ScoreSetup.bound pol pc text -> at_boundary pol bias pc e (FirstDispatch.HashReturned q r) ->
 HashResume.compatible r s -> well_formed s -> exists child,ScoreCall.execute bias pc text q r s c=Some child /\
   ScoreCall.entered pol bias pc e q r child.
Proof.
 intros A N Code [_ [R [Inputs _]]] C W;destruct(batch_inputs _ _ _ _ _ A N) as [P [_ [[_ Sep] _]]].
 apply ScoreCall.checked;[exact Code|exact P|exact (callee_image _ _ _ _ _ A N)|exact (entry_range _ _ _ _ _ A)|
   exact (entry_text _ _ _ _ _ A)|exact Sep|exact Inputs|exact R|exact C|exact W].
Qed.

Lemma ladder_geometry pol bias pc text e : admissible pol bias pc text e -> (0<count e)%nat ->
 ProductRun.geometry (HashLayout.chunk pol e bias).
Proof.
 intros A N;destruct(batch_inputs _ _ _ _ _ A N) as [_ [_ [_ [_ [_ Entries]]]]].
 exact (proj2(proj2(proj2(proj2(Entries 0%nat (count e) zero_loc N eq_refl zero_words))))).
Qed.

Lemma scoring_context pol bias pc text e c masks stop : admissible pol bias pc text e -> (0<count e)%nat ->
 StrictDispatch.bound pc text -> ScoreSetup.bound pol pc text -> first_chunk pol bias pc text e c masks ->
 scoring pol bias pc text e c masks stop ->
 exists q r child score,HashLayout.active pol e /\ ScoreStart.reached pol bias pc e q r child score /\
 ScoreProgress.observed pol bias score stop.
Proof.
 intros A N Hash Scorer Native [q [r [s [cf [child [score [Run [C [W [Call [Start Progress]]]]]]]]]]].
 destruct(dispatch_correct _ _ _ _ _ _ _ A Hash N Native) as [b [At B]];rewrite Run in At;injection At as <-.
 destruct(score_handoff _ _ _ _ _ _ _ _ cf A N Scorer B C W) as [v [V E]];rewrite Call in V;injection V as <-.
 destruct(ScoreStart.from_entry _ _ _ _ _ _ _ (proj1(batch_inputs _ _ _ _ _ A N)) (callee_image _ _ _ _ _ A N) E)
    as [v [V Ready]];rewrite Start in V;injection V as <-;exists q,r,child,score;exact (conj (proj1 B) (conj Ready Progress)).
Qed.

Lemma scored_rejection pol bias pc text e c masks stop :
 matches pc (destination pol) text -> admissible pol bias pc text e -> (0<count e)%nat ->
 StrictDispatch.bound pc text -> ScoreSetup.bound pol pc text -> first_chunk pol bias pc text e c masks ->
 scoring pol bias pc text e c masks stop -> scorer_rejected pol stop=true ->
 exists v,ScorePublish.execute bias pc text stop=Some v /\ RejectExecution.post (bias+pc) e v /\ rejected_inputs pol e.
Proof.
 intros M A N Hash Scorer Native Scored Zero;destruct pol;[discriminate|].
 change ((regs(LinkedRun.machine stop) 12%nat=?0)=true) in Zero;apply Z.eqb_eq in Zero.
 destruct(scoring_context _ _ _ _ _ _ _ _ A N Hash Scorer Native Scored) as [q [r [caller [score [Live [Ready Run]]]]]].
 destruct(batch_inputs _ _ _ _ _ A N) as [P [_ [[_ Sep] [_ [Idx _]]]]];pose proof(callee_image _ _ _ _ _ A N) as I.
 destruct(proj2(StrictScreen.with_frame _ _ _ _ _ _ _ P I Live Ready) _ Run) as [D F].
 destruct(ScorePublish.checked _ _ _ _ _ _ _ M Hash P I (entry_range _ _ _ _ _ A) (entry_text _ _ _ _ _ A) Sep N Idx D F Zero)
     as [v [End Post]];exists v;split;[exact End|split;[exact Post|]].
 intros j J Row Sig;pose proof(StrictScreen.lane _ _ _ D j J) as B;rewrite Zero,Z.bits_0 in B.
 enough (On:StrictOrderClear.eligible e j) by (apply (proj2 B) in On;discriminate).
 apply StrictAccept.screened;unfold HashLayout.row;now rewrite TailCopy.own_row by exact Row.
Qed.

Lemma observed_correct pol pc text bias e carry masks :
 matches pc (destination pol) text -> StrictDispatch.bound pc text -> ScoreSetup.bound pol pc text -> admissible pol bias pc text e ->
 (count e=0%nat -> empty_mapped (bias+pc) text e) ->
 ((0<count e)%nat -> first_chunk pol bias pc text e carry masks) ->
 (exists ws ip final,observation pol bias pc text e carry masks ws ip final) /\
 (forall ws ip final,observation pol bias pc text e carry masks ws ip final ->
    returned pol e ip final /\ WriteTrace.confined (writable e) ws).
Proof.
 intros Image Hash Scorer Caller Empty Batch;destruct (grouped _ _ _ Image _ _ Caller) as [Exists Sound].
 assert (Dispatch:forall b,(0<count e)%nat -> FirstDispatch.run pol bias pc text e carry masks=Some b -> at_boundary pol bias pc e b).
 { intros b N Run;destruct(dispatch_correct _ _ _ _ _ _ _ Caller Hash N (Batch N)) as [v [Eq Post]];rewrite Run in Eq;now injection Eq as <-. }
 split.
 - destruct (Nat.eqb_spec (count e) 0) as [Z|Live].
   + specialize (Empty Z);unfold empty_mapped in Empty;destruct(empty_return e) as [ip f].
     exists nil,ip,f;apply observe_empty;[exact Z|exact (proj1 (Empty carry))].
   + assert (N:(0<count e)%nat) by lia. destruct(dispatch_correct _ _ _ _ _ _ _ Caller Hash N (Batch N)) as [[q|q|q r] [Run Post]].
     * do 3 eexists;exact (observe_rejected _ _ _ _ _ _ _ q N Run).
     * destruct Exists as [ip [f R]];do 3 eexists;eapply observe_next;[exact N|exact Run|exact R].
     * pose proof(proj1(batch_inputs _ _ _ _ _ Caller N)) as P.
       destruct(HashResume.complete_ok _ _ _ _ _ _ e P (proj2(proj2(proj2 Post))) (initial_cpu _ P) (proj1(proj2 Post))) as [C W].
       destruct(score_handoff _ _ _ _ _ _ _ _ carry Caller N Scorer Post C W) as [child [Call Enter]].
       destruct(ScoreStart.from_entry _ _ _ _ _ _ _ P (callee_image _ _ _ _ _ Caller N) Enter) as [score [Start Ready]].
       destruct (proj1 (ScoreProgress.checked _ _ _ _ _ _ _ _ P (callee_image _ _ _ _ _ Caller N) (ladder_geometry _ _ _ _ _ Caller N) (proj1 Post) Ready)) as [stop Progress].
       assert (Scored:scoring pol bias pc text e carry masks stop).
       { exists q,r,(HashResume.complete r e),carry,child,score;split;[exact Run|split;[exact C|split;[exact W|split;[exact Call|split;[exact Start|exact Progress]]]]]. }
       destruct(scorer_rejected pol stop) eqn:Zero.
       -- destruct(scored_rejection _ _ _ _ _ _ _ _ Image Caller N Hash Scorer (Batch N) Scored Zero) as [[last|last] [End _]].
          ++ do 3 eexists;eapply observe_scored_return;eassumption.
          ++ destruct Exists as [ip [f R]];do 3 eexists;eapply observe_scored_next;eassumption.
       -- destruct Exists as [ip [f R]];do 3 eexists;eapply observe_scoring;eassumption.
 - intros ws ip f O;inversion O as [ws' ip' f' Z Run|q N Run|q ip' f' N Next R|
     stop q N Scored Zero End|stop q ip' f' N Scored Zero End R|stop ip' f' N Scored Pending R];subst.
   + specialize (Empty Z);unfold empty_mapped in Empty;destruct(empty_return e) as [back last] eqn:E.
     destruct (proj2 (Empty carry) _ _ Run) as [-> Same].
     inversion Same as [|s t u own rest Impossible];[|discriminate].
     subst;split;[apply Sound,empty_path;[exact Image|now rewrite Z|exact E]|constructor].
   + pose proof(Dispatch _ N Run) as T;split;[exact (rejected_verdict _ _ _ _ _ _ Caller N T)|exact (proj1(proj1(proj1 T)))].
   + split;[exact (Sound _ _ R)|exact (proj1(proj1(proj1(Dispatch _ N Next))))].
   + destruct(scored_rejection _ _ _ _ _ _ _ _ Image Caller N Hash Scorer (Batch N) Scored Zero) as [v [Done [Post Invalid]]].
     rewrite End in Done;injection Done as <-;split;[eapply rejected_return;eassumption|exact (proj1(proj1 Post))].
   + destruct(scored_rejection _ _ _ _ _ _ _ _ Image Caller N Hash Scorer (Batch N) Scored Zero) as [v [Done [Post Invalid]]].
     rewrite End in Done;injection Done as <-;split;[exact (Sound _ _ R)|exact (proj1(proj1 Post))].
   + destruct(scoring_context _ _ _ _ _ _ _ _ Caller N Hash Scorer (Batch N) Scored) as [q [r [child [score [Live [Ready Progress]]]]]].
     split;[exact (Sound _ _ R)|exact (proj1 (proj2 (ScoreProgress.checked _ _ _ _ _ _ _ _ (proj1(batch_inputs _ _ _ _ _ Caller N))
       (callee_image _ _ _ _ _ Caller N) (ladder_geometry _ _ _ _ _ Caller N) Live Ready) _ Progress))].
Qed.

Lemma scorer_verdict_checked pol bias pc text e c masks stop : admissible pol bias pc text e -> (0<count e)%nat ->
 StrictDispatch.bound pc text -> ScoreSetup.bound pol pc text -> first_chunk pol bias pc text e c masks ->
 scoring pol bias pc text e c masks stop -> scorer_result pol bias e stop.
Proof.
 intros A N Hash Scorer Native Scored.
 destruct(scoring_context _ _ _ _ _ _ _ _ A N Hash Scorer Native Scored) as [q [r [child [score [Live [Ready Progress]]]]]].
 destruct(batch_inputs _ _ _ _ _ A N) as [P [_ [_ [Maps _]]]];pose proof(callee_image _ _ _ _ _ A N) as I.
 destruct pol.
 - pose proof(ladder_geometry _ _ _ _ _ A N) as G.
   destruct(proj2(ScoreProgress.zip _ _ _ _ _ _ _ P I G Ready) _ Progress) as [mid [ladder [L Stage]]].
   exists ladder;split;[exact Stage|split;[exact (proj2(proj2(proj2(LadderStage.checked _ _ _ _ _ I G L) _ Stage)))|]].
   eapply LadderProduct.checked;[exact I|exact Maps|exact (Tables.loaded _ _ static_tables_correct Maps)|exact G|exact L].
 - exact (proj2(StrictScreen.checked _ _ _ _ _ _ _ P I Live Ready) _ Progress).
Qed.

Lemma verified pol pc text : matches pc (destination pol) text -> empty_image text -> Prologue.bound text -> StageEntry.bound text -> TailWrites.bound text -> StageWrites.bound text (destination pol Prepare-pc) -> RejectCall.bound pc text -> RejectDispatch.bound pc text -> RejectFinish.bound text -> StageEntry.preserves_bp text=true -> HashEntry.bound pc text -> ScoreSetup.bound pol pc text ->
 batch_contract pol pc text.
Proof.
 intros Image Bytes Setup Select Pad Transfer Rejection ScatterCode ExitCode RBP Hash Scorer.
 assert (Empty:forall bias e,admissible pol bias pc text e -> count e=0%nat ->
   empty_mapped (bias+pc) text e).
 { intros bias e Input Z;apply mapped_return;[exact (entry_text _ _ _ _ _ Input)|].
   apply empty_path_writes;[exact Bytes|exact (cpu_words _ _ _ _ _ Input)|exact Z]. }
 assert (Live:forall bias e,admissible pol bias pc text e -> (0<count e)%nat ->
   StageEntry.physical (bias+pc) text (destination pol Prepare-pc) e).
 { intros bias e Input N;destruct (batch_inputs _ _ _ _ _ Input N) as [P [[Rows _] [[_ Apart] _]]].
   destruct Rows as [Fit Const].
   apply StageEntry.from_entry;[exact Setup|exact Select|exact Pad|exact Transfer|exact RBP|exact P|exact N|exact Fit|exact Const|
     exact (entry_text _ _ _ _ _ Input)|exact Apart]. }
 assert (Native:forall bias e c masks,admissible pol bias pc text e -> (0<count e)%nat ->
     first_chunk pol bias pc text e c masks).
 { intros bias e c masks Input N.
   destruct (scalar_from_entry _ _ _ _ _ c masks Input N (Live _ _ Input N)) as [stop [Run Post]].
   exists stop;split;[exact Run|split;[exact Post|]].
   destruct (batch_inputs _ _ _ _ _ Input N) as [P [[_ Inputs] [[_ Apart] [_ [Indices _]]]]].
   pose proof(callee_image _ _ _ _ _ Input N) as Loaded.

   assert (Data:ScalarInputs.recoded e (LinkedRun.machine stop) /\ ScalarInputs.copy_ready e (LinkedRun.machine stop) /\ StageEntry.metadata e (mem(LinkedRun.machine stop)) /\ StageEntry.saved_caller e (LinkedRun.machine stop)).
   { destruct Post as [_ [_ [_ [_ [_ Contract]]]]]. apply Contract;[exact N|].
     intros j J;exact (proj1 (proj2 (Inputs j J))). }
   assert (Layout:WrapperInputs.layout e (mem(LinkedRun.machine stop))) by
      (destruct Data as [_ [[_ [_ [_ [_ [_ [_ Layout]]]]]] _]];exact Layout).
   assert (Exit:forall decoded p,EligibilityFrame.context pol bias (bias+pc) e p ->
     LinkedRun.accounted e (writable e) p -> byte_memory(mem(LinkedRun.machine p)) ->
     regs(LinkedRun.machine p) 4%nat=BatchScalar.common_top pol e-104 -> LinkedRun.ip p=bias+PrepareNative.common+PrepareUnwind.unwind_offset decoded ->
     PrepareUnwind.return_value decoded (LinkedRun.machine p) mod 2^32=0 ->
     exists r,RejectedPath.execute decoded pol bias pc text p=Some r /\ RejectExecution.post (bias+pc) e r).
   { intros dec p;apply RejectedPath.checked;[exact ScatterCode|exact ExitCode|exact P|exact Loaded|exact (entry_range _ _ _ _ _ Input)|
       exact (proj1(proj2(proj2(proj2 Rejection))))|exact (entry_text _ _ _ _ _ Input)|exact Apart|exact N|exact Indices]. }
   split;[exact (proj1 Data)|]. split.
   { intro Nonzero;destruct (BatchDecode.from_scalar pol bias pc text e c masks stop) as [d [Trace [Entry CallerRegs]]];
       [exact P|exact (callee_image _ _ _ _ _ Input N)| |exact Run|exact Post|exact (proj1(proj2 Data))|exact Nonzero|].
     2:{ exists d;split;[exact Trace|split;[exact Entry|split;[exact CallerRegs|]]].
         destruct(BatchScalar.has_masks _ _ _ _ _ _ _ _ Run) as [bank Bank].
         pose proof(NativeWords.decoder_entry _ _ _ _ _ _ _ _ _ (initial_cpu _ P) Run (proj1(proj1(proj2 Data))) Trace) as Words.
         destruct(EligibleLanes.from_decoder _ _ _ stop d bank P (callee_image _ _ _ _ _ Input N)
            (decoder_aligned _ _ _ _ _ Input N) Entry Words (proj1 Data) (BatchDecode.caller_args _ _ _ _ CallerRegs)) as [r [R Check]].
         exists bank,r;split;[exact Bank|split;[exact R|split;[exact Check|]]].
         pose proof(EligibilityFrame.restore _ _ _ _ _ _ _ P Post CallerRegs (proj1(proj2(proj2 Data))) (proj2(proj2(proj2 Data))) Layout Check) as Frame.
         split;[exact Frame|intro Zero;apply Exit].
         - exact Frame.
         - exact (EligibleLanes.writes _ _ _ _ _ (proj2 Check)).
         - exact (proj2(proj2(EligibleLanes.words _ _ _ _ _ (proj2 Check)))).
         - exact (EligibleLanes.stack _ _ _ _ _ (proj2 Check)).
         - rewrite (EligibleLanes.destination _ _ _ _ _ (proj2 Check));unfold EligibleLanes.next;now rewrite Zero.
         - reflexivity. }
     intros j sig J;destruct (Inputs _ (TailCopy.live_row e j N)) as [Key [Sig Msg]].
     unfold ScalarInputs.encoding_ptr;destruct sig;[|exact Key]. destruct Sig as [[Low High] Away].
     split;[unfold fits64;split;[exact Low|lia]|intros x X;apply Away;lia]. }
   intro Zero;split;[exact (ScalarInputs.zero_rejects pol e _ (proj1 Data) Zero)|].
   destruct Post as [PC [SP [Acc [Links [Outputs _]]]]].
   destruct(Exit false stop (EligibilityFrame.Context _ _ _ _ _ Links Outputs (proj1(proj2(proj2 Data))) (proj2(proj2(proj2 Data))) Layout)
      Acc (proj1(proj1(proj2 Data))) SP PC Zero) as [r [End Result]].
   exists r;split;[unfold RejectExecution.scalar_rejection;rewrite Run;cbn [LinkedRun.bind];rewrite Zero,Z.eqb_refl;exact End|exact Result]. }
 assert (CallerCode:StrictDispatch.bound pc text) by
   (exact (conj Hash (conj ScatterCode (conj ExitCode (proj1(proj2(proj2(proj2 Rejection)))))))).
 constructor;[exact Image|exact Arguments.checked_arguments|exact static_tables_correct|
 exact (linked_calls pol)|exact (conj CallWrites.embedded (conj NestedRegions.embedded protected_slots))| | |exact CallerCode|exact Scorer| | | |].
 - intros bias e carry masks Input;eapply observed_correct;[exact Image|exact CallerCode|exact Scorer|exact Input|apply Empty|apply Native];exact Input.
 - intros bias e Input;split.
   + intros ip final N Run x X.
     destruct (proj2 (grouped _ _ _ Image _ _ Input) _ _ Run) as [_ [_ [_ [_ [F _]]]]].
     apply F,(LoadedImage.immutable _ _ _ _ (callee_image _ _ _ _ _ Input N)),X.
   + intro N;split.
     * intros prior s carry ws last Past Current D L Run.
       pose proof(LoadedImage.after _ _ _ _ _ (callee_image _ _ _ _ _ Input N) Past) as Loaded.
       rewrite <-Current in Loaded.
       pose proof(LoadedImage.scatter pol) as I.
       destruct (LoadedImage.symbols _ _ _ _ Loaded _ _ I) as [_ Map].
       destruct (batch_inputs _ _ _ _ _ Input N) as [Place _].
       assert (Apart:forall x,
         LoadedImage.extent bias Zip215.ScatterBytes.address (Z.of_nat(length Zip215.ScatterBytes.symbol_bytes)) x ->
         ~Return.span (output e) (Z.of_nat(count e)) x).
       { intros x X InOut. apply (LoadedImage.immutable _ _ _ _ Loaded x);
         [left;eexists _,_;split;[exact I|exact X]|right;right;exact InOut]. }
       destruct (CallWrites.scatter_stores CallWrites.embedded _ _ _ _ _ _ Place D L Map Apart Run) as [W Replay].
       split;[exact W|rewrite Replay;apply LoadedImage.after;[exact Loaded|]].
       exact (TracedCalls.lend _ _ _ (nested_in_root _) W).
     * destruct (batch_inputs _ _ _ _ _ Input N) as [Place [_ [[_ Apart] _]]].
       apply RejectCall.checked with (mode:=pol);
         [exact Rejection|exact Place|exact (entry_range _ _ _ _ _ Input)|
          exact (entry_text _ _ _ _ _ Input)|exact Apart|exact (callee_image _ _ _ _ _ Input N)].
 - exact Live.
 - exact Native.
 - intros bias e c masks stop A N Run;eapply scorer_verdict_checked;[exact A|exact N|exact CallerCode|exact Scorer|apply Native|exact Run];assumption.
 - intros bias e Input Z. destruct (empty_return e) as [ip final] eqn:E. split.
   + apply (proj2 (grouped _ _ _ Image _ _ Input)),empty_path;[exact Image|now rewrite Z|exact E].
   + exact (Empty _ _ Input Z).
Qed.

Theorem assembled_zip215_verify_batch_correct :
 batch_contract Zip215 ZipBytes.address ZipBytes.symbol_bytes.
Proof. apply verified;[vm_compute;split;reflexivity|vm_compute;repeat split;reflexivity|repeat constructor|repeat constructor|repeat constructor|vm_compute;repeat split;reflexivity|vm_compute;repeat split;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|vm_compute;reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity]. Qed.

Theorem assembled_dalek_verify_batch_correct :
 batch_contract Dalek DalekBytes.address DalekBytes.symbol_bytes.
Proof. apply verified;[vm_compute;split;reflexivity|vm_compute;repeat split;reflexivity|repeat constructor|repeat constructor|repeat constructor|vm_compute;repeat split;reflexivity|vm_compute;repeat split;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|vm_compute;reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity]. Qed.
