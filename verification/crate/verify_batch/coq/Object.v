From Coq Require Import List ZArith Lia.
From Machine Require execution.Composition.
From Machine Require Import execution.LinkedCalls memory.FlatMemory memory.ByteMemory memory.MemoryGeometry.
From Ed25519Simd.PrepareChunk Require Object.
From Ed25519Simd.Sha512Challenge Require Object.
From Ed25519Simd.Zip215 Require Object.
From Ed25519Simd.DalekPostHash Require Object.
From Ed25519Simd.VerifyBatch Require Import Policy Image Control Scatter Loop Return LoadedImage EntryWrites CallWrites NestedRegions Prologue StageEntry RejectCall Audit TableCertificate ZipBytes DalekBytes.
From Ed25519Simd.VerifyBatch Require StrictAccept ChunkRestart ChunkStaging ChunkScalar ChunkScreen ChunkDispatch NativeLoop.
Local Open Scope Z_scope.

Lemma linked_calls pol : callees pol.
Proof.
 split;[exact PrepareChunk.Object.assembled_prepare_chunk_correct|].
 split;[exact Sha512Challenge.Object.assembled_sha512_challenge_correct|].
 destruct pol;[exact Zip215.Object.assembled_zip215_correct|].
 split;[exact DalekPostHash.Object.assembled_dalek_post_hash_correct|].
 vm_compute;split;reflexivity.
Qed.

Lemma empty_correct pol bias pc text e ip final:admissible pol bias pc text e -> count e=0%nat ->
 empty_return e=(ip,final) -> returned pol e ip final /\ effects e nil final.
Proof.
 intros A N E;pose proof(Return.empty e (cpu_words _ _ _ _ _ A) (caller_sp _ _ _ _ _ A)) as ABI;rewrite E in ABI.
 destruct ABI as [PC [OK [SP [G M]]]];split.
 - unfold returned;repeat apply conj;try assumption.
   + intros x _;now rewrite M.
   + rewrite M;apply (cpu_words _ _ _ _ _ A).
   + intros j J;lia.
   + intros i I;lia.
 - split;[constructor|intros x;now rewrite M].
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

Definition active_chunk e:=exists j,(j<8)%nat /\ EligibleLanes.candidate e j.

Lemma dispatch_correct pol bias pc text e c ks : admissible pol bias pc text e -> StrictDispatch.bound pc text -> (0<count e)%nat ->
 first_chunk pol bias pc text e c ks ->
 Composition.ensures (Composition.output (FirstDispatch.run pol bias pc text e c ks)) (@ChunkDispatch.post BatchWindow.initial pol bias pc e).
Proof.
 intros A Code N [s [Run [Post _]]].
 destruct (ChunkScalar.first_execution _ _ _ _ _ _ _ _ Run) as [p [bank [Stage [Scalar [_ Words]]]]].
 specialize (Words (cpu_words _ _ _ _ _ A)).
 unfold FirstDispatch.run,FirstDispatch.dispatch;rewrite Stage;cbn [LinkedRun.bind];rewrite Scalar;cbn [LinkedRun.bind].
 exact (@ChunkDispatch.from_scalar BatchWindow.initial pol bias pc text e s bank A Code N Post Words).
Qed.

Lemma native_verdict pol e q:indices e -> Iteration.exit e q ->
 NativeLoop.prefix_at pol e (count e) (mem(LinkedRun.machine q)) ->
 returned pol e (LinkedRun.ip q) (LinkedRun.machine q) /\ effects e (LinkedRun.log q) (LinkedRun.machine q).
Proof.
 intros Idx [Paid [Bytes [OK [PC [SP G]]]]] Prefix;split;[|exact Paid].
 unfold returned;split;[exact PC|split;[exact OK|split;[exact SP|split;[exact G|]]]].
 split;[intros x X;rewrite (proj2 Paid);apply (WriteTrace.frame _ _ (proj1 Paid)),X|].
 split;[exact Bytes|split;[|exact Prefix]].
 intros j J;destruct(indices_cover e Idx j J) as [i [I <-]];destruct(Prefix i I) as [[] [V _]];cbn in V;auto.
Qed.

Lemma rejected_verdict pol bias pc text e q : admissible pol bias pc text e -> (0<count e)%nat ->
 @ChunkDispatch.post BatchWindow.initial pol bias pc e (FirstDispatch.Completed q) ->
 returned pol e (LinkedRun.ip q) (LinkedRun.machine q).
Proof.
 intros Caller Live [None Done].
 destruct (@ChunkDispatch.rejected_outputs BatchWindow.initial pol bias pc e _ None Done)
   as [Paid [[Status Outputs] [Bytes [Size [PC [SP Saved]]]]]].
 destruct(batch_inputs _ _ _ _ _ Caller Live) as [_ [_ [_ [_ [Idx _]]]]].
 assert (Prefix:NativeLoop.prefix_at pol e (count e) (mem(LinkedRun.machine q))).
 { intros i I;apply (Outputs i);change (count e<=8)%nat in Size;change (i<Nat.min (count e) 8)%nat;lia. }
 exact (proj1 (native_verdict pol e q Idx (conj Paid (conj Bytes (conj Status (conj PC (conj SP Saved))))) Prefix)).
Qed.

Corollary single_policy_rejection pol pc text : batch_contract pol pc text ->
 forall bias e cf masks,admissible pol bias pc text e -> (0<count e<=8)%nat -> ~HashLayout.active pol e ->
 exists q,FirstDispatch.run pol bias pc text e cf masks=Some(FirstDispatch.Completed q) /\
 returned pol e (LinkedRun.ip q) (LinkedRun.machine q) /\ LinkedRun.accounted e (writable e) q /\
 forall i,(i<count e)%nat -> mem(LinkedRun.machine q)(output e+Z.of_nat(position e i))=0.
Proof.
 intros Main bias e cf masks A [N Size] Bad.
 destruct(dispatch_correct _ _ _ _ _ _ _ A (dispatch_code _ _ _ Main) N (machine_scalar_return _ _ _ Main _ _ cf masks A N))
    as [[b Run] All]. specialize (All b Run) as Done; destruct b as [q|q|q r].
 - exists q;split;[exact Run|split;[exact (rejected_verdict _ _ _ _ _ _ A N Done)|]].
   destruct Done as [_ [Paid [[_ Zeros] _]]];split;[exact Paid|intros i I;apply Zeros;change (i<Nat.min (count e) 8)%nat;lia].
 - destruct Done as [_ [_ [_ [_ [More _]]]]];change (8<count e)%nat in More;lia.
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
   as [[b Run] All]. specialize (All b Run) as T; destruct b as [q|q|q r].
 1,2: exfalso;exact ((proj1 T) Live).
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

Lemma ladder_geometry pol bias pc text e : admissible pol bias pc text e -> (0<count e)%nat ->
 ProductRun.geometry (HashLayout.chunk pol e bias).
Proof.
 intros A N;destruct(batch_inputs _ _ _ _ _ A N) as [_ [_ [_ [_ [_ Entries]]]]].
 exact (proj2(proj2(proj2(Entries 0%nat (count e) N eq_refl)))).
Qed.

Lemma scoring_context pol bias pc text e c masks stop : admissible pol bias pc text e -> (0<count e)%nat ->
 StrictDispatch.bound pc text -> ScoreSetup.bound pol pc text -> first_chunk pol bias pc text e c masks ->
 scoring pol bias pc text e c masks stop ->
 exists q r child score,HashLayout.active pol e /\ ScoreStart.reached pol bias pc e q r child score /\
 ScoreProgress.observed pol bias score stop.
Proof.
 intros A N Hash Scorer Native [q [r [score [Run [Start Progress]]]]].
 destruct (proj2 (dispatch_correct _ _ _ _ _ _ _ A Hash N Native) _ Run) as [Live [Ret [Inputs Words]]].
 destruct(batch_inputs _ _ _ _ _ A N) as [P [_ [[Range Sep] _]]].
 pose proof (ScoreStart.from_hash_checked _ _ _ _ _ _ _ Scorer P (callee_image _ _ _ _ _ A N)
   Range (entry_text _ _ _ _ _ A) Sep Inputs Ret Words) as Path.
 destruct (proj2 Path score Start) as [child Ready].
 exists q,r,child,score;auto.
Qed.

Lemma scorer_verdict_checked pol bias pc text e c masks stop : admissible pol bias pc text e -> (0<count e)%nat ->
 StrictDispatch.bound pc text -> ScoreSetup.bound pol pc text -> first_chunk pol bias pc text e c masks ->
 scoring pol bias pc text e c masks stop -> scorer_result pol bias pc e stop.
Proof.
 intros A N Hash Scorer Native Scored.
 destruct(scoring_context _ _ _ _ _ _ _ _ A N Hash Scorer Native Scored) as [q [r [child [score [Live [Ready Progress]]]]]].
 destruct(batch_inputs _ _ _ _ _ A N) as [P [_ [_ [Maps _]]]];pose proof(callee_image _ _ _ _ _ A N) as I.
 split.
 - destruct pol;[exact Logic.I|exact (proj2(StrictScreen.checked _ _ _ _ _ _ _ P I Live Ready) _ Progress)].
 - apply (ScoreDecision.checked _ _ _ _ _ _ _ _ _ P I (ladder_geometry _ _ _ _ _ A N)
      Maps (Tables.loaded _ _ static_tables_correct Maps) Live Ready Progress).
Qed.

Lemma observed_correct pol pc text bias e carry masks :
 matches pc (destination pol) text -> StrictDispatch.bound pc text -> ScoreSetup.bound pol pc text ->
 ChunkRestart.code text (destination pol Prepare-pc) -> admissible pol bias pc text e ->
 (count e=0%nat -> empty_mapped (bias+pc) text e) ->
 ((0<count e)%nat -> StageEntry.physical (bias+pc) text (destination pol Prepare-pc) e) ->
 (exists ws ip final,observation pol bias pc text e carry masks ws ip final) /\
 (forall ws ip final,observation pol bias pc text e carry masks ws ip final ->
    returned pol e ip final /\ effects e ws final).
Proof.
 intros Image Dispatch Score Restart Caller Empty Live;split.
 - destruct(Nat.eqb_spec (count e) 0) as [Z|NZ].
   + specialize(Empty Z);unfold empty_mapped in Empty;destruct(empty_return e) as [ip s].
     exists nil,ip,s;apply observe_empty;[exact Z|exact(proj1(Empty carry))].
   + assert(N:(0<count e)%nat) by lia.
     destruct(proj1(NativeLoop.checked_verdicts _ _ _ _ _ Caller Image Dispatch Score Restart carry masks N (Live N))) as [q Run].
     do 3 eexists;exact (observe_native _ _ _ _ _ _ _ q N Run).
 - intros ws ip s O;inversion O as [ws' ip' s' Z Run|q N Run];subst.
   + specialize(Empty Z);unfold empty_mapped in Empty;destruct(empty_return e) as [back final] eqn:E.
     destruct(proj2(Empty carry) _ _ Run) as [-> Same].
     inversion Same as [|u v t pre rest Impossible];[|discriminate];subst.
     exact(empty_correct _ _ _ _ _ _ _ Caller Z E).
   + destruct(proj2(NativeLoop.checked_verdicts _ _ _ _ _ Caller Image Dispatch Score Restart carry masks N (Live N)) _ Run)
       as [Exit Prefix].
     destruct(batch_inputs _ _ _ _ _ Caller N) as [_ [_ [_ [_ [Idx _]]]]].
     exact (native_verdict pol e q Idx Exit Prefix).
Qed.

Lemma verified pol pc text : matches pc (destination pol) text -> empty_image text -> Prologue.bound text -> ChunkRows.Selection.bound text -> TailWrites.bound text -> StageWrites.bound text (destination pol Prepare-pc) -> RejectCall.bound pc text -> RejectDispatch.bound pc text -> RejectFinish.bound text -> StageEntry.checked_layout text (destination pol Prepare-pc)=true -> ChunkStaging.preserves_bp text=true -> HashEntry.bound pc text -> ScoreSetup.bound pol pc text ->
 batch_contract pol pc text.
Proof.
 intros Image Bytes Setup Select Pad Transfer Rejection ScatterCode ExitCode RBP LoopBP Hash Scorer.
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
 assert (CallerCode:StrictDispatch.bound pc text) by
   (exact (conj Hash (conj ScatterCode (conj ExitCode (proj1(proj2(proj2(proj2 Rejection)))))))).
 assert (Native:forall bias e c masks,admissible pol bias pc text e -> (0<count e)%nat ->
     first_chunk pol bias pc text e c masks).
 { intros bias e c masks Input N.
   destruct (scalar_from_entry _ _ _ _ _ c masks Input N (Live _ _ Input N)) as [s [Run Post]].
   destruct (ChunkScalar.first_execution _ _ _ _ _ _ _ _ Run) as [_ [bank [_ [_ [Bank Words]]]]].
   specialize (Words (cpu_words _ _ _ _ _ Input)).
   destruct (@ChunkScreen.checked BatchWindow.initial pol bias pc text e s bank Input CallerCode N Post Words) as [Digits [Decode Reject]].
   exists s;split;[exact Run|split;[exact Post|split;[exact Digits|split]]].
   - intro NZ;destruct (Decode NZ) as [d [To [Entry [Caller [t Trace]]]]].
     exists d;split;[unfold BatchDecode.observe;rewrite Run;cbn [LinkedRun.bind];now rewrite (proj2(Z.eqb_neq _ _) NZ)|].
     split;[exact Entry|split;[exact Caller|exists bank,t;exact (conj Bank Trace)]].
   - intro Zero;split;[exact (ScalarInputs.zero_rejects pol e _ Digits Zero)|].
     unfold RejectExecution.scalar_rejection;rewrite Run;cbn [LinkedRun.bind];rewrite Zero,Z.eqb_refl;exact (Reject Zero). }
 assert (Run:forall bias e c masks,admissible pol bias pc text e ->
   (exists ws ip final,observation pol bias pc text e c masks ws ip final) /\
   (forall ws ip final,observation pol bias pc text e c masks ws ip final -> returned pol e ip final /\ effects e ws final)).
 { intros;apply observed_correct;[exact Image|exact CallerCode|exact Scorer|exact (conj Select (conj Pad (conj Transfer LoopBP)))|assumption|apply Empty|apply Live];assumption. }
 constructor;[exact Image|exact Arguments.checked_arguments|exact static_tables_correct|
 exact (linked_calls pol)|exact (conj CallWrites.embedded (conj NestedRegions.embedded protected_slots))|exact Run| |exact CallerCode|exact Scorer| | | |].
 - intros bias e Input;split.
   + intros ip final N cf masks ws O x X;destruct(proj2(Run bias e cf masks Input) _ _ _ O) as [[_ [_ [_ [_ [F _]]]]] _].
     apply F,(LoadedImage.immutable _ _ _ _ (callee_image _ _ _ _ _ Input N)),X.
   + intro N;split.
     * intros prior s carry ws last Past Current D L Steps.
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
       destruct (CallWrites.scatter_stores CallWrites.embedded _ _ _ _ _ _ Place D L Map Apart Steps) as [W Replay].
       split;[exact W|rewrite Replay;apply LoadedImage.after;[exact Loaded|]].
       exact (TracedCalls.lend _ _ _ (nested_in_root _) W).
     * destruct (batch_inputs _ _ _ _ _ Input N) as [Place [_ [[_ Apart] _]]].
       apply RejectCall.checked with (mode:=pol);
         [exact Rejection|exact Place|exact (entry_range _ _ _ _ _ Input)|
          exact (entry_text _ _ _ _ _ Input)|exact Apart|exact (callee_image _ _ _ _ _ Input N)].
 - exact Live.
 - exact Native.
 - intros bias e c masks stop A N Scored;eapply scorer_verdict_checked;[exact A|exact N|exact CallerCode|exact Scorer|apply Native|exact Scored];assumption.
 - intros bias e Input Z. destruct (empty_return e) as [ip final] eqn:E. split.
   + exact (proj1(empty_correct _ _ _ _ _ _ _ Input Z E)).
   + exact (Empty _ _ Input Z).
Qed.

Theorem assembled_zip215_verify_batch_correct :
 batch_contract Zip215 ZipBytes.address ZipBytes.symbol_bytes.
Proof. apply verified;[vm_compute;split;reflexivity|vm_compute;repeat split;reflexivity|repeat constructor|repeat constructor|repeat constructor|vm_compute;repeat split;reflexivity|vm_compute;repeat split;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|vm_compute;reflexivity|vm_compute;reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity]. Qed.

Theorem assembled_dalek_verify_batch_correct :
 batch_contract Dalek DalekBytes.address DalekBytes.symbol_bytes.
Proof. apply verified;[vm_compute;split;reflexivity|vm_compute;repeat split;reflexivity|repeat constructor|repeat constructor|repeat constructor|vm_compute;repeat split;reflexivity|vm_compute;repeat split;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|vm_compute;reflexivity|vm_compute;reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity]. Qed.
