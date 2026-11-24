From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.PrepareChunk Require Object.
From Ed25519Simd.Sha512Challenge Require Object.
From Ed25519Simd.Zip215 Require Object.
From Ed25519Simd.DalekPostHash Require Object.
From Ed25519Simd.VerifyBatch Require Import Policy Image Control Scatter Loop Return LoadedImage EntryWrites CallWrites NestedRegions Prologue StageEntry RejectCall Audit TableCertificate ZipBytes DalekBytes.
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

Lemma observed_correct pol pc text bias e carry masks :
 matches pc (destination pol) text -> admissible pol bias pc text e ->
 (count e=0%nat -> empty_mapped (bias+pc) text e) ->
 ((0<count e)%nat -> StageEntry.physical (bias+pc) text (destination pol Prepare-pc) e) ->
 (exists ws ip final,observation pol bias pc text e carry masks ws ip final) /\
 (forall ws ip final,observation pol bias pc text e carry masks ws ip final ->
    returned pol e ip final /\ WriteTrace.confined (writable e) ws).
Proof.
 intros Image Caller Empty Batch;destruct (grouped _ _ _ Image _ _ Caller) as [Exists Sound].
 split.
 - destruct (Nat.eqb_spec (count e) 0) as [Z|Live].
   + specialize (Empty Z);unfold empty_mapped in Empty;destruct(empty_return e) as [ip f].
     exists nil,ip,f;apply observe_empty;[exact Z|exact (proj1 (Empty carry))].
   + destruct Exists as [ip [f R]];destruct(scalar_from_entry _ _ _ _ _ carry masks Caller ltac:(lia) (Batch ltac:(lia))) as [stop [O _]].
     exists (LinkedRun.log stop),ip,f;eapply observe_batch;[lia|exact O|exact R].
 - intros ws ip f O;inversion O as [ws' ip' f' Z Run|st ip' f' N Native R];subst.
   + specialize (Empty Z);unfold empty_mapped in Empty;destruct(empty_return e) as [back last] eqn:E.
     destruct (proj2 (Empty carry) _ _ Run) as [-> Same].
     inversion Same as [|s t u own rest Impossible];[|discriminate].
     subst;split;[apply Sound,empty_path;[exact Image|now rewrite Z|exact E]|constructor].
   + destruct (scalar_from_entry _ _ _ _ _ carry masks Caller N (Batch N)) as [mid [Trace [_ [_ [[Safe _] _]]]]].
     rewrite Trace in Native;injection Native as <-;exact (conj (Sound _ _ R) Safe).
Qed.

Lemma verified pol pc text : matches pc (destination pol) text -> empty_image text -> Prologue.bound text -> StageEntry.bound text -> TailWrites.bound text -> StageWrites.bound text (destination pol Prepare-pc) -> RejectCall.bound pc text -> RejectDispatch.bound pc text -> RejectFinish.bound text ->
 batch_contract pol pc text.
Proof.
 intros Image Bytes Setup Select Pad Transfer Rejection ScatterCode ExitCode.
 assert (Empty:forall bias e,admissible pol bias pc text e -> count e=0%nat ->
   empty_mapped (bias+pc) text e).
 { intros bias e Input Z;apply mapped_return;[exact (entry_text _ _ _ _ _ Input)|].
   apply empty_path_writes;[exact Bytes|exact (cpu_words _ _ _ _ _ Input)|exact Z]. }
 assert (Live:forall bias e,admissible pol bias pc text e -> (0<count e)%nat ->
   StageEntry.physical (bias+pc) text (destination pol Prepare-pc) e).
 { intros bias e Input N;destruct (batch_inputs _ _ _ _ _ Input N) as [P [[Rows _] [[_ Apart] _]]].
   destruct Rows as [Fit Const].
   apply StageEntry.from_entry;[exact Setup|exact Select|exact Pad|exact Transfer|exact P|exact N|exact Fit|exact Const|
     exact (entry_text _ _ _ _ _ Input)|exact Apart]. }
 constructor;[exact Image|exact Arguments.checked_arguments|exact static_tables_correct|
 exact (linked_calls pol)|exact (conj CallWrites.embedded (conj NestedRegions.embedded protected_slots))| | | | |].
 - intros bias e carry masks Input;eapply observed_correct;[exact Image|exact Input|apply Empty|apply Live];exact Input.
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
 - intros bias e c masks Input N.
   destruct (scalar_from_entry _ _ _ _ _ c masks Input N (Live _ _ Input N)) as [stop [Run Post]].
   exists stop;split;[exact Run|split;[exact Post|]].
   assert (Digits:ScalarInputs.recoded e (LinkedRun.machine stop)).
   {destruct Post as [_ [_ [_ [_ [_ Recoded]]]]]. apply Recoded;[exact N|].
     destruct (batch_inputs _ _ _ _ _ Input N) as [_ [[_ Inputs] _]].
     intros j J;exact (proj1 (proj2 (Inputs j J))). }
   split;[exact Digits|]. intro Zero;split;[exact (ScalarInputs.zero_rejects pol e _ Digits Zero)|].
   destruct (batch_inputs _ _ _ _ _ Input N) as [Place [_ [[_ Apart] _]]].
   pose proof (callee_image _ _ _ _ _ Input N) as Loaded.
   destruct (PrepareUnwind.rejected _ _ _ _ _ Place Loaded Post Zero) as [caller [Unwind End]].
   destruct End as [At [SP [AX [Memory [Log [Args Left]]]]]];destruct Post as [_ [_ [[Safe Replay] _]]].
   assert (Paid:LinkedRun.accounted e (writable e) caller) by
     (split;[rewrite Log;exact Safe|intros x;rewrite Memory,Log;apply Replay]).
   pose proof (entry_text _ _ _ _ _ Input) as Mapped.
   destruct (RejectDispatch.resume pol bias pc text e caller ScatterCode Place Loaded (entry_range _ _ _ _ _ Input)
     (proj1 (proj2 (proj2 (proj2 Rejection)))) Mapped Apart Paid At SP Args Left ltac:(now rewrite AX))
     as [cont [Dispatched Continued]].
   destruct (RejectFinish.next _ _ _ _ _ ExitCode Place Mapped Apart Continued) as [last [Finished Exit]].
   exists (RejectExecution.classify cont last);split;[|exact (RejectExecution.classified _ _ _ _ Place (proj2 (proj2 (proj2 Continued))) Exit)].
   unfold RejectExecution.scalar_rejection,RejectExecution.finish_chunk;rewrite Run;cbn [LinkedRun.bind].
   rewrite Zero,Z.eqb_refl,Unwind;cbn [LinkedRun.bind];rewrite Dispatched;cbn [LinkedRun.bind];now rewrite Finished.
 - intros bias e Input Z. destruct (empty_return e) as [ip final] eqn:E. split.
   + apply (proj2 (grouped _ _ _ Image _ _ Input)),empty_path;[exact Image|now rewrite Z|exact E].
   + exact (Empty _ _ Input Z).
Qed.

Theorem assembled_zip215_verify_batch_correct :
 batch_contract Zip215 ZipBytes.address ZipBytes.symbol_bytes.
Proof. apply verified;[vm_compute;split;reflexivity|vm_compute;repeat split;reflexivity|repeat constructor|repeat constructor|repeat constructor|vm_compute;repeat split;reflexivity|vm_compute;repeat split;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity]. Qed.

Theorem assembled_dalek_verify_batch_correct :
 batch_contract Dalek DalekBytes.address DalekBytes.symbol_bytes.
Proof. apply verified;[vm_compute;split;reflexivity|vm_compute;repeat split;reflexivity|repeat constructor|repeat constructor|repeat constructor|vm_compute;repeat split;reflexivity|vm_compute;repeat split;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity]. Qed.
