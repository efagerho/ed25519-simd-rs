From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls memory.FlatMemory memory.ByteMemory memory.MemoryGeometry.
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

Lemma rejected_verdict pol bias pc text e c masks stop : admissible pol bias pc text e ->
 (0<count e<=8)%nat -> first_chunk pol bias pc text e c masks ->
 BatchScalar.observe pol bias (bias+pc) text e c masks=Some stop -> regs(LinkedRun.machine stop) 0%nat mod 2^32=0 ->
 exists q,RejectExecution.scalar_rejection pol bias pc text e c masks=Some(RejectExecution.BatchReturned q) /\
   returned pol e (LinkedRun.ip q) (LinkedRun.machine q) /\ LinkedRun.accounted e (writable e) q /\
   forall i,(i<count e)%nat -> mem(LinkedRun.machine q)(output e+Z.of_nat(position e i))=0 /\
   ~signature_accepts pol (read_input (mem e) (regs e 7%nat) i).
Proof.
 intros Caller [Live Size] [s [Run [_ [_ [_ Reject]]]]] O Zero;rewrite O in Run;injection Run as <-.
 destruct(Reject Zero) as [Invalid [[q|q] [Path [Paid [[Status Outputs] [Bytes Exit]]]]]].
 2:{ destruct Exit as [More _];lia. }
 destruct Exit as [_ [PC [SP Saved]]]. destruct(batch_inputs _ _ _ _ _ Caller Live) as [_ [_ [_ [_ [Idx _]]]]].
 exists q;split;[exact Path|split].
 - unfold returned;repeat apply conj;try assumption.
   + intros x Outside;rewrite (proj2 Paid);apply (WriteTrace.frame _ _ (proj1 Paid)),Outside.
   + intros j J;destruct(indices_cover e Idx j J) as [i [I <-]];left;apply Outputs;lia.
   + intros i I;exists false;split;[apply Outputs;lia|split;[discriminate|intro A;exfalso;exact (Invalid i ltac:(lia) I A)]].
 - split;[exact Paid|intros i I;split;[apply Outputs;lia|apply Invalid;lia]].
Qed.

Lemma continuing_footprint pol bias pc text e c masks stop :
 first_chunk pol bias pc text e c masks ->
 BatchScalar.observe pol bias (bias+pc) text e c masks=Some stop ->
 ((8<count e)%nat \/ regs(LinkedRun.machine stop) 0%nat mod 2^32<>0) ->
 exists p,continuing_prefix pol bias pc text e c masks stop=Some p /\ LinkedRun.accounted e (writable e) p.
Proof.
 intros [s [Run [_ [_ [Checked Rejected]]]]] O More;rewrite O in Run;injection Run as <-.
 unfold continuing_prefix;destruct (Z.eqb_spec (regs(LinkedRun.machine stop) 0%nat mod 2^32) 0) as [Zero|Positive].
 - destruct(Rejected Zero) as [_ [[q|q] [Trace [Paid [_ [_ Exit]]]]]].
   + destruct More as [Large|H];[|contradiction];destruct Exit as [Small _];lia.
   + exists q;rewrite Trace;auto.
 - destruct(Checked Positive) as [d [Trace [_ Body]]].
   destruct Body as [bank [r [Bank [R Body]]]];pose proof(PairReturn.writes _ _ _ _ Body) as Paid;exists (PairReturn.returned r);
     rewrite Trace;cbn [LinkedRun.bind];rewrite Bank;cbn [LinkedRun.bind];rewrite R;auto.
Qed.

Lemma observed_correct pol pc text bias e carry masks :
 matches pc (destination pol) text -> admissible pol bias pc text e ->
 (count e=0%nat -> empty_mapped (bias+pc) text e) ->
 ((0<count e)%nat -> first_chunk pol bias pc text e carry masks) ->
 (exists ws ip final,observation pol bias pc text e carry masks ws ip final) /\
 (forall ws ip final,observation pol bias pc text e carry masks ws ip final ->
    returned pol e ip final /\ WriteTrace.confined (writable e) ws).
Proof.
 intros Image Caller Empty Batch;destruct (grouped _ _ _ Image _ _ Caller) as [Exists Sound].
 split.
 - destruct (Nat.eqb_spec (count e) 0) as [Z|Live].
   + specialize (Empty Z);unfold empty_mapped in Empty;destruct(empty_return e) as [ip f].
     exists nil,ip,f;apply observe_empty;[exact Z|exact (proj1 (Empty carry))].
   + assert (N:(0<count e)%nat) by lia;pose proof(Batch N) as Full.
     destruct Full as [stop [O _]].
     assert (Grouped:((8<count e)%nat \/ regs(LinkedRun.machine stop) 0%nat mod 2^32<>0) ->
          exists ws ip f,observation pol bias pc text e carry masks ws ip f).
     { intros More;destruct Exists as [ip [f R]].
       destruct(continuing_footprint _ _ _ _ _ _ _ _ (Batch N) O More) as [q [Trace _]].
       do 3 eexists;exact (observe_batch _ _ _ _ _ _ _ _ _ _ _ N More O Trace R). }
     destruct(le_dec (count e) 8) as [Small|Large];[|apply Grouped;left;lia].
     destruct(Z.eq_dec (regs(LinkedRun.machine stop) 0%nat mod 2^32) 0) as [Zero|Nonzero];[|apply Grouped;right;exact Nonzero].
     destruct(rejected_verdict _ _ _ _ _ _ _ _ Caller (conj N Small) (Batch N) O Zero) as [q [Run _]].
     do 3 eexists;exact (observe_rejected _ _ _ _ _ _ _ _ _ (conj N Small) O Zero Run).
 - intros ws ip f O;inversion O as [ws' ip' f' Z Run|st q Size Native Zero Path|st prefix ip' f' N More Native Path R];subst.
   + specialize (Empty Z);unfold empty_mapped in Empty;destruct(empty_return e) as [back last] eqn:E.
     destruct (proj2 (Empty carry) _ _ Run) as [-> Same].
     inversion Same as [|s t u own rest Impossible];[|discriminate].
     subst;split;[apply Sound,empty_path;[exact Image|now rewrite Z|exact E]|constructor].
   + destruct(rejected_verdict _ _ _ _ _ _ _ _ Caller Size (Batch (proj1 Size)) Native Zero) as [q' [Run [ABI [Paid _]]]].
     rewrite Path in Run;injection Run as <-;exact (conj ABI (proj1 Paid)).
   + destruct(continuing_footprint _ _ _ _ _ _ _ _ (Batch N) Native More) as [q [Trace [Safe _]]].
     rewrite Path in Trace;injection Trace as <-;exact (conj (Sound _ _ R) Safe).
Qed.

Lemma verified pol pc text : matches pc (destination pol) text -> empty_image text -> Prologue.bound text -> StageEntry.bound text -> TailWrites.bound text -> StageWrites.bound text (destination pol Prepare-pc) -> RejectCall.bound pc text -> RejectDispatch.bound pc text -> RejectFinish.bound text -> StageEntry.preserves_bp text=true ->
 batch_contract pol pc text.
Proof.
 intros Image Bytes Setup Select Pad Transfer Rejection ScatterCode ExitCode RBP.
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
   destruct (batch_inputs _ _ _ _ _ Input N) as [P [[_ Inputs] _]].
   assert (Data:ScalarInputs.recoded e (LinkedRun.machine stop) /\ ScalarInputs.copy_ready e (LinkedRun.machine stop) /\ StageEntry.metadata e (mem(LinkedRun.machine stop)) /\ StageEntry.saved_caller e (LinkedRun.machine stop)).
   { destruct Post as [_ [_ [_ [_ [_ Contract]]]]]. apply Contract;[exact N|].
     intros j J;exact (proj1 (proj2 (Inputs j J))). }
   split;[exact (proj1 Data)|]. split.
   { intro Nonzero;destruct (BatchDecode.from_scalar pol bias pc text e c masks stop) as [d [Trace Entry]];
       [exact P|exact (callee_image _ _ _ _ _ Input N)| |exact Run|exact Post|exact (proj1(proj2 Data))|exact Nonzero|].
     2:{ exists d;split;[exact Trace|split;[exact Entry|]].
         destruct(BatchScalar.has_masks _ _ _ _ _ _ _ _ Run) as [bank Bank].
         pose proof(NativeWords.decoder_entry _ _ _ _ _ _ _ _ _ (initial_cpu _ P) Run (proj1(proj1(proj2 Data))) Trace) as Words.
         destruct(PairReturn.from_decoder _ _ _ _ bank P (callee_image _ _ _ _ _ Input N)
            (decoder_aligned _ _ _ _ _ Input N) Entry Words) as [r [R Check]].
         exists bank,r;auto. }
     intros j sig J;destruct (Inputs _ (TailCopy.live_row e j N)) as [Key [Sig Msg]].
     unfold ScalarInputs.encoding_ptr;destruct sig;[|exact Key]. destruct Sig as [[Low High] Away].
     split;[unfold fits64;split;[exact Low|lia]|intros x X;apply Away;lia]. }
   intro Zero;split;[exact (ScalarInputs.zero_rejects pol e _ (proj1 Data) Zero)|].
   destruct (batch_inputs _ _ _ _ _ Input N) as [Place [_ [[_ Apart] [_ [Indices _]]]]].
   pose proof (callee_image _ _ _ _ _ Input N) as Loaded.
   destruct (PrepareUnwind.rejected _ _ _ _ _ Place Loaded Post Zero) as [caller [Unwind End]].
   destruct End as [At [SP [AX [Memory [Log [Args [Left BP]]]]]]];destruct Post as [_ [_ [[Safe Replay] _]]].
   assert (Paid:LinkedRun.accounted e (writable e) caller) by
     (split;[rewrite Log;exact Safe|intros x;rewrite Memory,Log;apply Replay]).
   pose proof (entry_text _ _ _ _ _ Input) as Mapped.
   destruct (RejectDispatch.resume pol bias pc text e caller ScatterCode Place Loaded (entry_range _ _ _ _ _ Input)
     (proj1 (proj2 (proj2 (proj2 Rejection)))) Mapped Apart Paid At SP Args Left ltac:(now rewrite AX) N Indices
     ltac:(rewrite Memory;exact (proj1(proj2(proj2 Data))))
     ltac:(destruct (proj2(proj2(proj2 Data))) as [Slots Saved];split;[rewrite Memory;exact Slots|now rewrite BP])
     ltac:(rewrite Memory;exact (proj1(proj1(proj2 Data))))) as [cont [Dispatched [Continued [Outputs [Saved Octets]]]]].
   destruct (RejectFinish.next _ _ _ _ _ ExitCode Place Mapped Apart Continued Saved) as [last [Finished Exit]].
   exists (RejectExecution.classify cont last);split;[|exact (RejectExecution.classified _ _ _ _ Place (proj2 (proj2 (proj2 Continued))) Exit Outputs Octets)].
   unfold RejectExecution.scalar_rejection,RejectExecution.finish_chunk;rewrite Run;cbn [LinkedRun.bind].
   rewrite Zero,Z.eqb_refl,Unwind;cbn [LinkedRun.bind];rewrite Dispatched;cbn [LinkedRun.bind];now rewrite Finished. }
 constructor;[exact Image|exact Arguments.checked_arguments|exact static_tables_correct|
 exact (linked_calls pol)|exact (conj CallWrites.embedded (conj NestedRegions.embedded protected_slots))| | | | |].
 - intros bias e carry masks Input;eapply observed_correct;[exact Image|exact Input|apply Empty|apply Native];exact Input.
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
 - intros bias e Input Z. destruct (empty_return e) as [ip final] eqn:E. split.
   + apply (proj2 (grouped _ _ _ Image _ _ Input)),empty_path;[exact Image|now rewrite Z|exact E].
   + exact (Empty _ _ Input Z).
Qed.

Theorem assembled_zip215_verify_batch_correct :
 batch_contract Zip215 ZipBytes.address ZipBytes.symbol_bytes.
Proof. apply verified;[vm_compute;split;reflexivity|vm_compute;repeat split;reflexivity|repeat constructor|repeat constructor|repeat constructor|vm_compute;repeat split;reflexivity|vm_compute;repeat split;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|vm_compute;reflexivity]. Qed.

Theorem assembled_dalek_verify_batch_correct :
 batch_contract Dalek DalekBytes.address DalekBytes.symbol_bytes.
Proof. apply verified;[vm_compute;split;reflexivity|vm_compute;repeat split;reflexivity|repeat constructor|repeat constructor|repeat constructor|vm_compute;repeat split;reflexivity|vm_compute;repeat split;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|repeat constructor;vm_compute;discriminate || reflexivity|vm_compute;reflexivity]. Qed.
