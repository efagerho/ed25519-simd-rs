From Coq Require Import List ZArith Lia.
From Machine Require execution.Composition.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.WordSemantics execution.ScalarBytes
 execution.ScalarWords memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.PrepareChunk Require Staging.
From Ed25519Simd.VerifyBatch Require Import Policy Image Return BatchScalar LoadedImage.
From Ed25519Simd.VerifyBatch Require BatchWindow ChunkStaging ChunkRows ScalarInputs WrapperInputs ScalarState.
Local Open Scope Z_scope.

Definition execute pol bias p masks:=bind (enter pol bias p) (fun child=>
 option_map (fun q=>(q,outgoing_masks bias (machine child) masks)) (scalar_call bias masks child)).

Local Opaque SignatureScalar.Program.run outgoing_masks SignatureScalar.Audit.digit_writes.
Lemma valid_words pol bias p masks q bank:well_formed(machine p) -> execute pol bias p masks=Some(q,bank) ->
 byte_memory (mem(machine q)) -> well_formed(machine q).
Proof.
 intros W;unfold execute,enter;destruct(via_strict pol bias p) as [s|] eqn:Shim;[|discriminate];cbn [bind].
 assert (SW:well_formed(machine s)) by (destruct pol;[injection Shim as <-;exact W|eapply segment_wf;eassumption]).
 destruct(to_scalar bias s) as [v|] eqn:Call;[|discriminate];cbn [bind].
 unfold scalar_call;destruct (_=?_);[|discriminate];destruct(list_eq_dec _ _ _);[|discriminate].
 destruct(SignatureScalar.Program.run _ _ _ _ _ _) as [back out] eqn:R;intro Eq;apply (f_equal (option_map fst)) in Eq;cbn [option_map fst] in Eq;injection Eq as <-.
 exact (ScalarState.returned_words _ _ _ _ _ _ _ _ (segment_wf _ _ _ _ _ SW Call) R).
Qed.

(* The first window gets its staging cursor from the wrapper entry. From that
   cursor the scalar call and outgoing mask bank are the same as in the loop. *)
Lemma first_execution pol bias entry text e c masks q :
 BatchScalar.observe pol bias entry text e c masks=Some q ->
 exists p bank,StageEntry.begin entry text e c=Some p /\ execute pol bias p masks=Some(q,bank) /\
   BatchScalar.masks_after pol bias entry text e c masks=Some bank /\
   (well_formed e -> byte_memory (mem(machine q)) -> well_formed(machine q)).
Proof.
 unfold BatchScalar.observe,BatchScalar.masks_after,scalar_entry.
 destruct (StageEntry.begin entry text e c) as [p|] eqn:Start;[|discriminate];cbn [bind].
 destruct (enter pol bias p) as [child|] eqn:E;[|discriminate];cbn [bind option_map].
 intro Call;set (bank:=outgoing_masks bias (machine child) masks).
 assert (Run:execute pol bias p masks=Some(q,bank)) by (unfold execute;rewrite E;cbn [bind];now rewrite Call).
 exists p,bank;split;[reflexivity|split;[exact Run|split;[reflexivity|]]].
 intro Words;exact (valid_words _ _ _ _ _ _ (StageEntry.begin_words _ _ _ _ _ Words Start) Run).
Qed.

Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition result pol bias pc e (pair:cursor*(nat->nat->bool)) :=
 BatchScalar.post pol bias (bias+pc) e (fst pair) /\
 (byte_memory (mem(machine (fst pair))) -> well_formed(machine (fst pair))).

Theorem checked pol bias pc e p masks:placement e -> loaded pol bias (mem e) (writable e) ->
 ChunkStaging.entry (bias+pc) (first_symbol pol-pc) e BatchWindow.first (BatchWindow.remaining e) p ->
 (forall x,BatchWindow.earlier e x -> mem(machine p) x=BatchWindow.before x) ->
 Composition.ensures (Composition.output (execute pol bias p masks)) (result pol bias pc e).
Proof.
 intros P Image St Earlier;destruct St as [Target Paid W SP Ret Matrix Metadata [SI [CX [DI Id]]] [Scratch Out] Left Next Saved Tables].
 destruct Saved as [RawSlots BP];assert (Saved:BatchWindow.saved_caller e (machine p)) by (split;[apply BatchWindow.attach;assumption|exact BP]).
 assert (View:input_view e p).
 { split;[exact W|split;[|split;[exact Metadata|split;[exact Saved|split;[exact Id|split;[exact Scratch|]]]]]].
   - intros j sig J;apply PrepareChunk.Staging.read_block;intros k K;destruct sig.
     + exact (Matrix j 1%nat k J ltac:(lia) K).
     + exact (Matrix j 0%nat k J ltac:(lia) K).
   - constructor;[exact Tables|intros kind j J;unfold WrapperInputs.address,WrapperInputs.field,descriptor;apply PrepareChunk.Staging.read_block;intros k K;destruct kind].
     + replace (Rows.frame e+704) with (DescriptorStores.bank (Rows.frame e) 3) by (unfold DescriptorStores.bank;ring);exact (Matrix j 3%nat k J ltac:(lia) K).
     + replace (Rows.frame e+640) with (DescriptorStores.bank (Rows.frame e) 2) by (unfold DescriptorStores.bank;ring);exact (Matrix j 2%nat k J ltac:(lia) K). }
 assert (Cursor:BatchWindow.next_descriptor e (regs(machine p) 3%nat)).
 { intros More;rewrite (Next More);unfold ChunkRows.base;rewrite Nat2Z.inj_add.
   replace (regs e 7%nat+(40*Z.of_nat BatchWindow.first+320)) with (regs e 7%nat+40*(Z.of_nat BatchWindow.first+Z.of_nat 8)) by ring.
   rewrite <-Nat2Z.inj_add;fold (ChunkRows.base e (BatchWindow.first+8));rewrite <-(Next More).
   symmetry;apply word_fits,(proj1 W). }
 assert (At:ip p=bias+first_symbol pol).
 { rewrite Target;replace (bias+pc+(first_symbol pol-pc)) with (bias+first_symbol pol) by ring.
   apply word_fits;destruct pol;[apply (mapped_word _ _ _ Image _ _ (in_common _) ltac:(vm_compute;reflexivity))|
     apply (mapped_word _ _ _ Image _ _ in_strict ltac:(vm_compute;reflexivity))]. }
 rewrite <-(BatchWindow.live_count e (initial_cpu _ P)) in Left.
 destruct(@reach_common iteration pol bias (bias+pc) e p P Image Paid At (conj SP (conj DI (conj SI (conj CX (conj Out (conj Left View)))))) Ret Cursor)
   as [v [Shim [A [PC [Args [Slots [Strict Zip]]]]]]].
 destruct(@through_scalar iteration pol bias (bias+pc) e v masks P Image A PC Args Slots Strict Zip) as [q [Run Post]].
 destruct(to_scalar bias v) as [child|] eqn:Raw;[|discriminate];cbn [bind] in Run.
 set (bank:=outgoing_masks bias (machine child) masks).
 assert (Call:execute pol bias p masks=Some(q,bank)).
 { unfold execute,enter;rewrite Shim;cbn [bind];rewrite Raw;cbn [bind];now rewrite Run. }
 apply Composition.option_result;exists (q,bank);split;[exact Call|split;[exact Post|]].
 exact (valid_words _ _ _ _ _ _ W Call).
Qed.
End Iteration.
