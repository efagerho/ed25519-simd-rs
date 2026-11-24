From Coq Require Import List ZArith Lia Bool.
From Machine Require Import execution.LinkedCalls memory.ByteMemory memory.FlatMemory.
From Curve25519 Require Import Radix51.
From Curve25519.group Require Import Affine Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Chunks Decode Kernels Program Unpack.
From Ed25519Simd.PostHash Require Lanes Product.
From Ed25519Simd.Dalek Require Batch FieldOps.
From Ed25519Simd.PrepareChunk Require Composition Staging.
From Ed25519Simd.DalekPostHash Require Decoded.
From Ed25519Simd.Zip215 Require Calls Equation.
From Ed25519Simd.Torsion Require Audit Object.
From Ed25519Simd.VerifyBatch Require Import Policy Lane Rows Digest Prepare Hash Candidate ProductRun.
Local Open Scope Z_scope.
Definition flat c := Staging.staged(p c).
Definition os c := Decoded.outputs Decode.Program.code (flat c) (scratch c).
Definition rvalid c := Decoded.valid_mask Decode.Program.code (flat c) (scratch c).
Definition saved_rvalid c := metadata c (Staging.selected(p c)+72).
Definition raw c j := Unpack.encoded (flat c) (scratch c+256) j.
Definition pad c := Z.to_nat ((stack_base c mod 64)/16).
Definition initial c j r := vectors(entry c) j r.

Definition mask c q := match mode c with
 | Policy.Zip215=> option_map (fun m=>Z.land m (saved_rvalid c))
     (Calls.torsion_run (pad c) q (Lanes.words(os c)) (initial c))
 | Policy.Dalek=>Decoded.direct Decode.Program.code (os c) (saved_rvalid c) (enabled c) q (pad c) (initial c)
 end.

Lemma kernels_checked op : Kernels.verified Decode.Program.code op=true.
Proof. destruct op;vm_compute;reflexivity. Qed.
Lemma decoder_lanes : Decoded.decoder_runs Decode.Program.code.
Proof.
 intros m ptr Bytes j J. apply (proj2(Chunks.decode_chunks _ (kernels_checked _) (kernels_checked _)
  (kernels_checked _) m ptr true Bytes));cbn;lia.
Qed.
Local Opaque Chunks.returned PrepareChunk.Composition.filter_entry PrepareChunk.Staging.scalar_run.
Lemma preparation_mask c : Prepare.placement c -> ready c=true -> saved_rvalid c=rvalid c.
Proof.
 intros P On. unfold saved_rvalid,metadata,PrepareChunk.Audit.metadata.
 rewrite write_outside by (unfold PrepareChunk.Caller.flags_offset;lia).
 replace (Staging.selected(p c)+72) with ((Staging.selected(p c)+PrepareChunk.Caller.r_mask_offset)+0)
 by reflexivity || (unfold PrepareChunk.Caller.r_mask_offset;ring).
 rewrite write_at by lia. unfold rvalid, Decoded.valid_mask, flat, scratch, PrepareChunk.Composition.decoded;reflexivity.
Qed.
Lemma raw_original c j : Prepare.placement c -> (j<8)%nat ->
 raw c j=little_endian(r_bytes(input_at c j)).
Proof.
 intros P J;destruct(same_input _ _ P J) as [_ [R _]]. rewrite <-R;exact (Staging.staged_encoding (p c) true j J).
Qed.
Lemma zip_bounds c q : Prepare.placement c -> Wide51.strict q ->
 Torsion.Audit.input_bounds q (Lanes.words(os c)).
Proof.
 intros P Bound row j R J;split;[apply (strict_split _ Bound);assumption|].
 intros _. rewrite Lanes.word_cell by assumption.
 pose proof (decoder_lanes (flat c) (scratch c) (Staging.staged_wf _ (rows_bytes c (entry_memory _ P))) j J) as H.
 destruct H as [_ [X [Y [Z [T _]]]]];unfold os,Decoded.outputs.
 assert (I:(row mod 5<5)%nat) by (apply Nat.mod_upper_bound;lia).
 assert (D:(row/5<4)%nat) by (apply Nat.div_lt_upper_bound;lia).
 destruct (row/5)%nat as [|[|[|[|d]]]];try lia;cbn [Lanes.component];  specialize(X _ I);specialize(Y _ I);specialize(Z _ I);specialize(T _ I);unfold Radix51.split in *;lia.
Qed.

Local Opaque MaskTrace.result Chunks.lane_output.
Lemma scored c q Q : Prepare.placement c -> ready c=true ->
 Wide51.strict q -> (forall j,(j<8)%nat -> represents_point (full c) (point_values q j) (Q j)) ->
 exists m,mask c q=Some m /\ forall j,(j<8)%nat ->
  ((enabled c j && Z.testbit m (Z.of_nat j))%bool=true <->
    enabled c j=true /\ check_point (mode c) (raw c j) (Q j)).
Proof.
 intros P On Bound Reps. assert (Pad:(pad c<4)%nat).
 { unfold pad. pose proof(Z.mod_pos_bound (stack_base c) 64 ltac:(lia)).
   assert (0<=(stack_base c mod 64)/16<4) by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia). lia. }
 assert (B:byte_memory(flat c)) by (apply Staging.staged_wf,rows_bytes,entry_memory,P).
 unfold mask;rewrite preparation_mask by assumption. unfold full in Reps.
 destruct(mode c) eqn:Mode.
 - destruct (Torsion.Audit.run_correct _ Torsion.Object.assembled_torsion_correct _ _ _ (initial c)
     Pad (zip_bounds c q P Bound)) as [m [Run [_ Bits]]].
   change (Calls.torsion_run (pad c) q (Lanes.words(os c)) (initial c)=Some m) in Run.
   rewrite Run; eexists;split;[reflexivity|].
   intros j J. specialize(Bits j J);rewrite Lanes.word_coords in Bits by exact J.
   pose proof(Equation.decoded_accepts Decode.Program.code (flat c) (scratch c) true (8+j)%nat
     (raw c j) (Q j) (point_values q j) m j (decoder_lanes _ _ B j J)
     ltac:(unfold raw,Unpack.encoded;f_equal;lia) (Reps j J) Bits) as E.
   unfold rvalid,Decoded.valid_mask;rewrite Z.land_spec,Lanes.octet_bit by exact J.
   replace (8*Z.of_nat 1+Z.of_nat j) with (Z.of_nat (8+j)) by lia.
   change (check_point Policy.Zip215 (raw c j) (Q j)) with (Equation.accepts (raw c j) (Q j)).
   rewrite <-E,!andb_true_iff. tauto.
 - assert (K:Dalek.FieldOps.checked Decode.Program.code=true) by (vm_compute;reflexivity).
   assert (V:Dalek.Batch.valid_chunk q Q).
   { split;[intros r j R J;apply (strict_split _ Bound);cbn;lia|intros j J;apply (proj1(Reps j J))]. }
   destruct (Decoded.direct_correct Decode.Program.code Decode.Program.code (flat c) (scratch c) q Q (enabled c) (pad c) (initial c) decoder_lanes K B Pad V)
    as [m [Run Bits]]. exists m;split;[exact Run|].
   intros j J. rewrite andb_true_iff,(Bits j J). cbn [check_point]. unfold Decoded.strict_R;tauto.
Qed.

Lemma score_hash c result keys q : Prepare.placement c -> ready c=true -> Hash.geometry c ->
 buffers c -> key_selection c keys -> Sha512Challenge.Output.challenge_digests (hash_entry c) (Sha512Challenge.Execution.after result) ->
 native_product c (Sha512Challenge.Execution.after result) keys q ->
 exists m, mask c q=Some m /\ forall j,(j<8)%nat ->
   ((enabled c j && Z.testbit m (Z.of_nat j))%bool=true <->signature_accepts (mode c) (input_at c j)).
Proof.
 intros P On Geom Buf Keys Dig [mid [ip Obs]].
 destruct(Product.product_ok _ _ _ _ _ _ _ _ _ Obs) as [Bound Reps].
 destruct(scored _ _ _ P On Bound Reps) as [m [Run Rules]];exists m;split;[exact Run|].
 intros j J. rewrite Rules,raw_original by assumption. unfold Product.candidate.
 apply checked_lane;[apply enabled_ok;assumption|].
 intro Live. split;[eapply enabled_key;eassumption|]. split.
 - rewrite (proj1(digits_passed c mid j Buf J));apply prepared_scalar;assumption.
 - unfold Product.challenge. change (regs(reducer c (Sha512Challenge.Execution.after result)) 6%nat)
    with (regs(hash_entry c) 7%nat). change (mem(reducer c (Sha512Challenge.Execution.after result)))
    with (Sha512Challenge.Execution.after result).
   rewrite (sha_to_scalar _ _ j J Dig),(hash_input c j P Geom J Live);reflexivity.
Qed.
