From Coq Require Import ZArith List Lia.
From Machine Require Import execution.LinkedCalls memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.Decode Require Object.
From Ed25519Simd.KeyTable Require Object.
From Ed25519Simd.DalekPostHash Require Audit Object.
From Ed25519Simd.PrepareChunk Require Import Caller Staging Dispatch Composition Audit.
Local Open Scope Z_scope.

Local Opaque decoded scalar_run Keys.filter_keys filter_entry.

Local Lemma byte_one b : Z.b2z b=1 <-> b=true.
Proof. destruct b;intuition discriminate. Qed.

Lemma prepares mode p prior incoming slide ts :
 layout p -> byte_memory(original p) -> scalar_inputs p prior slide ->
 (forall t,WordBounds.data_words(ts t)) -> chunk_result mode p prior incoming slide ts.
Proof.
 intros Layout Bytes Args Scratch;pose proof(scalar_call p prior incoming slide Args) as Scalar.
 unfold chunk_result;set (out:=scalar_run p prior incoming slide) in *;set (s:=regs out 0%nat).
 set (cpu:=filter_entry p ts prior).
 pose proof(initializes_tables p ts Bytes Scratch) as Init.
 pose proof(built_tables p ts prior Layout Bytes Init) as Tables.
 assert (Lanes:forall sig j,(j<8)%nat -> lane_result p sig j) by (intros;apply decode_lane;assumption).
 assert (Flags:forall j,(j<8)%nat -> (final_flag mode cpu s (decoded p) j=true <-> accepts mode p j)).
 { intros;apply valid_lane;auto. }
 split.
 - rewrite ready_correct by exact (proj1 Scalar);split;intros [j [J H]];exists j;split;[exact J|apply Flags;assumption|exact J|apply Flags;assumption].
 - intros _;split;[exact Scalar|];split;[exact Init|];split;[exact Tables|];intros j J.
   set (m:=metadata mode p cpu s).
   split;[intros;apply staged_bytes;assumption|].
   split;[intros;apply Lanes,J|].
   assert (R:m (selected p+72)=Lanes.octet (decoded p) 1).
   { unfold m,metadata;rewrite write_outside by (unfold flags_offset;lia).
     replace (selected p+72) with ((selected p+r_mask_offset)+0) by (unfold r_mask_offset;ring).
     rewrite write_at by lia;reflexivity. }
   split;[now rewrite R|].
   assert (F:m (selected p+64+Z.of_nat j)=Z.b2z(final_flag mode cpu s (decoded p) j)).
   { unfold m,metadata;unfold flags_offset;rewrite write_at by lia;now rewrite Nat2Z.id. }
   rewrite F;split.
   + rewrite <-(Flags _ J);exact (byte_one _).
   + split;[destruct(final_flag _ _ _ _ _);auto|].
     transitivity (read_word (mem cpu) (selected p+8*Z.of_nat j)).
     * apply read_block;intros k K;unfold m,metadata;rewrite !write_outside by (unfold flags_offset,r_mask_offset;lia);reflexivity.
     * unfold cpu;rewrite pointer_value by assumption;unfold selected_ptr.
       unfold returned_bit,key_mask.
       destruct(bit _ _);[unfold table_offset,table_stride,tables_offset;ring|reflexivity].
Qed.

Local Transparent decoded.
Theorem assembled_prepare_chunk_correct : prepare_chunk_contract.
Proof.
 constructor.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;repeat split;reflexivity.
 - exact Decode.Object.assembled_decode_correct.
 - intros p pad Pad.
   assert (Call:Decode.Caller.caller_result (HelperBytes.address-pc DecodePair)
     (DecoderBytes.pow_pc-pc DecodePair) true pad).
   { destruct pad as [|[|[|[|pad]]]];try lia;vm_compute;repeat split;reflexivity. }
   split;[exact Call|].
   unfold decoded;exact (Chunks.returned_by_caller _ _ Decode.Program.code (staged p) (scratch p) true pad Call).
 - intros [];repeat split;reflexivity.
 - vm_compute;repeat split;reflexivity.
 - exact KeyTable.Object.assembled_key_table_correct.
 - split;[|exact (DalekPostHash.Audit.arithmetic_bytes DalekPostHash.Object.assembled_dalek_post_hash_correct)].
   exact (proj1 ((proj1 (DalekPostHash.Audit.wrapper_bytes
     DalekPostHash.Object.assembled_dalek_post_hash_correct)) DalekPostHash.Caller.Filter
     ltac:(simpl;tauto))).
 - intros mode p prior incoming slide ts [Layout _];apply prepares,Layout.
Qed.
