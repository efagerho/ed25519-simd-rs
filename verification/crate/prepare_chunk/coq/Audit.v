From Coq Require Import ZArith List Bool.
From Machine Require Import execution.LinkedCalls memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.Decode Require Audit Image Program Kernels Chunks Caller DecoderBytes HelperBytes.
From Ed25519Simd.Pow2 Require ObjectBytes.
From Ed25519Simd.KeyTable Require Audit ObjectBytes CachedBytes.
From Ed25519Simd.SignatureScalar Require ObjectBytes.
From Ed25519Simd.DalekPostHash Require Caller Binding FilterBytes Queue Keys.
From Ed25519Simd.PostHash Require Import Lanes.
From Ed25519Simd.PrepareChunk Require Import CommonBytes StrictBytes Caller Staging Dispatch Composition.
Import ListNotations. Local Open Scope Z_scope.

Definition pc s := match s with
 | Common=>CommonBytes.address | Strict=>StrictBytes.address
 | Scalar=>SignatureScalar.ObjectBytes.address | DecodePair=>DecoderBytes.address
 | Tables=>KeyTable.ObjectBytes.address | Filter=>FilterBytes.address end.
Definition raw s := match s with
 | Common=>CommonBytes.symbol_bytes | Strict=>StrictBytes.symbol_bytes
 | Scalar=>SignatureScalar.ObjectBytes.symbol_bytes | DecodePair=>DecoderBytes.symbol_bytes
 | Tables=>KeyTable.ObjectBytes.symbol_bytes | Filter=>FilterBytes.symbol_bytes end.
Definition image_layout := KeyTable.Audit.linked
 (map (fun s=>KeyTable.Audit.span (pc s) (raw s)) [Common;Strict;Scalar;DecodePair;Tables;Filter])=true.

(* The common entry sees RSP 16 bytes below the strict entry's RSP.
   A 4 KiB reserved stack region includes the nested decoder and table calls. *)
Definition placement p :=
 let stack_region:=(stack p-4096,4120) in
 let writes:=[(scratch p,25344);(selected p,80);stack_region] in
 let separated a n:=forall r,In r writes -> disjoint a n (fst r) (snd r) in
 layout p /\ scratch p mod 64=0 /\ stack p mod 16=8 /\
 (forall r,In r writes -> fits64 (fst r) (snd r)) /\
 disjoint (scratch p) 25344 (fst stack_region) (snd stack_region) /\
 disjoint (selected p) 80 (fst stack_region) (snd stack_region) /\
 fits64 (pointers p) 128 /\ separated (pointers p) 128 /\
 fits64 (identity_ptr p) 2720 /\ separated (identity_ptr p) 2720 /\
 forall sig j,(j<8)%nat -> let n:=if sig:bool then 64 else 32 in
 fits64 (lane_ptr p sig j) n /\ separated (lane_ptr p sig j) n.

(* These are the bytes exposed to Rust on success. The post-hash consumer
   receives the upper decoder octet even when its corresponding S is invalid. *)
Definition metadata mode p cpu s :=
 let r:=write_bytes (mem cpu) (selected p+r_mask_offset) 1 (fun _=>octet (decoded p) 1) in
 write_bytes r (selected p+flags_offset) 8
   (fun i=>Z.b2z(final_flag mode cpu s (decoded p) (Z.to_nat i))).

Definition chunk_result mode p prior incoming slide table_scratch :=
 let out:=scalar_run p prior incoming slide in
 let s:=regs out 0%nat in let cpu:=filter_entry p table_scratch prior in
 let result:=dispatch mode cpu s (decoded p) in
 (snd result=true <-> exists j,(j<8)%nat /\ accepts mode p j) /\
 (snd result=true ->
   scalar_result p out /\ initialized_tables p table_scratch /\ tables_result p table_scratch prior /\
   forall j,(j<8)%nat ->
   let m:=metadata mode p cpu s in
   (forall sig k,0<=k<32 ->
     staged p (encoded_ptr p sig j+k)=original p (lane_ptr p sig j+k)) /\
   (forall sig,lane_result p sig j) /\
   bit (m (selected p+72)) j=returned_bit p true j /\
   (m (selected p+64+Z.of_nat j)=1 <-> accepts mode p j) /\
   (m (selected p+64+Z.of_nat j)=0 \/ m (selected p+64+Z.of_nat j)=1) /\
   read_word m (selected p+8*Z.of_nat j)=
   (if returned_bit p false j then scratch p+3584+2720*Z.of_nat j else identity_ptr p)).

(* The paired decoder's native return is the same packed mask consumed
   by the two wrapper branches, for every allowed decoder stack padding. *)
Definition decoder_handoff :=
 let h:=HelperBytes.address-pc DecodePair in let pow:=DecoderBytes.pow_pc-pc DecodePair in
 forall p pad,(pad<4)%nat ->
 Decode.Caller.caller_result h pow true pad /\
 Decode.Caller.return_value h pow true pad
   (Chunks.chunk_mask Decode.Program.code (staged p) (scratch p) true)=decoded p.
Definition exits := forall zero,
 next common Scalars zero=Some(if zero then Finish else CopyInit) /\
 next common CopyInit zero=Some CopyLane /\
 next common CopyLane zero=Some(if zero then Decode else CopyLane) /\
 next common Decode zero=Some(if zero then Reject else Build) /\
 next common Build zero=Some Finish /\ next common Reject zero=Some Finish /\
 next strict Prepare zero=Some(if zero then ReturnStrict else Screen) /\
 next strict Screen zero=Some ReturnStrict /\
 next common Finish zero=None /\ next strict ReturnStrict zero=None.

Record prepare_chunk_contract : Prop := {
 common_image : image pc Common common=raw Common;
 strict_image : image pc Strict strict=raw Strict;
 relative_targets : image_layout /\ forallb (fits_jump pc Common common) common=true /\
   forallb (fits_jump pc Strict strict) strict=true /\
   forallb (fun j=>(0<=?table_offset j)&&(table_offset j<?2^16)) (seq 0 8)=true;
 decoder : Decode.Audit.decode_contract (pc DecodePair) (raw DecodePair)
   HelperBytes.address HelperBytes.symbol_bytes DecoderBytes.pow_pc Pow2.ObjectBytes.symbol_bytes;
 paired_call : decoder_handoff;
 branch_targets : exits;
 decoder_kernels : Decode.Image.kernel_image Decode.Program.code (pc DecodePair) (raw DecodePair)
   HelperBytes.address HelperBytes.symbol_bytes;
 builder : KeyTable.Audit.key_table_contract (pc Tables) (raw Tables) (pc DecodePair) (raw DecodePair)
   HelperBytes.address HelperBytes.symbol_bytes CachedBytes.address CachedBytes.symbol_bytes;
 filter_image : DalekPostHash.Caller.image Binding.pc DalekPostHash.Caller.Filter=raw Filter /\
   DalekPostHash.Queue.exact_image Decode.Program.code /\
   Kernels.carry Decode.Program.code=DalekPostHash.Keys.carry_code;
 preparation : forall mode p prior incoming slide table_scratch,
   placement p -> byte_memory(original p) -> scalar_inputs p prior slide ->
   (forall t,WordBounds.data_words(table_scratch t)) ->
   chunk_result mode p prior incoming slide table_scratch
}.
