From Coq Require Import List Bool ZArith.
From Machine Require Import execution.LinkedCalls memory.ByteMemory.
From Curve25519.group Require Import Affine.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.Decode Require Import Kernels Unpack.
From Ed25519Simd.Decode Require Image DecoderBytes HelperBytes Program.
From Ed25519Simd.Dalek Require Import Batch.
From Ed25519Simd.PostHash Require Import Product Staging.
From Ed25519Simd.Zip215 Require Import Schedule.
From Ed25519Simd.DalekPostHash Require Import Caller Binding Screen Keys Decoded Queue.
Local Open Scope Z_scope.
From Ed25519Simd.Zip215 Require ScatterTrace.
From Ed25519Simd.DalekPostHash Require ScatterBytes.

(* The base and public keys denote the points in the caller's tables.
   Metadata describes the eight lanes before weak-key filtering. *)
Record job := Job {
  digest_entry : cpu;
  ladder_entry : cpu;
  base : point;
  key : nat -> point;
  metadata : lanes
}.
Definition product b :=
  candidate (digest_entry b) (ladder_entry b) (base b) (key b).
Definition candidate_returns b q :=
  exists slide mid ip, observation false slide (digest_entry b) (ladder_entry b)
                                  mid q (base b) (key b) ip.
Definition filtered b :=
  let m := metadata b in
  Lanes (active m) (index m) (filter_keys (ladder_entry b) (eligible m)).

(* The same predicate governs every active output on both paths.
   strict_R w Q means w = compress Q and [8]Q is not the identity. *)
Definition accepts b w j :=
  eligible (metadata b) j = true /\
  multiple 8 (key b j) <> identity /\
  strict_R w (product b j).

(* The paired decoder takes the key chunk at ptr and R at ptr + 256. *)
Definition decoded_result dk := forall b flat ptr q pad init len out,
  byte_memory flat -> (pad < 4)%nat -> positions (metadata b) len ->
  candidate_returns b q ->
  let m := filtered b in
  let os := outputs dk flat ptr in
  exists mask,
    direct Decode.Program.code os (valid_mask dk flat ptr) (eligible m) q pad init = Some mask /\
    scatter m len mask out = Some (place (active m) 0 m (fun j => Z.testbit mask (Z.of_nat j)) out) /\
    forall j, (j < 8)%nat ->
      (eligible m j && Z.testbit mask (Z.of_nat j) = true <->
       accepts b (encoded flat (ptr + 256) j) j).

(* Each occupied slot contains the return of its own candidate call. *)
Definition flush_result k := forall n flat pts enc jobs pad init len out,
  (n <= 8)%nat -> Dalek.Audit.input_layout n pts enc -> byte_memory flat -> (pad < 4)%nat ->
  (forall i, (i < n)%nat ->
     candidate_returns (jobs i) (point_words flat pts i) /\ positions (metadata (jobs i)) len) ->
  let meta := fun i => filtered (jobs i) in
  exists bits,
    flush k flat pts enc pad init n meta len out = Some (0%nat, writes n meta bits out) /\
    forall i j, (i < n)%nat -> (j < 8)%nat ->
      (eligible (meta i) j && bits i j = true <->
       accepts (jobs i) (encoded flat (Batch.ptr enc i) j) j).

Definition push_result := forall b flat ptr n pad len out,
  byte_memory flat -> (n < 8)%nat -> (pad < 4)%nat -> positions (metadata b) len ->
  let m := filtered b in
  dispatch flat ptr n pad =
    Some (if screen flat ptr then RejectChunk else
          if Nat.eqb (S n) 8 then FlushFull else Buffered (S n)) /\
  (screen flat ptr = true ->
     scatter m len 0 out = Some (place (active m) 0 m (fun _ => false) out) /\
     forall j, (j < 8)%nat -> ~ accepts b (encoded flat ptr j) j).

Definition decoder_image dk := Decode.Image.kernel_image dk
  Decode.DecoderBytes.address Decode.DecoderBytes.symbol_bytes
  Decode.HelperBytes.address Decode.HelperBytes.symbol_bytes.

Record dalek_post_hash_contract : Prop := {
  wrapper_bytes : linked_image;
  scatter_writes : ScatterTrace.confined_prefix ScatterBytes.symbol_bytes;
  arithmetic_bytes : exact_image Decode.Program.code /\ Kernels.carry Decode.Program.code = carry_code;
  call_arguments : candidate_abi false /\ push_abi;
  branches : screening_flow /\
    next Decoded MatchX false false = Some (Local Done) /\
    next Decoded Reject false false = Some (Local Done) /\
    next Decoded Done false false = Some (External Scatter) /\
    next Flush Recompress false false = Some (Local SaveMask) /\
    next Flush SaveMask false false = Some (Local Score) /\
    next Filter SecondDifference false false = Some (Local KeysDone);
  candidate_existence : forall b slide,
    call_inputs false slide (digest_entry b) (ladder_entry b) (base b) (key b) ->
    (forall ip mid, reduce_call slide (digest_entry b) ip mid ->
       passes_digits (digest_entry b) (ladder_entry b) mid) ->
    exists q, candidate_returns b q;
  weak_key_filter : forall b j, valid_tables (ladder_entry b) (base b) (key b) -> (j < 8)%nat ->
    (eligible (filtered b) j = true <-> eligible (metadata b) j = true /\ multiple 8 (key b j) <> identity);
  cache_hit_push : push_result;
  cache_hit_flush : exists k, exact_image k /\ flush_result k;
  cache_miss_or_disabled : exists dk, decoder_image dk /\ decoded_result dk
}.
