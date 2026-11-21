From Coq Require Import List Bool ZArith Lia.
From Machine Require Import memory.ByteMemory.
From Curve25519.group Require Import Affine Representation PrimeField.
From Ed25519Simd.Dalek Require Import Batch.
From Ed25519Simd.Zip215 Require Import Staging Caller Binding Equation Calls Schedule.
Import ListNotations. Local Open Scope Z_scope.

Definition resolve_byte exact (slow:nat->bool->option Z) src :=
 match src with
 | ExactByte i=>Some(octet exact i)
 | CheckedByte start paired high=>option_map (fun word=>octet word (if high then 1 else 0))
     (slow start paired) end.

Fixpoint score (todo:stores) exact slow (meta:nat->lanes) len out :=
 match todo with []=>Some out | (i,src)::rest=>
 match resolve_byte exact slow src with None=>None | Some m=>
 match scatter (meta i) len m out with None=>None | Some o=>score rest exact slow meta len o end end end.

Definition execute fast decode flat pts enc n pad init_exact init_check matches meta len out :=
 let probes:=map matches (seq 0 n) in
 match probe 52 Count n 0 0 (fun i=>nth i probes false) with None=>None | Some use_exact=>
 match (if use_exact then exact_run fast flat pts enc pad init_exact n else Some 0) with
 | None=>None | Some m=>
 let pattern:=map (fun i=>octet m i=?255) (seq 0 n) in
 match run pattern with None=>None | Some todo=>
 score todo m (fun start paired=>checked_mask decode flat pts enc start paired pad init_check) meta len out end end end.

(* The output specification visits chunks, then active lanes, in input order.
   Padding is omitted, and the last active writer wins for repeated indices. *)
Definition expected n meta verdict out := fold_left (fun o i=>
 place (active(meta i)) 0 (meta i) (verdict i) o) (seq 0 n) out.
Definition encoded_at flat enc i j := Unpack.encoded flat (Batch.ptr enc i) j.

Definition flush_correct fast decode :=
 forall flat pts enc n Q pad init_exact init_check matches meta len out,
 (n<=8)%nat -> byte_memory flat -> Dalek.Audit.input_layout n pts enc -> (pad<4)%nat ->
 (forall i,(i<n)%nat -> candidate_chunk(point_words flat pts i)(Q i) /\ positions(meta i) len) ->
 exists final, execute fast decode flat pts enc n pad init_exact init_check matches meta len out=Some final /\
 exists verdict, (forall i j,(i<n)%nat -> (j<8)%nat -> (verdict i j=true <-> accepts (encoded_at flat enc i j)(Q i j))) /\
 final=expected n meta verdict out.

(* On a miss the FFI receives affine R from the Rust front end. The set bit
   supplies its unique decoded point. A clear bit means no such point exists. *)
Definition input_R raw valid j r :=
 if Z.testbit valid (Z.of_nat j) then exists R,
 encoded_point raw R /\ represents_point true r R /\
 residue (Edwards.cz r)=1%fp /\ forall P,encoded_point raw P -> P=R
 else forall R,~encoded_point raw R.

Definition direct_correct := forall q r Q raw valid meta len out pad init,
 (pad<4)%nat -> positions meta len -> Torsion.Audit.input_bounds q r ->
 (forall j,(j<8)%nat -> represents_point true (Wide51.point_values q j)(Q j) /\
  input_R (raw j) valid j (Wide51.point_values r j)) ->
 exists m final, torsion_run pad q r init=Some m /\
 scatter meta len (Z.land m valid) out=Some final /\
 exists verdict, (forall j,(j<8)%nat -> (verdict j=true <-> accepts (raw j)(Q j))) /\
 final=place (active meta) 0 meta verdict out.

Record zip215_contract : Prop := {
 caller_image : linked_image;
 staged_calls : candidate_abi /\ push_abi /\
   exit_of Enqueue=Jump Eq false (Entry Flush) /\ exit_of Queued=Ret /\
   exit_of DecodedCheck=Jump Always false (Entry Scatter);
 queue_occupancy : queue_lifecycle;
 candidate_result : product_correct;
 decoded_result : direct_correct;
 deferred_result : exists fast decode,
 Dalek.Audit.shared_image fast Decode.DecoderBytes.address Decode.DecoderBytes.symbol_bytes
 Decode.HelperBytes.address Decode.HelperBytes.symbol_bytes /\
 Decode.Image.kernel_image decode Decode.DecoderBytes.address Decode.DecoderBytes.symbol_bytes
 Decode.HelperBytes.address Decode.HelperBytes.symbol_bytes /\ flush_correct fast decode
}.
