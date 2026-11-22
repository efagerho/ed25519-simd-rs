From Coq Require Import List ZArith Bool Lia.
From Machine Require Import memory.ByteMemory execution.LinkedCalls.
From Curve25519.group Require Import Affine.
From Ed25519Simd.Dalek Require Import Batch Encoding.
From Ed25519Simd.Dalek Require Audit Object Schedule ObjectBytes.
From Ed25519Simd.Decode Require DecoderBytes HelperBytes Unpack.
From Ed25519Simd.SmallOrder Require EntryBytes.
From Ed25519Simd.PostHash Require Import Staging Lanes.
From Ed25519Simd.Zip215 Require Import Schedule.
From Ed25519Simd.DalekPostHash Require Import Caller Screen Decoded.
Import ListNotations. Local Open Scope Z_scope.

Inductive push_action := RejectChunk | Buffered (count:nat) | FlushFull.
Definition dispatch flat ptr n pad :=
 if screen flat ptr then Some RejectChunk else
 let st:=fold_left Staging.step push_ops (initial n pad true) in
 match occupancy st, next Push Enqueue (zf st) false with
 | Number z,Some(Local Queued)=>Some(Buffered (Z.to_nat z))
 | Number _,Some(External Flush)=>Some FlushFull | _,_=>None end.
Lemma dispatch_ok flat ptr n pad : (n<8)%nat -> (pad<4)%nat ->
 dispatch flat ptr n pad=Some(if screen flat ptr then RejectChunk else
 if Nat.eqb (S n) 8 then FlushFull else Buffered (S n)).
Proof.
 intros N P;unfold dispatch;destruct (screen flat ptr);[reflexivity|].
 do 8 (destruct n as [|n];[do 4 (destruct pad as [|pad];[vm_compute;reflexivity|]);lia|]);lia.
Qed.

Definition exact_run k flat pts enc pad init n := Dalek.Schedule.execute k flat pts enc
 (Dalek.Audit.small_call EntryBytes.address Decode.HelperBytes.address flat pts pad init) n.
(* R14 holds the remaining mask; the next chunk takes its low byte. The
   first failed scatter terminates the flush before any subsequent store. *)
Fixpoint drain count i (mask:Z) meta len out := match count with O=>Some out | S rest=>
 match scatter (meta i) len (mask mod 256) out with
 | None=>None | Some o=>
   if reaches Flush Score false false Advance &&
      reaches Flush Advance (Nat.eqb rest 0) false (match rest with O=>Restore | _=>Score end)
   then drain rest (S i) (Z.shiftr mask 8) meta len o else None end end.
Definition flush k flat pts enc pad init n meta len out :=
 match next Flush Count (Nat.eqb n 0) false with Some(Local Empty)=>Some (n,out) | Some(Local Recompress)=>
 let st:=Staging.step (initial n pad true) (Staging.ClearCount 7) in
 match occupancy st with Number z=>
 match exact_run k flat pts enc pad init n with None=>None | Some mask=>
 option_map (fun o=>(Z.to_nat z,o)) (drain n 0 mask meta len out) end
 | _=>None end | _=>None end.

Definition writes n meta verdict out := fold_left (fun o i=>
 place (active(meta i)) 0 (meta i) (verdict i) o) (seq 0 n) out.
Lemma drain_ok n start mask meta len verdict out :
 (forall i,(start<=i<start+n)%nat -> positions(meta i) len) ->
 (forall i j,(i<n)%nat -> (j<8)%nat ->
 Z.testbit mask (8*Z.of_nat i+Z.of_nat j)=verdict (start+i)%nat j) ->
 drain n start mask meta len out=Some(fold_left (fun o i=>
 place (active(meta i)) 0 (meta i) (verdict i) o) (seq start n) out).
Proof.
 revert start mask out;induction n;intros start mask out Pos Bits;[reflexivity|].
 cbn [drain seq fold_left].
 rewrite (scatter_lanes _ _ _ _ (verdict start) (Pos start ltac:(lia))).
 - assert (Go:reaches Flush Score false false Advance &&
      reaches Flush Advance (Nat.eqb n 0) false (match n with O=>Restore | _=>Score end)=true)
     by (destruct n;reflexivity).
   rewrite Go;apply IHn;[intros;apply Pos;lia|]. intros i j I J;rewrite Z.shiftr_spec by lia.
   replace (8*Z.of_nat i+Z.of_nat j+8) with (8*Z.of_nat(S i)+Z.of_nat j) by lia.
   replace (S start+i)%nat with (start+S i)%nat by lia;apply Bits;lia.
 - intros j J. assert (Lim:(j<8)%nat) by (destruct(Pos start ltac:(lia));lia).
   change 256 with (2^8);rewrite Z.mod_pow2_bits_low by lia.
   specialize(Bits 0%nat j ltac:(lia) Lim);rewrite Nat.add_0_r in Bits;exact Bits.
Qed.

Definition exact_image k := Dalek.Audit.shared_image k Decode.DecoderBytes.address Decode.DecoderBytes.symbol_bytes
 Decode.HelperBytes.address Decode.HelperBytes.symbol_bytes.
Local Opaque Dalek.Schedule.execute Dalek.Audit.small_call.
Lemma flush_ok : exists k, exact_image k /\ forall n flat pts enc Q pad init meta len out,
 (n<=8)%nat -> Dalek.Audit.input_layout n pts enc -> byte_memory flat -> (pad<4)%nat ->
 (forall i,(i<n)%nat -> valid_chunk(point_words flat pts i)(Q i) /\ positions(meta i) len) ->
 exists bits,flush k flat pts enc pad init n meta len out=Some (0%nat,writes n meta bits out) /\
 forall i j,(i<n)%nat -> (j<8)%nat -> (bits i j=true <-> strict_R (Unpack.encoded flat (ptr enc i) j)(Q i j)).
Proof.
 destruct(Dalek.Audit.recompress_result _ _ _ _ _ _ _ _ Dalek.Object.assembled_dalek_recompress_correct)
 as [k [Image [_ [_ Exact]]]]. exists k;split;[exact Image|].
 intros n flat pts enc Q pad init meta len out N Layout Bytes P Valid.
 destruct(Exact n flat pts enc Q pad init N Layout Bytes P ltac:(intros;apply Valid;auto))
 as [m [Run [_ Bits]]].
 exists(fun i j=>Z.testbit m (8*Z.of_nat i+Z.of_nat j));split;[|exact Bits].
 destruct n;[reflexivity|]. unfold flush;change (next Flush Count (Nat.eqb (S n) 0) false) with (Some(Local Recompress)).
 change (exact_run k flat pts enc pad init (S n)=Some m) in Run;rewrite Run.
 rewrite (drain_ok _ _ _ _ _ (fun i j=>Z.testbit m (8*Z.of_nat i+Z.of_nat j))).
 - reflexivity.
 - intros;apply Valid;lia.
 - reflexivity.
Qed.
