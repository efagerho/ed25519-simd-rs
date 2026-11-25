From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls memory.FlatMemory memory.MemoryGeometry.
From Curve25519.group Require Import Affine Representation.
From ProofArithmetic Require Import Radix.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Import LinkedBytes Program Operands ScalarAction Execution Native Composition.
From Ed25519Simd.FullLadder Require StageEntry.
From Machine Require execution.MappedFetch.
From Ed25519Simd.LadderStep Require Audit LinkedBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition images := [(entry_pc,Z.of_nat(length symbol_bytes));
 (stage_pc,Z.of_nat(length Ed25519Simd.StageRound.ObjectBytes.symbol_bytes));
 (L.wrapper_pc,LA.wrapper_size);(L.double4_pc,Callees.dsize);(L.cached_pc,Callees.asize)].
Fixpoint separate (xs:list (Z*Z)) := match xs with nil=>True | (a,n)::t=>
 Forall (fun p=>disjoint a n (fst p) (snd p)) t /\ separate t end.
Definition pad_of s := regs s 4%nat mod 64.
Definition base_of s := regs s 4%nat+staging (pad_of s).
Definition external_ranges s := [(regs s 6%nat,64);(regs s 2%nat,273*120);
 (regs s 1%nat,512);(regs s 8%nat,512)] ++ map (fun j=>(SA.key_table s j,17*160)) (seq 0 8).
Record placement slide s : Prop := {
 entry_alignment : In (pad_of s) [8;24;40;56];
 frame_range : fits64 (regs s 4%nat-5032) 5041;
 point_stack : disjoint (regs s 7%nat) 1280 (regs s 4%nat-5032) 5040;
 child_layout : arena slide (regs s 7%nat) (base_of s);
 source_regions : forall a n,In (a,n) (external_ranges s) ->
   disjoint a n (regs s 7%nat) 1280 /\ disjoint a n (regs s 4%nat-5032) 5040;
 loaded_images : forall pc n,In (pc,n) images -> fits64 (slide+pc) n /\
   disjoint (slide+pc) n (regs s 7%nat) 1280 /\ disjoint (slide+pc) n (regs s 4%nat-5032) 5040
}.
(* The control interpreter checks the stack, saved registers, addresses,
   modes, call displacements and branches. Native call observations carry
   the entire accumulator and staged operands across each ABI boundary. *)
Definition execution slide s full out :=
 regs s 9%nat=bits full /\ exists ops cache, run full (pad_of s)=Some ops /\
 native_runs slide (regs s 7%nat) (base_of s) (slide+stage_pc) (pad_of s) s ops
  (ByteMemory.buffer_words (mem s) (regs s 7%nat),ByteMemory.buffer_words (mem s) (base_of s)) (out,cache).

Record full_ladder_contract : Prop := {
 wrapper_binding : image=symbol_bytes /\ valid=true /\ separate images;
 staging_certificate : SA.stage_contract Ed25519Simd.StageRound.ObjectBytes.symbol_bytes;
 step_certificate : LA.ladder_contract;
 first_stage_call : forall slide s c, placement slide s -> well_formed s ->
   MappedFetch.mapped (mem s) (slide+entry_pc) symbol_bytes ->
   exists u k,StageEntry.entered slide s c u k /\ StageEntry.entry_state slide s u;
 full_product : forall slide s full B A, placement slide s ->
   regs s 9%nat=bits full -> valid_inputs (slide+stage_pc) (pad_of s) s ->
   valid_tables s B A ->
   (exists out,execution slide s full out) /\
   forall out,execution slide s full out ->
     strict out /\ (forall j,(j<8)%nat ->
       represents_point full (point_values out j)
        (plus (scale (number 16 (digit_list s 1 j)) B)
              (scale (-number 16 (digit_list s 8 j)) (A j)))) /\
      (full=false -> zero_t out)
}.
