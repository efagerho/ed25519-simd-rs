From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import Edwards group.Representation.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.Blocks abi.SysV execution.LinkedCalls memory.FlatMemory memory.ByteMemory
 execution.WordBounds memory.MemoryGeometry execution.ScalarRefinement.
From Ed25519Simd.Double4 Require Double4ABI Double4Memory Double4Spec.
From Ed25519Simd.CachedAdd Require CachedAddABI CachedAddMemory CachedAddSpec.
From Ed25519Simd.LadderStep Require Import LinkedBytes Callees Schedule.
Import ListNotations. Open Scope Z_scope.

Local Notation RCX := (1%nat).
Local Notation RDX := (2%nat).
Local Notation RBX := (3%nat).
Local Notation RSP := (4%nat).
Local Notation RSI := (6%nat).
Local Notation RDI := (7%nat).
Local Notation R12 := (12%nat).
Local Notation R13 := (13%nat).

Definition prologue := [Save RBX; Save R12; Save R13; Copy RBX RDI; Copy R12 RSI; Copy R13 RDX].
Definition epilogue := [Restore R13; Restore R12; Restore RBX; Return].
Definition program := prologue ++ [
  Invoke double4_pc;
  Copy RDI RBX; Copy RSI R12; Immediate RDX 0; Immediate RCX 0; Invoke (add_target cached_pc false false);
  Copy RDI RBX; Invoke double4_pc;
  Copy RDI RBX; LeaSIB RSI R12 1280] ++ affine_setup ++ [Invoke (add_target cached_pc true true);
  Copy RDI RBX; LeaSIB RSI R12 2240; Copy RDX R13; Immediate RCX 0; Invoke (add_target cached_pc false false)
] ++ epilogue.

Definition wrapper_size := Z.of_nat (length symbol_bytes).

(* The aligned scratch origin and padding describe the space below the
   caller's RSP. All callee frames occupy the same reusable interval. *)
Record placement_ok slide scratch pad point cache : Prop := {
 padding_ok : PointFrame.permitted_padding pad;
 scratch_aligned : scratch mod 64=0;
 point_aligned : point mod 64=0;
 cache_aligned : cache mod 64=0;
 stack_fits : fits64 (scratch-16) (1345+pad);
 point_fits : fits64 point 1280;
 cache_fits : fits64 cache 3520;
 point_stack : disjoint point 1280 (scratch-16) (1344+pad);
 cache_stack : disjoint cache 3520 (scratch-16) (1344+pad);
 cache_point : disjoint cache 3520 point 1280;
 code_regions : forall pc size, In (pc,size)
   [(wrapper_pc,wrapper_size);(double4_pc,dsize);(cached_pc,asize)] ->
   fits64 (slide+pc) size /\ disjoint point 1280 (slide+pc) size /\
   disjoint cache 3520 (slide+pc) size /\
   disjoint (scratch-16) (1344+pad) (slide+pc) size
}.
Definition writable scratch pad point x :=
 point<=x<point+1280 \/ scratch-16<=x<scratch+1320+pad.
Definition result_value full initial point cache j :=
 ladder_formula full (Wide51.point_values(buffer_words initial point)j)
  (cache_values false (buffer_words initial cache) j) (cache_values true (buffer_words initial (cache+1280)) j)
  (cache_values false (buffer_words initial (cache+2240)) j).

Definition group_result full before after point cache :=
 forall j P Odd Base Even, (j<8)%nat ->
 represents_xyz (point_values (buffer_words before point) j) P ->
 represents_cache (cache_values false (buffer_words before cache) j) Odd ->
 represents_cache (cache_values true (buffer_words before (cache+1280)) j) Base ->
 represents_cache (cache_values false (buffer_words before (cache+2240)) j) Even ->
 represents_point full (point_values (buffer_words after point) j)
   (ladder_sum P Odd Base Even).

Definition separate_images :=
 disjoint wrapper_pc wrapper_size double4_pc dsize /\ disjoint wrapper_pc wrapper_size cached_pc asize /\
 disjoint double4_pc dsize cached_pc asize.

Record ladder_result (execute : Z -> cpu -> Prop) caller scratch pad point cache full entry out : Prop := {
 returned : execute caller out;
 unique_return : forall ip other, execute ip other -> ip = caller /\ other = out;
 restored_stack : regs out RSP = regs entry RSP + 8;
 saved_registers : forall r, In r sysv_saved -> regs out r = regs entry r;
 byte_frame : preserved (fun x => ~ writable scratch pad point x) (mem entry) (mem out);
 reduced_output : strict (buffer_words (mem out) point);
 coordinate_result : has_value (buffer_words (mem out) point) (result_value full (mem entry) point cache);
 omitted_t_zero : full = false -> forall i j, (i < 5)%nat -> (j < 8)%nat ->
   Wide51.cell (buffer_words (mem out) point) (15+i)%nat j = 0;
 edwards_sum : group_result full (mem entry) (mem out) point cache
}.

Arguments returned {execute caller scratch pad point cache full entry out} _.

(* The caller supplies runtime placement. All three byte bindings are conclusions. *)
Record ladder_contract : Prop := {
 wrapper_matches : assemble wrapper_pc program = Some symbol_bytes;
 double_matches : doubling_image=doubling_bytes;
 cached_matches : addition_image=addition_bytes;
 images_disjoint : separate_images;
 run_ladder :
  forall slide scratch pad point cache full entry,
    placement_ok slide scratch pad point cache -> well_formed entry ->
    regs entry RSP = scratch + 1320 + pad ->
    regs entry RDI = point -> regs entry RSI = cache ->
    regs entry RDX = CachedAddABI.flag_word full ->
    Wide51.loose_xyz (buffer_words (mem entry) point) ->
    cache_bounds false (buffer_words (mem entry) cache) ->
    cache_bounds true (buffer_words (mem entry) (cache + 1280)) ->
    cache_bounds false (buffer_words (mem entry) (cache + 2240)) ->
    let execute := runs (dispatch (slide + double4_pc) (slide + cached_pc) scratch pad)
                        slide wrapper_pc program entry in
    let caller := read_word (mem entry) (regs entry RSP) in
    exists out, ladder_result execute caller scratch pad point cache full entry out
}.
