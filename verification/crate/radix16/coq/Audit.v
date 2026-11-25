From Machine Require execution.LocatedEvents execution.StoreInstructions memory.PackedWrites memory.WriteTrace.
From Coq Require Import List ZArith.
From Curve25519 Require Import SignedRadix16.
From Machine Require Import isa.ProgramLayout execution.LinkedCalls execution.Packed
  memory.FlatMemory memory.ByteMemory memory.MemoryGeometry execution.WordSemantics abi.SysV.
From Ed25519Simd.Scalar Require Import ScalarSpec ScalarABI ScalarBytes.
From Ed25519Simd.Scalar Require Program.
From Ed25519Simd.Radix16 Require Import Program.
Import ListNotations. Local Open Scope Z_scope.

Definition image pc target :=
  option_map (fun prefix => prefix ++ flat_map encode tail ++ encoding 0 Return)
             (assemble pc [Save 7; Invoke target; Restore 7]).
Definition size (bs : list Z) := Z.of_nat (length bs).

(* RSP points to an eight-byte return address. The saved RDI and the nested
   return address occupy the sixteen bytes immediately below it. *)
Record placement sp dst src pc n helper m : Prop := {
  stack_range : fits64 (sp - 16) 25;
  stack_alignment : sp mod 16 = 8;
  dst_range : fits64 dst 512;
  src_range : fits64 src 512;
  buffers_apart : disjoint dst 512 src 512;
  dst_stack : disjoint dst 512 (sp - 16) 24;
  src_stack : disjoint src 512 (sp - 16) 24;
  code_ranges : forall a len, In (a, len) [(pc, n); (helper, m)] ->
    fits64 a len /\ disjoint dst 512 a len /\ disjoint src 512 a len /\
    disjoint (sp - 16) 24 a len
}.

(* The reducer ABI numbers its stack, output and input regions 0, 1 and 2. *)
Definition location pc s :=
  Placement (fun r => match r with
                      | 0%nat => regs s 4%nat
                      | 1%nat => regs s 7%nat
                      | _ => regs s 6%nat
                      end)
            pc (read_word (mem s) (regs s 4%nat)).

Definition reduce pc s ip out :=
  let loc := location pc s in
  callee_returns Ed25519Simd.Scalar.Program.scalar_program abi_layout loc
    (entry_from_bytes loc (regs s) (vectors s) (flag s) (mem s)) (mem s) ip out.

(* CALL decodes its rel32 displacement. The reducer must resume at the POP
   at pc+6 before the straight-line vector tail and the final RET execute. *)
Definition run slide pc target n entry ip out :=
  let saved := snd (caller_step slide pc (Save 7) entry) in
  let '(dest, invoked) := caller_step slide (pc + 1) (Invoke target) saved in
  dest = slide + target /\
  exists mid,
    reduce dest invoked (word (slide + (pc + 6))) mid /\
    let resumed := snd (caller_step slide (pc + 6) (Restore 7) mid) in
    caller_step slide (pc + n - 1) Return (execute 8 tail resumed) = (ip, out).

(* A located execution of the scalar helper, followed by the wrapper's actual
   packed tail. Both consume the byte memory of their immediate predecessor. *)
Definition child_events pc s ws := let loc:=location pc s in
 let initial:=entry_from_bytes loc (regs s) (vectors s) (flag s) (mem s) in
 exists fuel final es,LocatedEvents.run pc fuel Ed25519Simd.Scalar.Program.scalar_program abi_layout
    (fst initial)=Some(final,es) /\
 ws=LocatedEvents.stores Ed25519Simd.Scalar.Program.scalar_program loc (snd initial) es.
Definition traced slide pc target n entry ip out ws :=
 let saved:=snd (caller_step slide pc (Save 7) entry) in
 let '(dest,invoked):=caller_step slide (pc+1) (Invoke target) saved in
 let own:=StoreInstructions.caller_stores slide pc (Save 7) entry ++
          StoreInstructions.caller_stores slide (pc+1) (Invoke target) saved in
 dest=slide+target /\ exists mid child,
 reduce dest invoked (word (slide+(pc+6))) mid /\ child_events dest invoked child /\
 let resumed:=snd (caller_step slide (pc+6) (Restore 7) mid) in
 caller_step slide (pc+n-1) Return (execute 8 tail resumed)=(ip,out) /\
 ws=own++child++PackedWrites.trace (slide+pc+7) resumed Packed.initial tail.

Definition signed_digits m dst lane :=
  map (fun k => signed_byte (m (dst + 64 * Z.of_nat lane + Z.of_nat k)))
      (seq 0 64).
Definition writable sp dst x := dst <= x < dst + 512 \/ sp - 16 <= x < sp.

Record digest_contract pc bs target callee_bytes : Prop := {
  wrapper_binding : image pc target = Some bs /\ forallb (valid 8) tail = true;
  reducer_binding : Blocks.image Ed25519Simd.Scalar.Program.scalar_program = callee_bytes;
  separate_code : disjoint pc (size bs) target (size callee_bytes);
  initializes_output : forall lane, (lane < 8)%nat ->
    exists row, stores (fold_left step tail initial) lane = Some row;
  trace_unique : forall slide entry ip out xs ys,
    traced slide pc target (size bs) entry ip out xs -> traced slide pc target (size bs) entry ip out ys -> xs=ys;
  write_footprint : forall slide entry ip out,
    let sp:=regs entry 4%nat in let dst:=regs entry 7%nat in
    placement sp dst (regs entry 6%nat) (slide+pc) (size bs) (slide+target) (size callee_bytes) ->
    well_formed entry -> run slide pc target (size bs) entry ip out ->
    exists ws,traced slide pc target (size bs) entry ip out ws /\
      (forall x,mem out x=WriteTrace.replay (mem entry) ws x) /\
      forall pre rest,ws=pre++rest -> WriteTrace.confined (writable sp dst) pre;
  run_correct : forall slide entry,
    let sp := regs entry 4%nat in
    let dst := regs entry 7%nat in
    let src := regs entry 6%nat in
    placement sp dst src (slide + pc) (size bs) (slide + target) (size callee_bytes) ->
    well_formed entry ->
    let ret := read_word (mem entry) sp in
    exists out,
      run slide pc target (size bs) entry ret out /\
      (forall ip other, run slide pc target (size bs) entry ip other -> ip = ret /\ other = out) /\
      regs out 4%nat = sp + 8 /\
      (forall r, In r sysv_saved -> regs out r = regs entry r) /\
      preserved (fun x => ~ writable sp dst x) (mem entry) (mem out) /\
      well_formed out /\
      (forall lane, (lane < 8)%nat ->
        let ds := signed_digits (mem out) dst lane in
        Forall (fun d => -8 <= d < 8) ds /\
        number 16 ds = lane_input (ByteMemory.buffer_words (mem entry) src) lane mod L)
}.
