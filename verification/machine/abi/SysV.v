From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks.
Import ListNotations.

(* Integer callee-saved registers in the SysV AMD64 convention.
   The return instruction advances RSP past the caller's return address. *)
Definition sysv_saved := [3;5;12;13;14;15]%nat.
Definition preserves_sysv (initial final:state) :=
 forall r,In r sysv_saved -> gpr(fst final)r=gpr(fst initial)r.
Definition restores_rsp (initial final:state) :=
 Some(gpr(fst final)4%nat)=option_map Ptr(pointer_at(fst initial)4 8%Z).

(* A successful call has one final state for its ABI, access, byte-memory,
   and arithmetic guarantees. Each certificate supplies its concrete predicates. *)
Record call_result p l initial final (access frame output : Prop) : Prop := {
 did_return : returns p l initial final;
 restored_stack : restores_rsp initial final;
 saved_registers : preserves_sysv initial final;
 allowed_access : access;
 byte_guarantee : frame;
 computed_output : output
}.
Arguments did_return {p l initial final access frame output} _.
Arguments restored_stack {p l initial final access frame output} _.
Arguments saved_registers {p l initial final access frame output} _.
Arguments allowed_access {p l initial final access frame output} _.
Arguments byte_guarantee {p l initial final access frame output} _.
Arguments computed_output {p l initial final access frame output} _.
