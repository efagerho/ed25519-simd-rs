From Coq Require Import List ZArith.
From Machine Require Import Blocks.
Import ListNotations.

(* Integer callee-saved registers in the SysV AMD64 convention.
   The return instruction advances RSP past the caller's return address. *)
Definition sysv_saved := [3;5;12;13;14;15]%nat.
Definition preserves_sysv (initial final:state) :=
 forall r,In r sysv_saved -> gpr(fst final)r=gpr(fst initial)r.
Definition restores_rsp (initial final:state) :=
 Some(gpr(fst final)4%nat)=option_map Ptr(pointer_at(fst initial)4 8%Z).
