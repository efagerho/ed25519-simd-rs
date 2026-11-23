From Coq Require Import List ZArith Strings.String.
From Machine Require Import execution.Blocks isa.IntelSyntax tests.model.Oracle.
Import ListNotations.
Open Scope Z_scope.

(* The callee decrements ECX. JNE in its caller consumes the resulting ZF. *)
Local Notation "'.Ltaken'" := (13%Z) (in custom intel_label at level 0).
Local Notation "'.Lcallee'" := (19%Z) (in custom intel_label at level 0).
Definition branch_probe := assemble [
 ScalarBlock 0 [] ends[ call .Lcallee ];
 ScalarBlock 5 [] ends[ jne .Ltaken ];
 ScalarBlock 7 ops[ mov eax, 0 ] ends[ ret ];
 ScalarBlock label[ .Ltaken ] ops[ mov eax, 1 ] ends[ ret ];
 ScalarBlock label[ .Lcallee ] ops[ dec ecx ] ends[ ret ]].
Definition probe_entry count := Control (At 0)
 (fun r => match r with 1%nat => Int count | 4%nat => Ptr (0%nat,8) | _ => Unknown end)
 None (fun a => if ptr_eq a (0%nat,8) then Some Caller else None).
Definition probe_layout : layout := fun _ cell => if cell =? 0 then ReturnWords 3 else Unmapped.
Definition probe_result n := match path 8 branch_probe probe_layout (probe_entry n) with
 | Some (c,[]) => match rip c, gpr c 0%nat, gpr c 1%nat, zf c, gpr c 4%nat with
   | Caller, Int branch, Int counter, Some zero, Ptr (O,16) =>
       [n;branch;counter;if zero then 1 else 0]
   | _,_,_,_,_ => [] end
 | _ => [] end.
Definition counts := [0;1;2;2^31;2^32-1;2^32;2^32+1;2^64-1].
Definition probe_report inputs := String.concat "|"%string
 (numbers (image branch_probe) :: map (fun n => numbers (probe_result n)) inputs).

Example branch_boundaries :
 valid_program branch_probe = true /\
 map probe_result [0;1;2;2^32+1] =
 [[0;1;2^32-1;0];[1;0;0;1];[2;1;1;0];[2^32+1;0;0;1]].
Proof. vm_compute; auto. Qed.
Example reject_mid_instruction :
 valid_program (Program [] [Code (Block 0 [] (JneRel8 (-1))); Code (Block 2 [] Ret)]) = false.
Proof. reflexivity. Qed.
Example reject_call_over_data :
 dispatch branch_probe (fun _ _ => WriteVector) (probe_entry 1) = None.
Proof. reflexivity. Qed.

(* Exercise sign extension, 32-bit truncation, TEST, and each PC-relative
   transfer width used by the two-entry point routines. *)
Definition flag_probe := assemble [
 ScalarBlock 0 [Mov32 0 0; Test32 1 3] (JeTo 29);
 ScalarBlock 13 [Cmp32Imm8 2 (-1)] (JeTo 33);
 ScalarBlock 18 [Test32 2 1] (JeTo 29);
 ScalarBlock 26 [Cmp32Imm8 1 4] FallThrough;
 ScalarBlock 29 [] (JumpTo true 39);
 LiteralPadding [0x90;0x90];
 ScalarBlock 33 [Mov32 0 1] FallThrough;
 ScalarBlock 38 [] Return;
 ScalarBlock 39 [] (JumpTo false 38)].
Definition flag_entry n := Control (At 0)
 (fun r => match r with 1%nat | 2%nat => Int n | 4%nat => Ptr (0%nat,8) | _ => Unknown end)
 None (fun a => if ptr_eq a (0%nat,8) then Some Caller else None).
Definition flag_row n := match path 12 flag_probe probe_layout (flag_entry n) with
 | Some (c,[]) => match rip c, gpr c 0%nat,zf c with
   | Caller,Int result,Some zero => [n;result;if zero then 1 else 0] | _,_,_=>[] end
 | _=>[] end.
Definition flag_report inputs := String.concat "|"%string
 (numbers (image flag_probe) :: map (fun n => numbers (flag_row n)) inputs).
Example flag_probe_checked : valid_program flag_probe=true /\
  map flag_row [0;1;2;2^32-1;2^32+1] =
  [[0;0;1];[1;0;0];[2;0;1];[2^32-1;1;1];[2^32+1;0;0]].
Proof. vm_compute; auto. Qed.
