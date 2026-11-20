From Coq Require Import List Bool ZArith Strings.String.
From Machine Require Import execution.Blocks isa.IntelSyntax tests.model.Oracle.
Import ListNotations.
Open Scope Z_scope.

(* Two distinct inputs, one output and a private stack. The two loads through
   R8 make both LEA encodings observable. High ZMM registers retain all lanes
   across VZEROUPPER, while seeded low registers expose its clearing effect. *)
Definition prologue_probe := assemble [
 ScalarBlock 0 ops[
   sub rsp, 1928;
   movabs rax, 0xfedcba9876543210;
   vpbroadcastq zmm29, rax;
   mov eax, 19;
   vpbroadcastq zmm28, rax;
   mov ecx, 4294967295;
   vmovdqu64 zmm16, zmmword ptr [rsi];
   vmovdqu64 zmm17, zmmword ptr [rsi + 64];
   vmovdqu64 zmm18, zmmword ptr [rdx];
   vmovdqu64 zmm19, zmmword ptr [rdx + 64];
   vmovdqu64 zmmword ptr [rsp], zmm17;
   vmovdqu64 zmmword ptr [rsp + 640], zmm19;
   lea r8, [rsp];
   vmovdqu64 zmm20, zmmword ptr [r8];
   lea r8, [rsp + 640];
   vmovdqu64 zmm21, zmmword ptr [r8];
   vmovdqu64 zmm22, zmmword ptr [rsp];
   vmovdqu64 zmm23, zmmword ptr [rsp + 640];
   vmovdqu64 zmmword ptr [rdi], zmm20;
   vmovdqu64 zmmword ptr [rdi + 64], zmm21;
   add rsp, 1928;
   vzeroupper ] ends[ ret ]].

Example prologue_layout_valid : valid_program prologue_probe = true.
Proof. reflexivity. Qed.

(* Region 0 holds the stack. Its 30 vector cells end eight bytes before the
   return slot at 1928. Regions 1..3 each have a guard, two data cells and a guard. *)
Definition prologue_layout : layout := fun r cell =>
 if Nat.eqb r 0 then
   if (0 <=? cell) && (cell <? 30) then WriteVector
   else if cell =? 30 then ReturnWords 2 else Unmapped
 else if (1 <=? cell) && (cell <=? 2) then
   match r with 1%nat => WriteVector | 2%nat | 3%nat => ReadVector | _ => Unmapped end
 else Unmapped.

Definition entry := Control (At 0)
 (fun r => match r with
  | 1%nat => Int (2^64-1) | 4%nat => Ptr (0%nat,1928)
  | 7%nat => Ptr (1%nat,64) | 6%nat => Ptr (2%nat,64) | 2%nat => Ptr (3%nat,64)
  | _ => Unknown end)
 None (fun a => if ptr_eq a (0%nat,1928) then Some Caller else None).

Definition initial_data seed := Data (initial_zmm seed)
 (fun a j =>
    let '(r, disp) := a in
    (* The stack snapshot starts at -64 (one guard cell below the frame). *)
    let first := if Nat.eqb r 0 then 256 + 8 else 504 + 32 * (Z.of_nat r - 1) in
    initial_word seed (first + disp / 8 + Z.of_nat j)).

Definition prologue_result seed :=
 match path 1 prologue_probe prologue_layout entry with
 | Some (c, es) =>
   match rip c, Blocks.gpr c 4%nat, Blocks.gpr c 0%nat, Blocks.gpr c 1%nat, Blocks.gpr c 8%nat with
   | Caller, Ptr (O,1936), Int ax, Int cx, Ptr (O,disp) =>
     let d := effects prologue_probe es (initial_data seed) in
     let cell r n := map (memory d (r,64*n)) (seq 0 8) in
     [seed;ax;cx;disp] ++
     flat_map (fun r => map (fun j => Blocks.zmm d j r) (seq 0 8)) (seq 0 32) ++
     flat_map (fun i => cell 0%nat (Z.of_nat i-1)) (seq 0 31) ++
     flat_map (fun r => flat_map (fun i => cell r (Z.of_nat i)) (seq 0 4)) (seq 1 3)
   | _, _, _, _, _ => [] end
 | None => [] end.

Definition seeds := probe_seeds.
Definition prologue_report inputs := String.concat "|"%string
 (numbers (image prologue_probe) :: map (fun seed => numbers (prologue_result seed)) inputs).
