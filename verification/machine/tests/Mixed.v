From Coq Require Import List Bool ZArith Strings.String.
From Machine Require Import execution.Blocks isa.IntelSyntax tests.model.Oracle.
Import ListNotations.
Open Scope Z_scope.

Local Notation "'.Lloop'" := (0%Z) (in custom intel_label at level 0).
Definition mixed_probe := assemble [
 VectorBlock label[ .Lloop ] vecs[
   vmovdqu64 zmm0, zmmword ptr [rdi + 64];
   vpaddq zmm31, zmm0, zmm31;
   vpmadd52luq zmm31, zmm31, zmm17 ] FallThrough;
 ScalarBlock 0x13 ops[
   vmovdqu64 zmmword ptr [rdi + 64], zmm31;
   dec ecx ] FallThrough;
 VectorBlock 0x1c vecs[ vpaddq zmm2, zmm2, zmm31 ] ends[ jne .Lloop ];
 ScalarBlock 0x24 ops[ vmovdqu64 zmm1, zmmword ptr [rdi + 64] ] ends[ ret ]].

Example mixed_layout_valid : valid_program mixed_probe = true.
Proof. reflexivity. Qed.

(* Region 0 holds the return PC. In region 1 only the middle vector cell
   is writable. The native harness also snapshots the two adjacent cells. *)
Definition mixed_layout : layout := fun r cell =>
 if Nat.eqb r 0 then (if cell =? 0 then ReturnWords 2 else Unmapped)
 else if Nat.eqb r 1 then
   if cell =? 1 then WriteVector else if (cell =? 0) || (cell =? 2) then ReadVector else Unmapped
 else Unmapped.
Definition entry seed := Control (At 0)
 (fun r => match r with
 | 1%nat => Int (1 + seed mod 3) | 4%nat => Ptr (0%nat,8)
 | 7%nat => Ptr (1%nat,0) | _ => Unknown end)
 None (fun a => if ptr_eq a (0%nat,8) then Some Caller else None).

Definition initial_data seed := Data (initial_zmm seed)
 (fun a j => initial_word seed (256 + 8*(snd a / 64) + Z.of_nat j)).

Definition mixed_result seed :=
 match path 10 mixed_probe mixed_layout (entry seed) with
 | Some (c,es) =>
   match rip c, Blocks.gpr c 4%nat, Blocks.gpr c 1%nat, zf c with
   | Caller, Ptr (O,16), Int n, Some zero =>
     let d := effects mixed_probe es (initial_data seed) in
     [seed; n; if zero then 1 else 0] ++
     flat_map (fun r => map (fun j => Blocks.zmm d j r) (seq 0 8)) (seq 0 32) ++
     flat_map (fun cell => map (memory d (1%nat,64*Z.of_nat cell)) (seq 0 8)) (seq 0 3)
   | _, _, _, _ => [] end
 | None => [] end.

Definition seeds := probe_seeds.
Example mixed_returns : forall seed, In seed seeds -> List.length (mixed_result seed) = 283%nat.
Proof. intros seed H. repeat (destruct H as [<-|H]; [reflexivity|]). contradiction. Qed.

Definition mixed_report inputs := String.concat "|"%string
 (numbers (image mixed_probe) :: map (fun n => numbers (mixed_result n)) inputs).
