(* Export only the typed kernel rows. Python supplies the bytes from the ELF. *)
From Coq Require Import List ZArith Strings.String Numbers.DecimalString.
From Machine Require Import Instructions.
From Machine Require ProgramLayout.
From Machine Require tests.CallerForms.
Require Import Program.
Import ListNotations.
Open Scope string_scope.

(* Fail the release conformance export if a scalar or control-flow form has
   no corresponding instruction in the native block probes. *)
Example native_caller_coverage : CallerForms.uncovered_caller_forms scalar_program = [].
Proof. vm_compute. reflexivity. Qed.

Definition signed n := NilZero.string_of_int (Z.to_int n).
Definition fields (i : instruction) :=
  let '(dst, op) := i in
  let args3 name a b := [name; decimal dst; decimal a; decimal b] in
  match op with
  | Copy a => ["vmovdqa64"; decimal dst; decimal a]
  | Load b d => ["vmovdqu64"; decimal dst; decimal b; signed d]
  | Xor a b => args3 "vpxorq" a b
  | Add a b => args3 "vpaddq" a b
  | Sub a b => args3 "vpsubq" a b
  | Mul a b => args3 "vpmullq" a b
  | And a b => args3 "vpandq" a b
  | Shl a n => args3 "vpsllq" a n
  | Shr a n => args3 "vpsrlq" a n
  | MaddMem hi a base d => [(if hi then "vpmadd52huq_mem" else "vpmadd52luq_mem"); decimal dst; decimal a; decimal base; signed d]
  | Madd hi a b => args3 (if hi then "vpmadd52huq" else "vpmadd52luq") a b
  end.
Fixpoint kernel_rows (pc : Z) (code : list instruction) : list string :=
  match code with
  | [] => []
  | i :: rest =>
      let size := List.length (encode i) in
      String.concat " " (signed pc :: decimal size :: fields i) ::
        kernel_rows (pc + Z.of_nat size) rest
  end.

Definition section_rows (s : ProgramLayout.section) :=
  match s with
  | ProgramLayout.Code b =>
      match ProgramLayout.body b with
      | [ProgramLayout.VectorCode id] =>
          kernel_rows (ProgramLayout.start b) (ProgramLayout.fragment_code scalar_program id)
      | _ => []
      end
  | _ => []
  end.

Definition exported :=
  let forms := CallerForms.caller_forms scalar_program in
  let counts := String.concat " " ["caller"; decimal (List.length forms);
                  decimal (List.length (nodup CallerForms.form_eq_dec forms))] in
  String.concat "|" (counts :: flat_map section_rows (ProgramLayout.sections scalar_program)).
Set Printing Width 10000.
Eval vm_compute in exported.
