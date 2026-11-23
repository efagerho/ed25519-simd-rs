From Coq Require Import List ZArith Bool.
From Machine Require Import isa.ProgramLayout.
From Machine Require execution.Blocks.
From Machine Require tests.Control tests.Mixed tests.Prologue tests.Aligned.
Import ListNotations.
Open Scope Z_scope.

(* For coverage, distinguish opcode, encoded length, GPR and address base,
   displacement sign (including zero), and branch direction. ZMM indices and
   immediate values share a form. Vector fragments have their own row tests. *)
Definition form := ((operation + exit) * nat)%type.
Definition scalar_form op :=
  match op with
  | Mov32 r _ => Mov32 r 0
  | MovAbsRax _ => MovAbsRax 0
  | MovRaxImm32 _ => MovRaxImm32 0
  | BroadcastRax _ => BroadcastRax 0
  | AdjustRsp sub _ => AdjustRsp sub 0
  | LeaR8Rsp d => LeaR8Rsp (Z.sgn d)
  | Test32 r _ => Test32 r 0 | Cmp32Imm8 r _ => Cmp32Imm8 r 0
  | DecEcx => DecEcx
  | LoadZmm _ base d => LoadZmm 0 base (Z.sgn d)
  | StoreZmm _ base d => StoreZmm 0 base (Z.sgn d)
  | VectorCode id => VectorCode id
  | ZeroUpper => ZeroUpper
  | MovReg d s => MovReg d s
  | AlignRsp64 => AlignRsp64
  | LeaR8Rsi d => LeaR8Rsi (Z.sgn d)
  end.

Definition op_forms p op : list form :=
  match op with
  | VectorCode _ => []
  | _ => [(inl (scalar_form op), length (op_bytes p op))]
  end.
Definition exit_forms e : list form :=
  let f := match e with
    | Next => Next | Ret => Ret | PushRbp => PushRbp | PopRbp => PopRbp
    | CallRel32 d => CallRel32 (Z.sgn d)
    | JneRel8 d => JneRel8 (Z.sgn d) | JeRel8 d => JeRel8 (Z.sgn d)
    | JmpRel8 d => JmpRel8 (Z.sgn d) | JmpRel32 d => JmpRel32 (Z.sgn d)
    end in
  match e with Next => [] | _ => [(inr f, length (exit_bytes e))] end.

Definition block_forms p b := flat_map (op_forms p) (body b) ++ exit_forms (terminator b).
Definition caller_forms p := flat_map (fun section =>
  match section with Code b => block_forms p b | Padding _ => [] end) (sections p).

(* Count forms only in blocks reached and successfully executed by a probe
   on its default inputs. Stop collecting when control returns to its caller. *)
Fixpoint exercised fuel p l c : list form :=
  match fuel, Blocks.rip c with
  | S n, Blocks.At pc =>
      match lookup (sections p) pc with
      | Some b =>
          match Blocks.block_control p l b c with
          | Some (next, _) => block_forms p b ++ exercised n p l next
          | None => [] end
      | None => [] end
  | _, _ => []
  end.

Definition form_eq_dec (a b : form) : {a = b} + {a <> b}.
Proof. unfold form. repeat decide equality. Defined.

Definition native_forms := Eval vm_compute in nodup form_eq_dec (
  flat_map (fun n => exercised 12 Control.flag_probe Control.probe_layout (Control.flag_entry n)) Control.counts ++
  flat_map (fun n => exercised 8 Control.branch_probe Control.probe_layout (Control.probe_entry n)) Control.counts ++
  flat_map (fun n => exercised 10 Mixed.mixed_probe Mixed.mixed_layout (Mixed.entry n)) Mixed.seeds ++
  exercised 1 Prologue.prologue_probe Prologue.prologue_layout Prologue.entry ++
  flat_map (fun n => exercised 8 Aligned.aligned_probe Aligned.aligned_layout (Aligned.entry n)) Aligned.seeds).

Definition uncovered_caller_forms p :=
  filter (fun f => if in_dec form_eq_dec f native_forms then false else true) (caller_forms p).
