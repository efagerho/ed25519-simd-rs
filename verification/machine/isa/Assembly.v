From Coq Require Import List ZArith.
From Machine Require Import isa.Instructions isa.ProgramLayout.
Import ListNotations.
Open Scope Z_scope.

Inductive ending := FallThrough | Return | CallTo (target:Z) | JneTo (target:Z) | PushFrame | PopFrame
| JeTo (target:Z) | JumpTo (short:bool) (target:Z).

Inductive source_section :=
| ScalarBlock (pc:Z) (ops:list operation) (last:ending)
| VectorBlock (pc:Z) (ops:list instruction) (last:ending)
| LiteralPadding (bytes:list Z).

Definition assemble_block p pc ops last :=
  let next e := after p (Block pc ops e) in
  let e := match last with
    | FallThrough => Next | Return => Ret | PushFrame => PushRbp | PopFrame => PopRbp
    | CallTo target => CallRel32 (target - next (CallRel32 0))
    | JeTo target => JeRel8 (target - next (JeRel8 0))
    | JumpTo true target => JmpRel8 (target - next (JmpRel8 0))
    | JumpTo false target => JmpRel32 (target - next (JmpRel32 0))
    | JneTo target => JneRel8 (target - next (JneRel8 0))
    end in
  Code (Block pc ops e).

Fixpoint assemble_sections p next_fragment source :=
  match source with
  | [] => []
  | ScalarBlock pc ops last :: rest =>
      assemble_block p pc ops last :: assemble_sections p next_fragment rest
  | VectorBlock pc _ last :: rest =>
      assemble_block p pc [VectorCode next_fragment] last :: assemble_sections p (S next_fragment) rest
  | LiteralPadding bytes :: rest => Padding bytes :: assemble_sections p next_fragment rest
  end.

Definition assemble source :=
  let fragments := flat_map (fun s => match s with VectorBlock _ ops _ => [ops] | _ => [] end) source in
  Program fragments (assemble_sections (Program fragments []) 0%nat source).
