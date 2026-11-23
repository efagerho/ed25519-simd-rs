From Coq Require Import List ZArith Bool.
From Machine Require Import execution.Lane execution.Blocks isa.Instructions.
Import ListNotations. Local Open Scope Z_scope.

(* Expose each instruction of an Evaluate event, resolving only the memory
   operand it actually reads. This lets proofs regroup a dynamic trace into
   arithmetic kernels across scalar branches and internal calls. *)
Inductive action :=
| Vector (i:instruction) (address:option pointer)
| LoadCell (r:nat) (a:pointer) | StoreCell (r:nat) (a:pointer)
| Constant (r:nat) (n:Z) | UpperZero.

Definition resolve bases b d :=
  option_map (fun entry => offset (snd entry) d) (find (fun e => Nat.eqb (fst e) b) bases).
Definition vector_action bases (i:instruction) :=
  Vector i (match snd i with
    | Load b d | MaddMem _ _ b d => resolve bases b d | _ => None end).
Definition actions p e := match e with
  | Evaluate id bases => map (vector_action bases) (fragment_code p id)
  | Read r a => [LoadCell r a] | Write r a => [StoreCell r a]
  | Broadcast r n => [Constant r n] | ClearUpper => [UpperZero] end.
Definition trace p es := flat_map (actions p) es.

Definition perform j s a := match a with
  | Vector (dst,op) addr =>
    let load (_:nat) (_:Z) := match addr with Some ptr => cells s ptr | None => 0 end in
    Lane (put (registers s) dst (bits load (registers s) dst op)) (cells s)
  | LoadCell r a => Lane (put (registers s) r (cells s a)) (cells s)
  | StoreCell r a => Lane (registers s) (fun k => if ptr_eq k a then registers s r else cells s k)
  | Constant r n => Lane (put (registers s) r n) (cells s)
  | UpperZero => Lane (fun r => if Nat.ltb r 16 && Nat.leb 2 j then 0 else registers s r) (cells s)
  end.

Lemma vectors_exact j bases code regs mem :
  fold_left (perform j) (map (vector_action bases) code) (Lane regs mem) =
  Lane (run (lane_load (Lane regs mem) bases) code regs) mem.
Proof.
 revert regs; induction code as [|[dst op] tail IH]; intro regs; [reflexivity|].
 cbn [map fold_left run]; destruct op; cbn [vector_action snd perform cells registers];
 rewrite IH; try reflexivity;
 cbn [bits]; unfold resolve, lane_load; cbn [cells]; destruct (find _ bases) as [[gpr_number resolved_pointer]|]; reflexivity.
Qed.

Lemma actions_exact p j e s :
  fold_left (perform j) (actions p e) s = lane_effect p j s e.
Proof. destruct e,s; try reflexivity; apply vectors_exact. Qed.

Lemma trace_exact p j es s :
  fold_left (perform j) (trace p es) s = lane_effects p j es s.
Proof.
 revert s; induction es as [|e es IH]; intro s; [reflexivity|].
 unfold trace; cbn [flat_map]; rewrite fold_left_app, actions_exact; apply IH.
Qed.

Theorem equivalent_trace p es q fs : trace p es = trace q fs ->
 forall j s, lane_effects p j es s = lane_effects q j fs s.
Proof. intros E j s; now rewrite <-!trace_exact,E. Qed.
