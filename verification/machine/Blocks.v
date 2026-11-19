From Coq Require Import List ZArith Bool.
From Machine Require Import Instructions.
From Machine Require ProgramLayout MachineState.
Import ListNotations.
Open Scope Z_scope.

(* Keep the layout and state definitions available through Machine.Blocks. *)
Include ProgramLayout.
Include MachineState.

(* Vector values never influence the supported scalar branches. A block can
   therefore compute the next PC and the ordered vector effects separately. *)
Inductive effect :=
| Read (dst : nat) (a : pointer) | Write (src : nat) (a : pointer)
| Broadcast (dst : nat) (n : Z) | ClearUpper
| Evaluate (fragment : nat) (bases : list (nat * pointer)).
Definition load_operands (code : list instruction) :=
 flat_map (fun i => match snd i with Load b d => [(b,d)] | _ => [] end) code.
Definition capture c bases := flat_map (fun b => match pointer_at c b 0 with
 | Some a => [(b,a)] | None => [] end) bases.

Definition exec_op p l c op : option (control * list effect) :=
 match op with
 | Mov32 d n => Some (set_gpr c d (Int (n mod 2^32)), [])
 | MovAbsRax n => Some (set_gpr c 0 (Int (n mod 2^64)), [])
 | BroadcastRax d => match gpr c 0%nat with Int n => Some (c,[Broadcast d n]) | _ => None end
 | LeaR8Rsp d => match pointer_at c 4 d with
                  | Some a => Some (set_gpr c 8 (Ptr a),[]) | None => None end
 | AdjustRsp sub n => match pointer_at c 4 (if sub then -n else n) with
   | Some a => Some (Control (rip c) (put (gpr c) 4 (Ptr a)) None (return_memory c),[])
   | None => None end
 | DecEcx => match gpr c 1%nat with
   | Int n => let v := (n-1) mod 2^32 in
     Some (Control (rip c) (put (gpr c) 1 (Int v)) (Some (v =? 0)) (return_memory c),[])
   | _ => None end
 | LoadZmm r b d => match pointer_at c b d with
   | Some a => if vector_ok l a false then Some (c,[Read r a]) else None | None => None end
 | StoreZmm r b d => match pointer_at c b d with
   | Some a => if vector_ok l a true then Some (c,[Write r a]) else None | None => None end
 | VectorCode id =>
   let loads := load_operands (fragment_code p id) in
   if forallb (fun bd => match pointer_at c (fst bd) (snd bd) with
        | Some a => vector_ok l a false | None => false end) loads then
     Some (c,[Evaluate id (capture c (nodup Nat.eq_dec (map fst loads)))]) else None
 | ZeroUpper => Some (c,[ClearUpper])
 | MovReg d s => Some (set_gpr c d (gpr c s),[])
 (* Pointer alignment uses a region whose physical origin is 64-byte aligned.
    Consumers must prove that placement condition; double4's scratch origin is
    the aligned frame base. Alignment changes flags, which are not consumed. *)
 | AlignRsp64 => match pointer_at c 4 0 with
   | Some (r,n) => Some (Control (rip c) (put (gpr c) 4 (Ptr (r,n-n mod 64)))
                           None (return_memory c),[])
   | None => None end
 | LeaR8Rsi d => match pointer_at c 6 d with
   | Some a => Some (set_gpr c 8 (Ptr a),[]) | None => None end
 end.

Fixpoint exec_body p l c ops := match ops with
 | [] => Some (c,[])
 | op::rest => match exec_op p l c op with
   | Some (c',e) => match exec_body p l c' rest with
     | Some (last,es) => Some (last,e++es) | None => None end | None => None end end.
(* Intel SDM vol. 2, CALL (near rel32), Jcc (JNE rel8) and RET (near).
   The signed displacement is relative to the end of the instruction.
   https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html *)
Definition transfer l c next e :=
 let jump t := Some (Control t (gpr c) (zf c) (return_memory c)) in
 match e with
 | Next => jump (At next)
 | JneRel8 d => match zf c with
      | Some zero => jump (At (if zero then next else next+d)) | None => None end
 | CallRel32 d => match pointer_at c 4 (-8) with
   | Some a => if return_ok l a then
     Some (Control (At (next+d)) (put (gpr c) 4 (Ptr a)) (zf c)
       (fun k => if ptr_eq k a then Some (At next) else return_memory c k)) else None
   | None => None end
 | PushRbp => match pointer_at c 4 (-8), gpr c 5%nat with
   | Some a, Int n => if return_ok l a then
       Some (Control (At next) (put (gpr c) 4 (Ptr a)) (zf c)
         (fun k => if ptr_eq k a then Some (SavedWord (stack_word n)) else return_memory c k))
       else None
   | _,_ => None end
 | PopRbp => match pointer_at c 4 0 with
   | Some a => if return_ok l a then match return_memory c a with
     | Some (SavedWord n) => Some (Control (At next)
         (put (put (gpr c) 4 (Ptr (offset a 8))) 5 (Int (stack_word n)))
         (zf c) (return_memory c))
     | _ => None end else None
   | None => None end
 | Ret => match pointer_at c 4 0 with
   | Some a => if return_ok l a then match return_memory c a with
     | Some t => Some (Control t (put (gpr c) 4 (Ptr (offset a 8))) (zf c) (return_memory c))
     | None => None end else None | None => None end
 end.

Definition block_control p l b c :=
 match exec_body p l c (body b) with
 | Some (c',es) => match transfer l c' (after p b) (terminator b) with
   | Some last => Some (last,es) | None => None end
 | None => None end.
Definition dispatch p l c := match rip c with
 | Caller | SavedWord _ => None
 | At n => match lookup (sections p) n with
   | Some b => block_control p l b c
   | None => None end end.

Definition apply_effect p s e := match e with
 | Read r a => register_write s r (memory s a)
 | Write r a => Data (zmm s) (fun k => if ptr_eq k a then fun j => zmm s j r else memory s k)
 | Broadcast r n => register_write s r (fun _ => n)
 | ClearUpper => Data (fun j r => if Nat.ltb r 16 && Nat.leb 2 j then 0 else zmm s j r) (memory s)
 | Evaluate id bases => Data (fun j => run (effective_load s bases j) (fragment_code p id) (zmm s j)) (memory s)
 end.
Definition effects p es s := fold_left (apply_effect p) es s.

Definition apply_result p d (result : option (control * list effect)) : option state :=
 match result with Some (c,es) => Some (c,effects p es d) | None => None end.
Definition execute_block p l b (s:state) := apply_result p (snd s) (block_control p l b (fst s)).
Definition step p l (s:state) := apply_result p (snd s) (dispatch p l (fst s)).
Inductive reaches p l : state -> state -> Prop :=
| here s : reaches p l s s
| more s t u : step p l s = Some t -> reaches p l t u -> reaches p l s u.
Definition returns p l s t := reaches p l s t /\ rip (fst t) = Caller.

(* A bounded search constructs a finite execution witness. Fuel is absent
   from the architectural step relation and from the return contract. *)
Fixpoint path fuel p l c : option (control * list effect) :=
 match rip c with Caller => Some (c,[]) | SavedWord _ => None | At _ => match fuel with
 | O => None | S n => match dispatch p l c with
   | Some (next,es) => match path n p l next with
     | Some (last,tail) => Some (last,es++tail) | None => None end
   | None => None end end end.
Lemma path_returns fuel p l c last es :
 path fuel p l c = Some (last,es) ->
 forall s, returns p l (c,s) (last,effects p es s).
Proof.
 revert c last es; induction fuel as [|n IH]; intros c last es H s;
 cbn [path] in H; destruct (rip c) eqn:PC; try discriminate;
 try (inversion H; subst; split; [constructor | exact PC]).
 destruct (dispatch p l c) as [[next prefix]|] eqn:D; try discriminate.
 destruct (path n p l next) as [[fin tail]|] eqn:T; try discriminate.
 inversion H; subst. unfold effects; rewrite fold_left_app.
 destruct (IH _ _ _ T (effects p prefix s)) as [R End].
 split; [eapply more; [unfold step;cbn;rewrite D;reflexivity|exact R]|exact End].
Qed.


Lemma returned_is_final p l s t :
 rip (fst s) = Caller -> reaches p l s t -> s = t.
Proof.
 intros End R. destruct R as [|s u t S R]; auto.
 unfold step,dispatch in S. rewrite End in S; discriminate.
Qed.

Theorem return_unique p l initial first second :
 returns p l initial first -> returns p l initial second -> first = second.
Proof.
 intros [R End]. revert second. induction R as [s|s t u S R IH];
 intros second [T E]; [eapply returned_is_final; eauto|].
 inversion T as [|s' t' u' S' R']; subst.
 - symmetry; eapply returned_is_final; [exact E|eapply more; eauto].
 - rewrite S in S'; inversion S'; subst. apply IH; [exact End|split;assumption].
Qed.
