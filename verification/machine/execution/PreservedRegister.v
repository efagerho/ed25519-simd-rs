From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics
 execution.ScalarBytes execution.MappedFetch execution.StoreInstructions.
From Machine Require isa.VectorMoves isa.IndexedLoad execution.IndexedLoads.
Import ListNotations. Local Open Scope Z_scope.

(* A sufficient instruction-level test that r survives. A decoded branch
   may still choose any target and all implicit RSP writes are included. *)
Definition keeps r op := let other d:=negb (Nat.eqb d r) in match op with
 | AndImmediate d _ | Load64 d _ | Load8 d _ | Zero32 d | And8 d _ | Inc d | Imm32 d _ | CopyG d _
 | LeaG d _ | Sub64 d _ | Add32 d _ | Add64 d _ | MoveBelow d _ | Copy32 d _=>other d
 | OneEax | ShrEax=>other 0%nat
 | SaveG _ | CallRelative _ | Ret=>other 4%nat
 | RestoreG d=>other 4%nat && other d
 | VectorMove (VectorMoves.Input i)=>match i with
   | IndexedLoad.LoadZ _ _ | IndexedLoad.LoadY _ _ | IndexedLoad.InsertY _ _ _ _ | IndexedLoad.UnpackWords _ _ _ _
   | IndexedLoad.ShuffleWords _ _ _ _=>true | _=>false end
 | _=>true end.

Lemma step_keeps r o off n op s c t ws : keeps r op=true ->
 step o off n op s c=Some(t,ws) -> regs(cpu_state t) r=regs s r.
Proof.
 destruct op;cbn [keeps];intros K Run;cbn [step] in Run.
 all: try solve [destruct (qword_op _ _ _) as [v|] eqn:QV;try discriminate;injection Run as <- <-;exact (f_equal (fun f=>f r) (proj1(proj2(qword_state _ _ _ _ QV))))].
 all: try match type of Run with context[VectorMoves.writing ?i]=>destruct (VectorMoves.writing i) end.
 all: try match type of Run with context[option_map _ ?b]=>destruct b as [[]|];try discriminate end.
 all: try match type of Run with context[if ?b then Some (_,_) else None]=>destruct b;try discriminate end.
 all: try (injection Run as <- <-;cbn [cpu_state]).
 all: try reflexivity.
 all: try (apply negb_true_iff in K).
 all: try solve [cbn [with_zf advance_rsp regs set set_regs low_byte push push_words with_words caller_step
     apply_stack result_regs stack_step target_ip];unfold put;rewrite K;reflexivity].
 - apply Bool.andb_true_iff in K as [SP D];apply negb_true_iff in SP,D.
   cbn [pop apply_stack stack_step result_regs set set_regs with_words regs];unfold advance_rsp,put;rewrite D,SP;reflexivity.
 - destruct op;[destruct i;cbn in K;try discriminate|];injection Run as <- <-;reflexivity.
 - change (put (regs s) 4 (word (regs s 4%nat+8)) r=regs s r);unfold put;now rewrite K.
Qed.

Fixpoint checks r (text:list Z) := match text with
 | []=>true | _::rest=>(match decode text with Some(_,op)=>keeps r op | None=>true end) && checks r rest end.
Lemma at_offset r text : checks r text=true -> forall i n op,
 decode (skipn i text)=Some(n,op) -> keeps r op=true.
Proof.
 induction text as [|b bs IH];intros C i n op D.
 - destruct i;discriminate.
 - cbn [checks] in C;apply Bool.andb_true_iff in C as [First Rest].
   destruct i as [|i];[cbn [skipn] in D;now rewrite D in First|exact (IH Rest i n op D)].
Qed.
Theorem steps_keep r o text s ws t : checks r text=true ->
 ScalarBytes.steps o text s ws t -> regs(cpu_state t) r=regs(cpu_state s) r.
Proof.
 intros C Run;induction Run as [s|s u v w tail F R IH];[reflexivity|rewrite IH].
 unfold ScalarBytes.fetch in F;destruct (loc s);try discriminate;destruct (_<?_);try discriminate.
 destruct(decode _) as [[n op]|] eqn:D;try discriminate;eapply step_keeps;[eapply at_offset;eassumption|exact F].
Qed.
Corollary run_keeps r o text n s t ws : checks r text=true -> run n (ScalarBytes.fetch o text) s=Some(t,ws) ->
 regs(cpu_state t) r=regs(cpu_state s) r.
Proof. intros C R;exact (steps_keep _ _ _ _ _ _ C (run_steps _ _ _ _ _ _ R)). Qed.
