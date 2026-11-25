From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics
 execution.ScalarBytes execution.MappedFetch execution.StoreInstructions.
From Machine Require isa.VectorMoves isa.IndexedLoad execution.IndexedLoads.
Import ListNotations. Local Open Scope Z_scope.

(* A sufficient instruction-level test that r survives. A decoded branch
   may still choose any target and all implicit RSP writes are included. *)
Definition keeps r op := let other d:=negb (Nat.eqb d r) in match op with
 | AndImmediate d _ | Load64 d _ | Load8 d _ | Zero32 d | And8 d _ | Inc d | Imm32 d _ | CopyG d _
 | LeaG d _ | Sub64 d _ | Add32 d _ | Add64 d _ | MoveBelow d _ | Copy32 d _ | Inc32 d | Dec32 d | Shl32 d _ | Or32 d _ | Shr32 d _ | And32 d _ | ExtendByte d _=>other d
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
 all: try match type of Run with context[if ?b then Some _ else Some _]=>destruct b end.
 all: try match type of Run with context[option_map _ ?b]=>destruct b as [[]|];try discriminate end.
 all: try match type of Run with context[if ?b then Some (_,_) else None]=>destruct b;try discriminate end.
 all: try (injection Run as <- <-;cbn [cpu_state]).
 all: try reflexivity.
 all: try (apply negb_true_iff in K).
 all: try solve [cbn [with_zf advance_rsp regs set set_regs low_byte push push_words with_words caller_step
     apply_stack result_regs stack_step target_ip];unfold put;rewrite K;reflexivity].
 - apply Bool.andb_true_iff in K as [SP D];apply negb_true_iff in SP,D.
   cbn [pop apply_stack stack_step result_regs set set_regs with_words regs];unfold advance_rsp,put;rewrite D,SP;reflexivity.
 - destruct op;[destruct i;cbn in K;try discriminate| | |];injection Run as <- <-;reflexivity.
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

(* Decode only instruction starts reachable in the remaining step budget.
   Direct CALL uses an absolute 64-bit target. If execution continues in
   this image after the CALL, that address determines the same relative
   offset; leaving the image blocks a further single-image fetch. *)
Definition successors off n op:=let next:=off+Z.of_nat n in match op with
 | Ret=>[] | Jump d | CallRelative d=>[next+d] | Branch _ d=>[next;next+d] | _=>[next] end.
Fixpoint checks_at r text off n:=match n with O=>true | S tail=>
 if off<?0 then true else match decode (skipn (Z.to_nat off) text) with None=>true | Some(w,op)=>
 keeps r op && match tail with O=>true | S _=>
 forallb (fun dest=>(-2^62<?dest) && (dest<?2^62) && checks_at r text dest tail) (successors off w op) end end end.

Lemma step_pc o pc w op s c t ws : step o pc w op s c=Some(t,ws) ->
 match loc t with Returned _=>True | Running d=>match op with
 | CallRelative rel=>d=word(o+(pc+Z.of_nat w+rel))-o
 | _=>In d (successors pc w op) end end.
Proof.
 destruct op;cbn [step];intro S.
 all: try match type of S with context[VectorMoves.writing ?i]=>destruct (VectorMoves.writing i) end.
 all: try match type of S with context[if ?b then Some _ else Some _]=>destruct b end.
 all: try match type of S with context[if ?b then Some _ else None]=>destruct b;try discriminate end.
 all: try match type of S with context[option_map _ ?b]=>destruct b;try discriminate end.
 all: try (injection S as <- <-;cbn [loc successors In];auto).
 - destruct op;injection S as <- <-;cbn [loc successors In];auto.
 - destruct b;cbn;auto.
Qed.

Lemma small_relative o a b : -2^62<a<2^62 -> 0<=b<2^32 -> word(o+a)-o=b -> a=b.
Proof.
 intros A B Eq;unfold word in Eq;pose proof(Z.div_mod (o+a) (2^64) ltac:(lia)) as D.
 assert ((o+a)/2^64=0) by lia;lia.
Qed.
Lemma continuing_offset o text off s c t ws : ScalarBytes.fetch o text (State (Running off) s c)=Some(t,ws) ->
 0<=off<Z.of_nat(length text).
Proof.
 unfold ScalarBytes.fetch;cbn [loc cf cpu_state];destruct(off<?0) eqn:N;[discriminate|].
 apply Z.ltb_ge in N;intro F;split;[exact N|].
 destruct (Z_lt_ge_dec off (Z.of_nat(length text)));[assumption|].
 rewrite skipn_all2 in F by lia;discriminate.
Qed.

Theorem run_keeps_at r o text : Z.of_nat(length text)<2^32 -> forall n off s c t ws,
 checks_at r text off n=true -> run n (ScalarBytes.fetch o text) (State (Running off) s c)=Some(t,ws) ->
 regs(cpu_state t) r=regs s r.
Proof.
 intro Len;induction n as [|n IH];intros off s c t ws X R;[injection R as <- <-;reflexivity|].
 cbn [run] in R;destruct(ScalarBytes.fetch o text (State (Running off) s c)) as [[mid own]|] eqn:F;[|discriminate].
 destruct(run n _ mid) as [[last tail]|] eqn:Rest;[|discriminate];injection R as <- <-.
 cbn [checks_at] in X;unfold ScalarBytes.fetch in F;cbn [loc cf cpu_state] in F;destruct(off<?0);[discriminate|].
 destruct(decode _) as [[width inst]|] eqn:D;[|discriminate];apply andb_true_iff in X as [K Next].
 pose proof(step_keeps _ _ _ _ _ _ _ _ _ K F) as Here;cbn [cpu_state] in Here.
 destruct n as [|n];[injection Rest as <- <-;exact Here|].
 destruct mid as [[d|ip] v cf];[|discriminate];cbn [cpu_state] in Here;rewrite <-Here.
 assert (Live:0<=d<Z.of_nat(length text)).
 { cbn [run] in Rest;destruct(ScalarBytes.fetch o text (State (Running d) v cf)) as [[u more]|] eqn:Fetch;[exact (continuing_offset _ _ _ _ _ _ _ Fetch)|discriminate]. }
 apply (IH d v cf last tail);[|exact Rest].
 rewrite forallb_forall in Next;pose proof(step_pc _ _ _ _ _ _ _ _ F) as PC;cbn [loc] in PC.
 destruct inst;try (specialize(Next d PC);repeat rewrite andb_true_iff in Next;tauto).
 specialize(Next (off+Z.of_nat width+disp) ltac:(cbn [successors In];auto)).
 repeat rewrite andb_true_iff in Next;destruct Next as [[Lo Hi] Good];apply Z.ltb_lt in Lo,Hi.
 rewrite <- (small_relative o (off+Z.of_nat width+disp) d ltac:(lia) ltac:(lia) (eq_sym PC));exact Good.
Qed.
