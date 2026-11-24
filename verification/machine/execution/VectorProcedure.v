From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.ScalarBytes execution.MappedFetch execution.LinkedRun execution.QwordBlock
 memory.WriteTrace memory.ByteMemory memory.MemoryGeometry abi.CallFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition no_read (_:nat) (_:Z):Z:=0.
Definition register_only (i:Instructions.instruction) := match snd i with
 | Load _ _ | MaddMem _ _ _ _=>false | _=>true end.
Lemma without_loads code load r : forallb register_only code=true ->
 Instructions.run load code r=Instructions.run no_read code r.
Proof.
 revert r;induction code as [|[d op] tail IH];intros r H;[reflexivity|].
 apply andb_true_iff in H as [Op Rest];cbn [Instructions.run];rewrite IH by exact Rest.
 destruct op;try discriminate;reflexivity.
Qed.

Record stack_area := Area { bottom:Z; ceiling:Z }.
Definition region a x := bottom a<=x<ceiling a.
Definition stack_ok a (allowed:Z->Prop) :=
 0<=bottom a /\ ceiling a<2^64 /\ forall x,region a x -> allowed x.
Definition room a depth s := bottom a+depth<=regs s 4%nat<=ceiling a.
Definition available e (allowed:Z->Prop) base text := mapped (mem e) base text /\
 forall x,base<=x<base+Z.of_nat(length text) -> ~allowed x.
Definition procedure := (cursor->option cursor)%type.
Definition then_run (a b:procedure) p := bind (a p) b.

(* The body ends at an instruction boundary, before the caller's next
   instruction. It may use the given depth below the incoming RSP. *)
Record effect_result e allowed p q depth finish (effect:cpu->cpu->Prop) := {
 at_end:ip q=finish; paid:accounted e allowed q;
 registers:forall r,regs(machine q) r=regs(machine p) r;
 outside:forall x,~(regs(machine p) 4%nat-depth<=x<regs(machine p) 4%nat) ->
   mem(machine q) x=mem(machine p) x;
 outcome:effect (machine p) (machine q)
}.
Definition projects code (s t:cpu) := forall j,vectors t j=Instructions.run no_read code (vectors s j).
Definition effect_contract e allowed a start finish depth effect (f:procedure) := forall p,
 ip p=start -> accounted e allowed p -> room a depth (machine p) ->
 exists q,f p=Some q /\ effect_result e allowed p q depth finish effect.
Definition guarded e allowed a start finish depth (need:cpu->Prop) effect (f:procedure) := forall p,
 need (machine p) -> ip p=start -> accounted e allowed p -> room a depth (machine p) ->
 exists q,f p=Some q /\ effect_result e allowed p q depth finish effect.
Definition contract e allowed a start finish depth code :=
 effect_contract e allowed a start finish depth (projects code).

Lemma compose e allowed a start mid finish da db ca cb f g :
 contract e allowed a start mid da ca f -> contract e allowed a mid finish db cb g ->
 contract e allowed a start finish (Z.max da db) (ca++cb) (then_run f g).
Proof.
 intros F G p PC Acc Space.
 destruct(F p PC Acc ltac:(unfold room in *;lia)) as [s [First [At A Reg Keep V]]].
 destruct(G s At A ltac:(unfold room in *;rewrite Reg;lia)) as [t [Second [End Paid R M W]]].
 exists t;split;[unfold then_run;now rewrite First|];constructor;auto.
 - intro;now rewrite R,Reg.
 - intros x X;rewrite M,Keep;[reflexivity|lia|rewrite Reg;lia].
 - intro j;now rewrite W,V,run_app.
Qed.

Lemma block e allowed a base text pc code :
 available e allowed base text -> InstructionRoute.linked text (route pc (map Arithmetic code)) ->
 forallb register_only code=true ->
 contract e allowed a (base+pc) (base+after pc (map Arithmetic code)) 0 code
  (segment base text (length code)).
Proof.
 intros [Image Apart] Bytes Only p PC Acc Space.
 destruct(execute base _ _ _ (machine p) (carry p) Bytes) as [s [Run [Regs [Mem [_ V]]]]].
 rewrite map_length in Run.
 destruct(at_segment _ _ _ _ _ _ _ _ _ Acc PC (image_after _ _ _ _ _ Acc Image Apart) Apart Run (Forall_nil _)) as [Step Paid].
 eexists;split;[exact Step|];constructor;[reflexivity|exact Paid|intro r;exact (f_equal (fun rs=>rs r) Regs)|
   intros x X;exact (f_equal (fun m=>m x) Mem)|].
 intro j;change (vectors s j=Instructions.run no_read code (vectors(machine p) j));rewrite V,arithmetic_lane;apply without_loads,Only.
Qed.

Definition wrapped base text retbase rettext (f:procedure) p :=
 bind (segment base text 1 p) (fun child=>bind (f child) (segment retbase rettext 1)).

Lemma invoke_effect e allowed a base text pc disp retbase rettext retpc depth (need:cpu->Prop) (inner outer:cpu->cpu->Prop) f :
 (forall s t,inner (push s (base+(pc+5))) t -> outer s (LinkedCalls.returning t)) ->
 stack_ok a allowed -> 0<=depth ->
 available e allowed base text -> available e allowed retbase rettext ->
 0<=pc -> ScalarBytes.decode (skipn (Z.to_nat pc) text)=Some(5%nat,CallRelative disp) ->
 0<=retpc -> ScalarBytes.decode (skipn (Z.to_nat retpc) rettext)=Some(1%nat,Ret) ->
 word64(base+(pc+5)+disp) -> word64(base+(pc+5)) ->
 guarded e allowed a (base+(pc+5)+disp) (retbase+retpc) depth need inner f ->
 guarded e allowed a (base+pc) (base+(pc+5)) (8+depth) (fun s=>need (push s (base+(pc+5)))) outer (wrapped base text retbase rettext f).
Proof.
 intros Lift [Low [High Allowed]] Depth [Image Sep] [RetImage RetSep] Pos Decode RetPos RetDecode Dest Back Body
   p Need PC Acc Space;set (s:=machine p) in *;set (sp:=regs s 4%nat).
 assert (Slot:word64(sp-8)) by (unfold sp,word64,room in *;lia).
 set (link:=base+(pc+5));set (mid:=push s link);set (w:=qword (word(base+pc)) (sp-8) link).
 assert (Stack:regs mid 4%nat=sp-8) by (change (word(sp-8)=sp-8);apply word_fits,Slot).
 assert (One:run 1 (ScalarBytes.fetch base text) (State (Running pc) s (carry p))=
   Some(State (Running (pc+5+disp)) mid (carry p),[w])).
 { cbn [run ScalarBytes.fetch loc cpu_state cf];rewrite (proj2(Z.ltb_ge _ _) Pos),Decode.
   cbn [step option_map run];replace (base+(pc+Z.of_nat 5+disp)) with (base+(pc+5)+disp) by ring.
   rewrite (word_fits _ Dest);replace (base+(pc+5)+disp-base) with (pc+5+disp) by ring.
   change (Some (State (Running (pc+5+disp)) mid (carry p),[qword (word(base+pc)) (word(sp-8)) link])=Some(State (Running (pc+5+disp)) mid (carry p),[w]));
   now rewrite (word_fits _ Slot). }
 assert (Safe:confined allowed [w]).
 { constructor;[intros x X;apply Allowed;change (sp-8<=x<sp-8+8) in X;
   unfold region,room,sp in *;lia|constructor]. }
 destruct(at_segment _ _ _ base text _ pc _ _ Acc PC (image_after _ _ _ _ _ Acc Image Sep) Sep One Safe)
   as [Enter A].
 set (child:=LinkedRun.finish base p (State (Running (pc+5+disp)) mid (carry p),[w])) in *.
 assert (ChildAt:ip child=base+(pc+5)+disp) by (change (base+(pc+5+disp)=base+(pc+5)+disp);ring).
 destruct(Body child Need ChildAt A ltac:(change (room a depth mid);unfold room;rewrite Stack;unfold room,sp in *;lia))
   as [last [Inside [At AtAcc Reg Keep Values]]].
 assert (LastSP:regs(machine last) 4%nat=sp-8) by (rewrite Reg;exact Stack).
 assert (ReturnWord:read_word (mem(machine last)) (sp-8)=link).
 { rewrite <-Stack;transitivity (read_word (mem mid) (regs mid 4%nat));[|exact (pushed_return_word s link Back)].
   apply preserved_read with (outside:=fun x=>~(sp-8-depth<=x<sp-8)).
   - intros x H;apply Keep;change (~(regs mid 4%nat-depth<=x<regs mid 4%nat));now rewrite Stack.
   - intros k K;rewrite Stack;lia. }
 set (out:=LinkedCalls.returning (machine last)).
 assert (RetRun:run 1 (ScalarBytes.fetch retbase rettext) (State (Running retpc) (machine last) (carry last))=
    Some(State (Returned link) out (carry last),[])).
 { cbn [run ScalarBytes.fetch loc cpu_state cf];rewrite (proj2(Z.ltb_ge _ _) RetPos),RetDecode.
   change (Some(State (Returned (word(read_word (mem(machine last)) (word(regs(machine last) 4%nat))))) out (carry last),@nil store)=Some(State (Returned link) out (carry last),@nil store)).
   rewrite LastSP,(word_fits _ Slot),ReturnWord,(word_fits link Back);reflexivity. }
 destruct(at_segment _ _ _ retbase rettext _ retpc _ _ AtAcc At (image_after _ _ _ _ _ AtAcc RetImage RetSep)
   RetSep RetRun (Forall_nil _)) as [Leave Last].
 eexists;split;[unfold wrapped;rewrite Enter;fold child;cbn [bind];rewrite Inside;exact Leave|].
 constructor;[reflexivity|exact Last| | |].
 - intro r;change (put (regs(machine last)) 4 (word(regs(machine last) 4%nat+8)) r=regs s r).
   unfold put;destruct (Nat.eqb 4 r) eqn:R.
   + apply Nat.eqb_eq in R;subst r;rewrite LastSP;replace (sp-8+8) with sp by ring.
     apply word_fits;unfold room,sp,word64 in *;lia.
   + rewrite Reg;change (put (regs s) 4 (word(sp-8)) r=regs s r);unfold put;now rewrite R.
 - intros x X;change (mem(machine last) x=mem s x);rewrite Keep.
   + change (store_word (mem s) (word(sp-8)) link x=mem s x);rewrite (word_fits _ Slot);
     apply FlatMemory.write_outside;change (~(sp-(8+depth)<=x<sp)) in X;lia.
   + change (~(regs mid 4%nat-depth<=x<regs mid 4%nat));rewrite Stack;change (~(sp-(8+depth)<=x<sp)) in X;lia.
 - apply Lift;exact Values.
Qed.

Lemma invoke e allowed a base text pc disp retbase rettext retpc depth code f :
 stack_ok a allowed -> 0<=depth ->
 available e allowed base text -> available e allowed retbase rettext ->
 0<=pc -> ScalarBytes.decode (skipn (Z.to_nat pc) text)=Some(5%nat,CallRelative disp) ->
 0<=retpc -> ScalarBytes.decode (skipn (Z.to_nat retpc) rettext)=Some(1%nat,Ret) ->
 word64(base+(pc+5)+disp) -> word64(base+(pc+5)) ->
 contract e allowed a (base+(pc+5)+disp) (retbase+retpc) depth code f ->
 contract e allowed a (base+pc) (base+(pc+5)) (8+depth) code (wrapped base text retbase rettext f).
Proof.
 intros Stack D Site End Pos Call RetPos Ret Dest Return Body p PC Acc Space.
 eapply (invoke_effect _ _ _ _ _ _ _ _ _ _ _ (fun _=>True) (projects code) (projects code) _
   ltac:(intros s t H;exact H) Stack D Site End Pos Call RetPos Ret Dest Return
   ltac:(intros child _;apply Body) p I PC Acc Space).
Qed.
