From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions isa.QwordRegister execution.LinkedCalls
 execution.WordSemantics execution.ScalarBytes execution.InstructionRoute execution.MappedFetch.
Import ListNotations. Local Open Scope Z_scope.

(* The scalar view of a straight-line block shares its arithmetic with the
   instruction interpreter. Only instructions which act independently on each
   lane have a projection here. *)
Inductive operation := Arithmetic (i:Instructions.instruction) | BitOr (dst a b:nat).
Definition native i := match i with Arithmetic i=>Alu i | BitOr d a b=>Or d a b end.
Definition width i := length (QwordRegister.encoding (native i)).
Fixpoint route pc code := match code with
 | []=>[] | i::rest=>(pc,width i,QwordOp(native i))::route (pc+Z.of_nat(width i)) rest end.
Fixpoint after pc code := match code with
 | []=>pc | i::rest=>after (pc+Z.of_nat(width i)) rest end.
Definition lane_step load (r:nat->Z) i := match i with
 | Arithmetic (d,op)=>put r d (bits load r d op)
 | BitOr d a b=>put r d (word (Z.lor (r a) (r b))) end.
Fixpoint lane load r code := match code with
 | []=>r | i::rest=>lane load (lane_step load r i) rest end.
Lemma route_length pc code : length(route pc code)=length code.
Proof. revert pc;induction code;intro pc;cbn;auto. Qed.

Theorem execute origin text code pc s carry : linked text (route pc code) ->
 exists t,run (length code) (ScalarBytes.fetch origin text) (State (Running pc) s carry)=
  Some(State (Running (after pc code)) t carry,[]) /\
 regs t=regs s /\ mem t=mem s /\ flag t=flag s /\
 forall j,vectors t j=lane (vector_load s j) (vectors s j) code.
Proof.
 revert pc s;induction code as [|i rest IH];intros pc s Bound.
 - exists s;repeat split;reflexivity.
 - unfold linked in Bound;cbn [route] in Bound;inversion Bound as [|h tail Entry Tail];subst;destruct Entry as [Pos Dec].
   set (next:=pc+Z.of_nat(width i)).
   assert (One:exists mid,step origin pc (width i) (QwordOp (native i)) s carry=
     Some(State (Running next) mid carry,[]) /\ regs mid=regs s /\ mem mid=mem s /\
     flag mid=flag s /\ forall j,vectors mid j=lane_step (vector_load s j) (vectors s j) i).
   { destruct i as [[d op]|d a b];eexists;repeat split;reflexivity. }
   destruct One as [mid [Step [Regs [Mem [Flag V]]]]].
   destruct (IH next mid Tail) as [t [Run [Rt [Mt [Ft Value]]]]].
   exists t;split.
   + cbn [length run ScalarBytes.fetch loc cpu_state cf]. rewrite (proj2(Z.ltb_ge _ _) Pos),Dec,Step,Run;reflexivity.
   + split;[now rewrite Rt,Regs|split;[now rewrite Mt,Mem|split;[now rewrite Ft,Flag|]]].
     intro j;rewrite Value,V;cbn [lane]. unfold vector_load;now rewrite Mem,Regs.
Qed.

Lemma arithmetic_lane load r code :
 lane load r (map Arithmetic code)=Instructions.run load code r.
Proof. revert r;induction code as [|[d op] tail IH];intro r;cbn;auto. Qed.

Definition same_operation (a b:operation) : {a=b}+{a<>b}.
Proof. repeat decide equality. Defined.
Definition projected i := match i with
 | QwordOp (Alu ins)=>Some (Arithmetic ins)
 | QwordOp (Or d a b)=>Some (BitOr d a b) | _=>None end.
Lemma projected_native i op : projected i=Some op -> i=QwordOp (native op).
Proof. destruct i;try discriminate;destruct i;intro E;try discriminate;injection E as <-;reflexivity. Qed.

Fixpoint checks text pc code := match code with
 | []=>true | i::rest=>match ScalarBytes.decode (skipn (Z.to_nat pc) text) with
   | Some(n,ins)=>match projected ins with
     | Some op=>if same_operation op i then
        (0<=?pc) && Nat.eqb n (width i) && checks text (pc+Z.of_nat n) rest else false
     | None=>false end | None=>false end end.
Lemma checks_route text code pc : checks text pc code=true -> linked text (route pc code).
Proof.
 revert pc;induction code as [|i rest IH];intros pc H;[constructor|].
 cbn [checks] in H;destruct (ScalarBytes.decode _) as [[n ins]|] eqn:D;try discriminate.
 destruct (projected ins) as [op|] eqn:P;try discriminate.
 destruct (same_operation op i) as [->|];try discriminate.
 apply Bool.andb_true_iff in H as [A H];apply Bool.andb_true_iff in A as [Pos Size].
 apply Nat.eqb_eq in Size;subst n;apply projected_native in P;subst ins.
 constructor;[split;[apply Z.leb_le,Pos|exact D]|apply IH,H].
Qed.
