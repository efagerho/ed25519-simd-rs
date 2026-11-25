From Coq Require Import List ZArith Lia.
From Machine Require Import isa.IndexedLoad isa.VectorMoves execution.WordSemantics execution.LinkedCalls
 execution.IndexedLoads execution.ScalarBytes execution.MappedFetch execution.InstructionRoute.
From Machine Require execution.Packed.
Import ListNotations. Local Open Scope Z_scope.

(* Track the register and qword lane supplying each result of a transpose. *)
Inductive permutation:=Unpack (high:bool) (dst a b:nat) | Shuffle (dst a b imm:nat).
Definition instruction op:=match op with Unpack hi d a b=>UnpackWords hi d a b | Shuffle d a b imm=>ShuffleWords d a b imm end.
Definition destination op:=match op with Unpack _ d _ _ | Shuffle d _ _ _=>d end.
Definition source op:=match op with Unpack hi _ a b=>Packed.unpack_source hi a b | Shuffle _ a b imm=>Packed.shuffle_source a b imm end.
Definition width op:=length(IndexedLoad.encode (instruction op)).
Fixpoint route pc ops:list line:=match ops with []=>[] | op::rest=>
 (pc,width op,VectorMove(Input(instruction op)))::route (pc+Z.of_nat(width op)) rest end.
Fixpoint after pc ops:=match ops with []=>pc | op::rest=>after (pc+Z.of_nat(width op)) rest end.
Definition rearrange {A:Type} (r:nat->nat->A) op:=fun reg j=>
 if Nat.eqb reg (destination op) then let '(a,b):=source op j in r a b else r reg j.
Definition live s r j:=vectors s j r.

Lemma one o pc op s c:
 let t:=IndexedLoads.execute [instruction op] s in
 step o pc (width op) (VectorMove(Input(instruction op))) s c=Some(State(Running(pc+Z.of_nat(width op))) t c,[]) /\
 regs t=regs s /\ mem t=mem s /\ flag t=flag s /\ forall r j,live t r j=rearrange (live s) op r j.
Proof.
 destruct op as [hi d a b|d a b imm];cbn zeta;repeat split;intros r j;
 unfold live,rearrange,IndexedLoads.execute,IndexedLoads.summary;cbn [instruction fold_left IndexedLoads.step
  IndexedLoads.initial IndexedLoads.vec IndexedLoads.gp IndexedLoads.zf vectors destination source];
 unfold Packed.update;destruct(Nat.eqb r d) eqn:E;try rewrite Nat.eqb_sym,E;
 try destruct(Packed.unpack_source hi a b j);try destruct(Packed.shuffle_source a b imm j);reflexivity.
Qed.

Lemma related {A B:Type} (R:A->B->Prop) ops : forall u v,
 (forall r j,R (u r j) (v r j)) -> forall r j,R (fold_left rearrange ops u r j) (fold_left rearrange ops v r j).
Proof.
 induction ops as [|op ops IH];intros u v Same r j;cbn [fold_left];[apply Same|apply IH].
 intros d k;unfold rearrange;destruct(Nat.eqb d (destination op));[destruct(source op k)|];apply Same.
Qed.

Lemma run_ops o text ops : forall pc s c,linked text (route pc ops) ->
 exists t,run (length ops) (ScalarBytes.fetch o text) (State(Running pc) s c)=Some(State(Running(after pc ops)) t c,[]) /\
 regs t=regs s /\ mem t=mem s /\ flag t=flag s /\ forall r j,live t r j=fold_left rearrange ops (live s) r j.
Proof.
 induction ops as [|op rest IH];intros pc s c Image;[exists s;repeat split;reflexivity|].
 cbn [route] in Image;apply Forall_cons_iff in Image as [[Pos Dec] Tail].
 set (b:=IndexedLoads.execute [instruction op] s);destruct(one o pc op s c) as [Step [G [M [F V]]]];fold b in Step,G,M,F,V.
 destruct(IH _ b c Tail) as [t [R [GT [MT [FT Out]]]]].
 exists t;split;[cbn [length run ScalarBytes.fetch loc cpu_state cf after];now rewrite (proj2(Z.ltb_ge _ _) Pos),Dec,Step,R|].
 split;[now rewrite GT,G|split;[now rewrite MT,M|split;[now rewrite FT,F|]]].
 intros r j;rewrite Out;cbn [fold_left].
 exact (related eq rest _ _ V r j).
Qed.
