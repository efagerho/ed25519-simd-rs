From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions isa.QwordRegister isa.VectorMoves execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.FullLadder Require Import LinkedBytes.
From Ed25519Simd.FullLadder Require Seed.
Import ListNotations. Local Open Scope Z_scope.

Definition ins op:=match op with
 | Seed.Imm wide v=>if wide then Imm64 0 v else Imm32 0 v
 | Seed.Broadcast d=>BroadcastG d 0 | Seed.Vec i=>QwordOp(Alu i)
 | Seed.ReadRow d b i=>AlignedRow(Row false d b (64*Z.of_nat i))
 | Seed.AddRow d a b i=>QwordOp(MemoryArithmetic false d a b (64*Z.of_nat i))
 | Seed.StoreRow b i r=>AlignedRow(Row true r b (64*Z.of_nat i)) end.
Definition width op:=length (Seed.encode op).
Fixpoint route off ops:list line:=match ops with []=>[] | op::rest=>
 (off,width op,ins op)::route (off+Z.of_nat(width op)) rest end.
Fixpoint after off ops:=match ops with []=>off | op::rest=>after (off+Z.of_nat(width op)) rest end.

Lemma image:linked symbol_bytes (route 54 Seed.code).
Proof. repeat (constructor;[split;[vm_compute;discriminate|vm_compute;reflexivity]|]);constructor. Qed.
Lemma end_offset:after 54 Seed.code=768. Proof. vm_compute;reflexivity. Qed.

Definition region pt x:=pt<=x<pt+1280.
Definition window a:=a mod 64=0 /\ fits64 a 1280.
Lemma address s b a i : regs s b=a -> window a -> (i<20)%nat ->
 word(regs s b+64*Z.of_nat i)=a+64*Z.of_nat i /\ (a+64*Z.of_nat i) mod 64=0.
Proof.
 intros B [Al [Lo Hi]] I;rewrite B;split;[apply word_fits;unfold word64;lia|].
 rewrite Z.mul_comm,Z.mod_add by lia;exact Al.
Qed.

Lemma one pt base op o off s c : Seed.valid op=true -> window pt -> window base ->
 regs s 3%nat=pt -> regs s 4%nat=base ->
 exists u ws,step o off (width op) (ins op) s c=Some(State(Running(off+Z.of_nat(width op))) u c,ws) /\
 (forall g,g<>0%nat -> regs u g=regs s g) /\ confined (region pt) ws.
Proof.
 intros V P B Out Stack;destruct op as [w v|r|[d v]|r b i|d a b i|b i r].
 - destruct w;(do 2 eexists;split;[reflexivity|split;[intros g G;cbn [regs set set_regs];destruct g;[contradiction|reflexivity]|exact (Forall_nil _)]]).
 - do 2 eexists;split;[reflexivity|split;[reflexivity|exact (Forall_nil _)]].
 - do 2 eexists;split;[reflexivity|split;[reflexivity|exact (Forall_nil _)]].
 - cbn [Seed.valid] in V;repeat rewrite andb_true_iff in V;destruct V as [[_ Eq] I];apply Nat.eqb_eq in Eq;subst b;apply Nat.ltb_lt in I.
   destruct(address _ _ _ _ Stack B I) as [Addr Al];cbn [ins step gpr offset zmm writing];rewrite Addr,Al.
   do 2 eexists;split;[reflexivity|split;[reflexivity|exact (Forall_nil _)]].
 - do 2 eexists;split;[reflexivity|split;[reflexivity|exact (Forall_nil _)]].
 - cbn [Seed.valid] in V;repeat rewrite andb_true_iff in V;destruct V as [[Eq I] _];apply Nat.eqb_eq in Eq;subst b;apply Nat.ltb_lt in I.
   destruct(address _ _ _ _ Out P I) as [Addr Al];cbn [ins step gpr offset zmm writing];rewrite Addr,Al.
   do 2 eexists;split;[reflexivity|split;[reflexivity|constructor;[|exact (Forall_nil _)]]];intros x X.
   change (pt+64*Z.of_nat i<=x<pt+64*Z.of_nat i+64) in X;unfold region;lia.
Qed.

Theorem execute o text pt base : forall ops off s c,
 linked text (route off ops) -> forallb Seed.valid ops=true -> window pt -> window base ->
 regs s 3%nat=pt -> regs s 4%nat=base ->
 exists u ws,run (length ops) (ScalarBytes.fetch o text) (State(Running off) s c)=
   Some(State(Running(after off ops)) u c,ws) /\
 (forall g,g<>0%nat -> regs u g=regs s g) /\ confined (region pt) ws.
Proof.
 induction ops as [|op rest IH];intros off s c Code Valid P B Out Stack.
 - exists s,[];repeat split;constructor.
 - unfold linked in Code;cbn [route] in Code;inversion Code as [|h xs H Tail];subst h xs;destruct H as [Pos Dec];apply andb_true_iff in Valid as [K V].
   destruct(one pt base op o off s c K P B Out Stack) as [mid [own [Step [G Safe]]]].
   destruct(IH _ mid c Tail V P B ltac:(rewrite G by discriminate;exact Out) ltac:(rewrite G by discriminate;exact Stack))
      as [u [tail [Run [Keep Rest]]]].
   exists u,(own++tail);split.
   + cbn [length run ScalarBytes.fetch loc cpu_state cf];rewrite (proj2(Z.ltb_ge _ _) Pos),Dec,Step,Run;reflexivity.
   + split;[intros g NZ;rewrite Keep,G by exact NZ;reflexivity|apply Forall_app;auto].
Qed.
