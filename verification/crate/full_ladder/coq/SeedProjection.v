From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions isa.ProgramLayout isa.QwordRegister isa.VectorMoves execution.WordBounds execution.WordSemantics
 execution.LinkedCalls execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Machine Require execution.VectorSpills.
From Ed25519Simd.FullLadder Require Import SeedPath.
From Ed25519Simd.FullLadder Require Seed.
Import ListNotations. Local Open Scope Z_scope.

Definition cell m base i j:=read_word m (base+64*Z.of_nat i+8*Z.of_nat j).
Definition source base j input s:=forall i,(i<20)%nat -> cell (mem s) base i j=input i.
Definition tracks pt j l s:=regs s 0%nat=Seed.rax l /\
 VectorSpills.tracks pt 20 j (VectorSpills.View (Seed.reg l) (Seed.out l)) s.

Lemma load_operand s b a i j : window a -> regs s b=a -> (i<20)%nat ->
 vector_load s j b (64*Z.of_nat i)=cell (mem s) a i j.
Proof. intros Win Base I;unfold vector_load,cell;now rewrite (proj1(address _ _ _ _ Base Win I)). Qed.

Lemma projected op o off s c u ws pt base input l j :
 Seed.valid op=true -> (j<8)%nat -> well_formed s -> regs s 3%nat=pt -> regs s 4%nat=base ->
 window pt -> window base -> source base j input s -> tracks pt j l s ->
 step o off (width op) (ins op) s c=Some(State(Running(off+Z.of_nat(width op))) u c,ws) ->
 tracks pt j (Seed.step input l op) u.
Proof.
 intros V J W Out Stack P B Src [AX View] Run;destruct View as [G Rows];cbn [VectorSpills.registers VectorSpills.rows] in G,Rows.
 destruct op as [wide v|d|[d v]|d b i|d a b i|b i r].
 - destruct wide;cbn [ins step Seed.valid unsigned] in Run,V;apply andb_true_iff in V as [Lo Hi];apply Z.leb_le in Lo;apply Z.ltb_lt in Hi.
   all:injection Run as <- <-;split;[cbn [regs set set_regs put Seed.step Seed.rax Nat.eqb];apply Z.mod_small;lia|split;[exact G|exact Rows]].
 - injection Run as <- <-;split;[exact AX|split;[|exact Rows]];intro r;cbn [Seed.step Seed.reg vectors VectorSpills.registers VectorSpills.rows];unfold put;destruct (d=?r)%nat;[exact AX|apply G].
 - assert (K:VectorSpills.admissible 20 (VectorSpills.Compute(d,v))=true) by (destruct v;try discriminate;reflexivity).
   destruct(VectorSpills.one o off (width(Seed.Vec(d,v))) (VectorSpills.Compute(d,v)) 3 pt 20 j
      (VectorSpills.View (Seed.reg l) (Seed.out l)) s c _ _ K J W Out (proj1 P) (proj2 P) (conj G Rows) Run)
       as [_ [Regs New]];split;[change (regs u 0%nat=Seed.rax l);exact (eq_trans (f_equal (fun g=>g 0%nat) Regs) AX)|exact New].
 - cbn [Seed.valid] in V;repeat rewrite andb_true_iff in V;destruct V as [[_ Eq] I];apply Nat.eqb_eq in Eq;subst b;apply Nat.ltb_lt in I.
   destruct(address _ _ _ _ Stack B I) as [Addr Al];cbn [ins step gpr offset zmm writing] in Run;rewrite Addr,Al in Run;injection Run as <- <-.
   split;[exact AX|split;[|exact Rows]];intro r;cbn [vectors vector_dest Seed.step Seed.reg VectorSpills.registers VectorSpills.rows];unfold put;destruct (d=?r)%nat;[|apply G].
   change (vector_load s j 4 (64*Z.of_nat i)=input i).
   rewrite (load_operand s 4 base i j B Stack I);apply Src,I.
 - cbn [Seed.valid] in V;repeat rewrite andb_true_iff in V;destruct V as [[[_ _] Choice] I];apply Nat.ltb_lt in I.
   injection Run as <- <-;split;[exact AX|split;[|exact Rows]];intro r;cbn [vectors vector_dest Seed.step Seed.reg VectorSpills.registers VectorSpills.rows];unfold put;destruct (d=?r)%nat;[|apply G].
   apply orb_true_iff in Choice as [OutR|InR];[apply Nat.eqb_eq in OutR;subst b|apply Nat.eqb_eq in InR;subst b].
   + change (Arithmetic.vpaddq (vectors s j a) (vector_load s j 3 (64*Z.of_nat i))=Arithmetic.vpaddq (Seed.reg l a) (Seed.out l i)).
     rewrite (load_operand s 3 pt i j P Out I),G;f_equal;exact (Rows i I).
   + change (Arithmetic.vpaddq (vectors s j a) (vector_load s j 4 (64*Z.of_nat i))=Arithmetic.vpaddq (Seed.reg l a) (input i)).
     rewrite (load_operand s 4 base i j B Stack I),G,(Src i I);reflexivity.
 - cbn [Seed.valid] in V;repeat rewrite andb_true_iff in V;destruct V as [[Eq I] _];apply Nat.eqb_eq in Eq;subst b.
   destruct(VectorSpills.one o off (width(Seed.StoreRow 3 i r)) (VectorSpills.Spill r i) 3 pt 20 j
      (VectorSpills.View (Seed.reg l) (Seed.out l)) s c _ _ I J W Out (proj1 P) (proj2 P) (conj G Rows) Run)
       as [_ [Regs New]];split;[change (regs u 0%nat=Seed.rax l);exact (eq_trans (f_equal (fun g=>g 0%nat) Regs) AX)|exact New].
Qed.

Theorem execute o text pt base j input : forall ops off s c u ws l,
 linked text (route off ops) -> forallb Seed.valid ops=true -> (j<8)%nat -> well_formed s ->
 regs s 3%nat=pt -> regs s 4%nat=base -> window pt -> window base -> disjoint pt 1280 base 1280 ->
 source base j input s -> tracks pt j l s ->
 run (length ops) (ScalarBytes.fetch o text) (State(Running off) s c)=Some(u,ws) ->
 tracks pt j (fold_left (Seed.step input) ops l) (cpu_state u).
Proof.
 induction ops as [|op rest IH];intros off s c u ws l Code Valid J W Out Stack P B Apart Src Old Run.
 - injection Run as <- <-;exact Old.
 - unfold linked in Code;cbn [route] in Code;inversion Code as [|h xs H Tail];subst h xs;destruct H as [Pos Dec];apply andb_true_iff in Valid as [K V].
   destruct(SeedPath.one pt base op o off s c K P B Out Stack) as [mid [own [One [Regs Safe]]]].
   cbn [length run ScalarBytes.fetch loc cpu_state cf] in Run;rewrite (proj2(Z.ltb_ge _ _) Pos),Dec,One in Run.
   destruct(run (length rest) _ _) as [[last later]|] eqn:Next;try discriminate;injection Run as <- <-.
   apply (IH _ mid c last later (Seed.step input l op) Tail V J (step_wf _ _ _ _ _ _ _ _ W One) ltac:(rewrite Regs by discriminate;exact Out)
       ltac:(rewrite Regs by discriminate;exact Stack) P B Apart);[|eapply projected;eassumption|exact Next].
   intros i I;rewrite <-(Src i I);unfold cell;apply preserved_read with (outside:=fun x=>~region pt x).
   + intros x X;pose proof(step_memory _ _ _ _ _ _ _ _ One) as M;cbn [cpu_state] in M;rewrite M;apply (WriteTrace.frame _ _ Safe),X.
   + intros k K';change (0<=k<8) in K';unfold region,disjoint in *;lia.
Qed.
