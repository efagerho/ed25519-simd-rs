From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions isa.VectorMoves execution.LinkedCalls execution.WordBounds
 execution.WordSemantics execution.ScalarBytes execution.MappedFetch execution.InstructionRoute
 memory.MemoryGeometry memory.ByteMemory memory.FlatMemory memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

Definition width wr r b d := length(row_encoding (Row wr r b d)).
Fixpoint route wr pc r b d n := match n with
 | O=>[] | S k=>let w:=width wr r b d in
   (pc,w,AlignedRow(Row wr r b d))::route wr (pc+Z.of_nat w) (S r) b (d+64) k end.
Fixpoint after wr pc r b d n := match n with
 | O=>pc | S k=>after wr (pc+Z.of_nat(width wr r b d)) (S r) b (d+64) k end.
Definition range a n x := a<=x<a+64*Z.of_nat n.
Definition saved s out a r n := forall i j,(i<n)%nat -> (j<8)%nat ->
 read_word (mem out) (a+64*Z.of_nat i+8*Z.of_nat j)=vectors s j (r+i)%nat.

(* A row store has a 64-byte footprint even when its payload equals the
   previous contents. Every read-back below uses the resulting byte memory. *)
Theorem stores o text n : forall pc r b d a s c,
 linked text (route true pc r b d n) -> regs s b+d=a -> a mod 64=0 ->
 fits64 a (64*Z.of_nat n) ->
 (forall i j,(i<n)%nat -> (j<8)%nat -> word64 (vectors s j (r+i)%nat)) ->
 exists t ws, run n (ScalarBytes.fetch o text) (State (Running pc) s c)=
    Some(State (Running (after true pc r b d n)) t c,ws) /\
 regs t=regs s /\ vectors t=vectors s /\ flag t=flag s /\
 confined (range a n) ws /\ saved s t a r n.
Proof.
 induction n as [|n IH];intros pc r b d a s c Bound Base Al Fit Words.
 - exists s,[];repeat split;try constructor;intros i j I;lia.
 - unfold linked in Bound;cbn [route] in Bound;inversion Bound as [|h tail One Rest];subst h tail.
   destruct One as [Pos Dec].
   set (w:=vector (word(o+pc)) a (fun j=>vectors s j r)).
   set (mid:=with_words s (regs s) (commit (mem s) w)).
   set (next:=pc+Z.of_nat(width true r b d)).
   assert (Addr:word(regs s b+d)=a) by (rewrite Base;apply word_fits;unfold word64,fits64 in *;lia).
   assert (Step:step o pc (width true r b d) (AlignedRow(Row true r b d)) s c=Some(State (Running next) mid c,[w])).
   { cbn [step gpr offset zmm writing];now rewrite Addr,Al. }
   destruct (IH next (S r) b (d+64) (a+64) mid c Rest
     ltac:(change (regs s b+(d+64)=a+64);lia)
     ltac:(replace (a+64) with (a+1*64) by ring;now rewrite Z.mod_add by lia)
     ltac:(unfold fits64 in *;lia)
     ltac:(intros i j I J;change (word64(vectors s j (S r+i)%nat));
         replace (S r+i)%nat with (r+S i)%nat by lia;apply Words;lia))
      as [t [ws [Run [Regs [Vec [Flag [Safe Rows]]]]]]].
   exists t,(w::ws);split.
   + cbn [run ScalarBytes.fetch loc cf cpu_state];rewrite (proj2 (Z.ltb_ge _ _) Pos),Dec,Step,Run;reflexivity.
   + split;[exact Regs|split;[exact Vec|split;[exact Flag|]]].
     split.
     * constructor;[intros x X;change (a<=x<a+64) in X;unfold range;lia|].
       apply Forall_impl with (P:=permits (range (a+64) n));[|exact Safe].
       intros f E x X;specialize(E x X);unfold range in *;lia.
     * intros [|i] j I J.
       -- replace (a+64*Z.of_nat 0+8*Z.of_nat j) with (a+8*Z.of_nat j) by ring.
          rewrite Nat.add_0_r;pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)) as M.
          change (mem t=WriteTrace.replay (mem mid) ws) in M.
          rewrite M;apply eq_trans with (y:=read_word (mem mid) (a+8*Z.of_nat j)).
          ++ apply preserved_read with (outside:=fun x=>~range (a+64) n x).
             ** exact (WriteTrace.frame _ _ Safe _).
             ** intros k K;change (0<=k<8) in K;unfold range;lia.
          ++ apply (write_read_vector (mem s) a (fun k=>vectors s k r) j);[exact J|pose proof (Words 0%nat j ltac:(lia) J) as V;now rewrite Nat.add_0_r in V].
       -- replace (a+64*Z.of_nat (S i)+8*Z.of_nat j) with (a+64+64*Z.of_nat i+8*Z.of_nat j) by lia.
          replace (r+S i)%nat with (S r+i)%nat by lia;exact (Rows i j ltac:(lia) J).
Qed.

Theorem loads o text n : forall pc r b d a s c,
 linked text (route false pc r b d n) -> regs s b+d=a -> a mod 64=0 -> fits64 a (64*Z.of_nat n) ->
 exists t,run n (ScalarBytes.fetch o text) (State (Running pc) s c)=
    Some(State (Running (after false pc r b d n)) t c,[]) /\
 regs t=regs s /\ mem t=mem s /\ flag t=flag s /\
 (forall j i,(i<n)%nat -> vectors t j (r+i)%nat=read_word (mem s) (a+64*Z.of_nat i+8*Z.of_nat j)) /\
 forall j k,(k<r \/ r+n<=k)%nat -> vectors t j k=vectors s j k.
Proof.
 induction n as [|n IH];intros pc r b d a s c Bound Base Al Fit.
 - exists s;repeat split;intros;try reflexivity;lia.
 - unfold linked in Bound;cbn [route] in Bound;inversion Bound as [|h tail One Rest];subst h tail.
   destruct One as [Pos Dec];set (v:=fun j=>read_word (mem s) (a+8*Z.of_nat j)).
   set (mid:=vector_dest s r v);set (next:=pc+Z.of_nat(width false r b d)).
   assert (Addr:word(regs s b+d)=a) by (rewrite Base;apply word_fits;unfold fits64,word64 in *;lia).
   assert (Step:step o pc (width false r b d) (AlignedRow(Row false r b d)) s c=Some(State (Running next) mid c,[])).
   { cbn [step gpr offset zmm writing];unfold vector_load;now rewrite Addr,Al. }
   destruct (IH next (S r) b (d+64) (a+64) mid c Rest ltac:(change (regs s b+(d+64)=a+64);lia)
     ltac:(replace (a+64) with (a+1*64) by ring;now rewrite Z.mod_add by lia)
     ltac:(unfold fits64 in *;lia)) as [t [Run [G [M [F [Rows Other]]]]]].
   exists t;split.
   + cbn [run ScalarBytes.fetch loc cf cpu_state];rewrite (proj2(Z.ltb_ge _ _) Pos),Dec,Step,Run;reflexivity.
   + split;[exact G|split;[exact M|split;[exact F|split]]].
     * intros j [|i] I.
       -- rewrite Nat.add_0_r,Other by lia;unfold mid,vector_dest;cbn [vectors];unfold put,v;rewrite Nat.eqb_refl;f_equal;ring.
       -- replace (r+S i)%nat with (S r+i)%nat by lia;rewrite Rows by lia;unfold mid,vector_dest;cbn [mem];f_equal;lia.
     * intros j k K;rewrite Other by lia;unfold mid,vector_dest;cbn [vectors];unfold put;now rewrite (proj2(Nat.eqb_neq r k) ltac:(lia)).
Qed.
