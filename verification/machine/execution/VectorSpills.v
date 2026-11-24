From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions isa.QwordRegister isa.VectorMoves execution.WordBounds execution.WordSemantics execution.LinkedCalls
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.VectorProcedure
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* A lane projection of decoded register arithmetic interleaved with stores
   to 64-byte rows. The last physical store to a given row wins. *)
Inductive action := Compute (i:Instructions.instruction) | Spill (src row:nat).
Definition operand b a:=match a with
 | Compute i=>QwordOp(Alu i) | Spill src row=>AlignedRow(Row true src b (64*Z.of_nat row)) end.
Definition width b a:=match a with
 | Compute i=>length(Instructions.encode i) | Spill src row=>length(row_encoding(Row true src b (64*Z.of_nat row))) end.
Fixpoint route b off ops : list line :=match ops with []=>[] | a::rest=>
 (off,width b a,operand b a)::route b (off+Z.of_nat(width b a)) rest end.
Definition admissible n a:=match a with Compute i=>register_only i | Spill _ row=>(row<?n)%nat end.

Record view:=View { registers:nat->Z; rows:nat->Z }.
Definition lane v a:=match a with
 | Compute (d,op)=>View (put (registers v) d (bits no_read (registers v) d op)) (rows v)
 | Spill src i=>View (registers v) (put (rows v) i (registers v src)) end.
Definition tracks a n j v s:= (forall r,vectors s j r=registers v r) /\ forall i,(i<n)%nat ->
 read_word (mem s) (a+64*Z.of_nat i+8*Z.of_nat j)=rows v i.

Lemma one o off w op b a n j v s c mid ws :
 admissible n op=true -> (j<8)%nat -> well_formed s -> regs s b=a -> a mod 64=0 -> fits64 a (64*Z.of_nat n) ->
 tracks a n j v s -> step o off w (operand b op) s c=Some(mid,ws) ->
 loc mid=Running(off+Z.of_nat w) /\ regs(cpu_state mid)=regs s /\ tracks a n j (lane v op) (cpu_state mid).
Proof.
 intros K J W Base Al [L H] [Regs Mem];destruct op as [[d op]|src row].
 - cbn [operand step qword_op option_map];intro R;injection R as <- <-;split;[reflexivity|split;[reflexivity|]].
   split;[|exact Mem];intro r;cbn [lane registers vector_dest cpu_state vectors];unfold put.
   destruct(d=?r)%nat;[|apply Regs]. destruct op;cbn [admissible register_only snd] in K;try discriminate;
    cbn [bits];rewrite ?Regs;reflexivity.
 - change ((row<?n)%nat=true) in K;apply Nat.ltb_lt in K.
   set (start:=a+64*Z.of_nat row).
   assert (Addr:word(regs s b+64*Z.of_nat row)=start) by (rewrite Base;apply word_fits;unfold word64,start;lia).
   assert (Aligned:start mod 64=0) by (unfold start;rewrite Z.mul_comm,Z.mod_add by lia;exact Al).
   cbn [operand step writing gpr zmm offset];rewrite Addr,Aligned;intro R;injection R as <- <-.
   split;[reflexivity|split;[reflexivity|split;[exact Regs|]]]. intros i I;cbn [rows lane];unfold put.
   destruct(Nat.eqb_spec row i) as [<-|Other].
   + change (read_word (write_bytes (mem s) start 64 (vector_byte (fun k=>vectors s k src))) (start+8*Z.of_nat j)=registers v src).
     rewrite write_read_vector by (try exact J;apply W,J);apply Regs.
   + rewrite <- (Mem i I);apply preserved_read with (outside:=fun x=>~(start<=x<start+64)).
     * intros x X;apply write_outside,X.
     * intros k B;change (0<=k<8) in B;unfold start;lia.
Qed.

Theorem execute o text b a n j : forall ops off s c t ws v,
 linked text (route b off ops) -> forallb (admissible n) ops=true -> (j<8)%nat ->
 well_formed s -> regs s b=a -> a mod 64=0 -> fits64 a (64*Z.of_nat n) -> tracks a n j v s ->
 MappedFetch.run (length ops) (ScalarBytes.fetch o text) (State (Running off) s c)=Some(t,ws) ->
 tracks a n j (fold_left lane ops v) (cpu_state t).
Proof.
 induction ops as [|op rest IH];intros off s c t ws v Image K J W Base Al Bounds V R.
 - injection R as <- <-;exact V.
 - unfold linked in Image;cbn [route] in Image;inversion Image as [|h tail Head Rest];subst h tail;destruct Head as [Pos Bytes].
   apply andb_true_iff in K as [Ok Next];cbn [length MappedFetch.run ScalarBytes.fetch loc cf cpu_state] in R.
   rewrite (proj2(Z.ltb_ge _ _) Pos),Bytes in R.
   destruct(step _ _ _ _ _ _) as [[m own]|] eqn:S0;try discriminate.
   destruct(run _ _ m) as [[u more]|] eqn:S1;try discriminate;injection R as <- <-.
   destruct(one _ _ _ _ _ _ _ _ _ _ _ _ _ Ok J W Base Al Bounds V S0) as [At [G New]].
   pose proof(step_wf _ _ _ _ _ _ _ _ W S0) as WM.
   destruct m as [pc mid cf'];cbn [loc] in At;subst pc.
   eapply IH;[exact Rest|exact Next|exact J|exact WM|rewrite <-Base;apply (f_equal (fun f=>f b) G)|exact Al|exact Bounds|exact New|exact S1].
Qed.
