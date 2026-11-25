From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.QwordRegister isa.VectorMoves execution.LinkedCalls execution.WordSemantics
 execution.WordBounds execution.ScalarBytes execution.MappedFetch memory.MemoryGeometry memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* The domain of a straight-line block with fixed GPRs. The decoded memory
   operand determines alignment and the write range. Other accepted
   instructions write only vector registers. *)
Definition accepts b lo hi op := match op with
 | BroadcastRip _ _=>true
 | QwordOp (AlignedRip _ _)=>false
 | QwordOp _=>true
 | AlignedRow i=>Nat.eqb (gpr i) b && (offset i mod 64=?0) &&
                  (lo<=?offset i) && (offset i+64<=?hi)
 | _=>false end.
Fixpoint scan text b lo hi off n := match n with O=>Some off | S k=>
 if off<?0 then None else match ScalarBytes.decode (skipn (Z.to_nat off) text) with
 | Some(width,i)=>if accepts b lo hi i then scan text b lo hi (off+Z.of_nat width) k else None
 | None=>None end end.
Definition interval a lo hi x:=a+lo<=x<a+hi.

Lemma next o off n op b lo hi a s c : accepts b lo hi op=true ->
 regs s b=a -> a mod 64=0 -> 0<=a+lo -> a+hi<=2^64 ->
 exists t ws,step o off n op s c=Some(State (Running(off+Z.of_nat n)) t c,ws) /\
 regs t=regs s /\ confined (interval a lo hi) ws.
Proof.
 intros Check Base Al L H;destruct op;cbn [accepts] in Check;try discriminate.
 - destruct i as [[d op]| | | | |];try discriminate;do 2 eexists;repeat split;constructor.
 - do 2 eexists;repeat split;constructor.
 - destruct i as [store r reg disp];cbn [gpr offset] in Check.
   repeat rewrite andb_true_iff in Check;destruct Check as [[[Reg A] Low] High].
   apply Nat.eqb_eq in Reg;subst reg;apply Z.eqb_eq in A;apply Z.leb_le in Low,High.
   assert (Addr:word(regs s b+disp)=a+disp) by (rewrite Base;apply word_fits;unfold word64;lia).
   assert (Align:(a+disp) mod 64=0) by (rewrite Z.add_mod,Al,A by lia;reflexivity).
   destruct store;cbn [step offset gpr zmm writing];rewrite Addr,Align;do 2 eexists;split;[reflexivity| |reflexivity|].
   + split;[reflexivity|constructor;[|constructor]]. intros x X;change (a+disp<=x<a+disp+64) in X;unfold interval;lia.
   + split;[reflexivity|constructor].
Qed.

Theorem execute o text b lo hi a : forall n off last s c,
 scan text b lo hi off n=Some last -> regs s b=a -> a mod 64=0 -> 0<=a+lo -> a+hi<=2^64 ->
 exists t ws,run n (ScalarBytes.fetch o text) (State (Running off) s c)=
   Some(State (Running last) t c,ws) /\ regs t=regs s /\ confined (interval a lo hi) ws.
Proof.
 induction n as [|n IH];intros off last s c Scan Base Al L H.
 - injection Scan as <-;exists s,[];repeat split;constructor.
 - cbn [scan] in Scan;destruct (off<?0) eqn:Pos;try discriminate.
   destruct (ScalarBytes.decode _) as [[w op]|] eqn:Bytes;try discriminate.
   destruct (accepts _ _ _ _) eqn:Ok;try discriminate.
   destruct(next o off w _ _ _ _ _ s c Ok Base Al L H) as [mid [own [Step [G Safe]]]].
   destruct(IH _ _ mid c Scan ltac:(now rewrite G) Al L H) as [t [tail [Run [Regs Rest]]]].
   exists t,(own++tail);split.
   + cbn [run ScalarBytes.fetch loc cpu_state cf];rewrite Pos,Bytes,Step,Run;reflexivity.
   + split;[now rewrite Regs,G|apply Forall_app;auto].
Qed.

(* Bound the vector registers overwritten by a straight-line block. Stores
   preserve the entire register file even when their source is a high ZMM. *)
Definition writes_below (first:nat) op := match op with
 | BroadcastRip d _ | QwordOp (Alu (d,_)) | QwordOp (Or d _ _)
 | QwordOp (Permute2 d _ _) | QwordOp (AlignedRip d _) | QwordOp (SubRip d _ _) | QwordOp (MemoryArithmetic _ d _ _ _) => (d<?first)%nat
 | AlignedRow i=>writing i || (zmm i<?first)%nat
 | _=>false end.
Fixpoint check_registers text first off n := match n with O=>true | S k=>
 if off<?0 then false else match ScalarBytes.decode (skipn (Z.to_nat off) text) with
 | Some(width,i)=>writes_below first i && check_registers text first (off+Z.of_nat width) k
 | None=>false end end.

Lemma upper_step first o off n op s c t ws : writes_below first op=true -> step o off n op s c=Some(t,ws) ->
 loc t=Running(off+Z.of_nat n) /\ forall j r,(first<=r)%nat -> vectors(cpu_state t) j r=vectors s j r.
Proof.
 destruct op;cbn [writes_below];try discriminate.
 - destruct i as [[dst op]| | | | |];cbn [step qword_op option_map];
     try destruct (_ mod 64=?0);try discriminate;
     intros D R;injection R as <- <-;split;try reflexivity;intros j high H;
     cbn [cpu_state vectors vector_dest];unfold Instructions.put;
     apply Nat.ltb_lt in D;match goal with |- context[Nat.eqb ?dst high]=>rewrite (proj2 (Nat.eqb_neq dst high) ltac:(lia));reflexivity end.
 - intros D R;injection R as <- <-;split;[reflexivity|];intros j high H;
   cbn [cpu_state vectors];unfold Instructions.put;apply Nat.ltb_lt in D;
   match goal with |- context[Nat.eqb ?dst high]=>rewrite (proj2 (Nat.eqb_neq dst high) ltac:(lia));reflexivity end.
 - destruct i as [store dst b disp];destruct store;cbn [step writing offset gpr zmm orb];
     destruct (_ mod 64=?0);try discriminate;intros D R;injection R as <- <-;split;try reflexivity.
   intros j high H;cbn [cpu_state vectors vector_dest];unfold Instructions.put;apply Nat.ltb_lt in D;
   match goal with |- context[Nat.eqb ?dst high]=>rewrite (proj2 (Nat.eqb_neq dst high) ltac:(lia));reflexivity end.
Qed.

Theorem upper_registers o text first : forall n off s c t ws,
 check_registers text first off n=true ->
 run n (ScalarBytes.fetch o text) (State (Running off) s c)=Some(t,ws) ->
 forall j r,(first<=r)%nat -> vectors(cpu_state t) j r=vectors s j r.
Proof.
 induction n as [|n IH];intros off s c t ws C Run.
 - injection Run as <- <-;reflexivity.
 - cbn [check_registers] in C;cbn [run ScalarBytes.fetch loc cpu_state cf] in Run.
   destruct (off<?0);try discriminate;destruct (ScalarBytes.decode _) as [[w op]|];try discriminate.
   apply andb_true_iff in C as [K Tail];destruct(step _ _ _ _ _ _) as [[u prefix]|] eqn:S0;try discriminate.
   destruct(upper_step _ _ _ _ _ _ _ _ _ K S0) as [At Same].
   destruct u as [pc mid mcf];cbn [loc] in At;subst pc.
   destruct(run _ _ _) as [[v more]|] eqn:Next;try discriminate;injection Run as <- <-.
   intros j r H;rewrite (IH _ _ _ _ _ Tail Next j r H);apply Same,H.
Qed.
