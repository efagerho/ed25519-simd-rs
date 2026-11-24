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
 - destruct i as [[d op]| | | |];try discriminate;do 2 eexists;repeat split;constructor.
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
