From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute memory.ByteMemory.
Import ListNotations. Local Open Scope Z_scope.

(* Consecutive RIP-relative broadcasts. Each offset is relative to the
   end of its ten-byte instruction; the words themselves are eight bytes. *)
Fixpoint route (n:nat) pc dst literal:list line:=match n with O=>[] | S k=>
 (pc,10%nat,BroadcastRip dst (literal-(pc+10)))::route k (pc+10) (S dst) (literal+8) end.

Lemma load origin text n : forall pc dst literal s c,
 linked text (route n pc dst literal) ->
 exists t,run n (ScalarBytes.fetch origin text) (State(Running pc) s c)=Some(State(Running(pc+10*Z.of_nat n)) t c,[]) /\
 regs t=regs s /\ mem t=mem s /\ flag t=flag s /\
 (forall j i,(i<n)%nat -> vectors t j (dst+i)%nat=read_word (mem s) (word(origin+literal+8*Z.of_nat i))) /\
 forall j r,(r<dst \/ dst+n<=r)%nat -> vectors t j r=vectors s j r.
Proof.
 induction n as [|n IH];intros pc dst literal s c Code.
 - exists s;replace (pc+10*Z.of_nat O) with pc by ring;repeat split;intros;try reflexivity;lia.
 - cbn [route] in Code;apply Forall_cons_iff in Code as [[Pos Dec] Tail].
   set (a:=word(origin+literal));set (mid:=vector_dest s dst (fun _=>read_word (mem s) a)).
   assert (One:step origin pc 10 (BroadcastRip dst (literal-(pc+10))) s c=Some(State(Running(pc+10)) mid c,[])).
   { cbn [step];replace (origin+(pc+Z.of_nat 10)+(literal-(pc+10))) with (origin+literal) by ring;reflexivity. }
   destruct(IH (pc+10) (S dst) (literal+8) mid c Tail) as [t [Steps [G [M [F [Rows Keep]]]]]].
   exists t;split.
   + cbn [run ScalarBytes.fetch loc cf cpu_state];rewrite (proj2(Z.ltb_ge _ _) Pos),Dec,One,Steps.
     replace (pc+10+10*Z.of_nat n) with (pc+10*Z.of_nat(S n)) by lia;reflexivity.
   + split;[exact G|split;[exact M|split;[exact F|]]];split.
     * intros j [|i] Bound.
       -- rewrite Nat.add_0_r,Keep by lia;unfold mid,vector_dest;cbn [vectors];unfold put;rewrite Nat.eqb_refl.
          replace (origin+literal+8*Z.of_nat O) with (origin+literal) by ring;reflexivity.
       -- replace (dst+S i)%nat with (S dst+i)%nat by lia;rewrite Rows by lia.
          replace (origin+(literal+8)+8*Z.of_nat i) with (origin+literal+8*Z.of_nat(S i)) by lia;reflexivity.
     * intros j r Outside;rewrite Keep by lia;unfold mid,vector_dest;cbn [vectors];unfold put;now rewrite (proj2(Nat.eqb_neq dst r) ltac:(lia)).
Qed.
