From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute memory.ByteMemory abi.SysV.
Import ListNotations. Local Open Scope Z_scope.

(* The inverse of the six-register frame-pointer prologue. The entry stack
   word at top is still live for a tail-called routine after the last POP. *)
Definition path off:list line:=[(off,4%nat,LeaG 4 (Address 5 None (-40)));(off+4,2%nat,RestoreG 15);
 (off+6,2%nat,RestoreG 14);(off+8,2%nat,RestoreG 13);(off+10,2%nat,RestoreG 12);
 (off+12,1%nat,RestoreG 3);(off+13,1%nat,RestoreG 5)].
Definition slot (g:nat):=match g with 5%nat=>8 | 3%nat=>16 | 12%nat=>24 | 13%nat=>32 | 14%nat=>40 | _=>48 end.
Definition saved m top (rs:nat->Z):=forall g,In g sysv_saved -> read_word m (top-slot g)=rs g.
Definition restored top s:=fold_left pop [15;14;13;12;3;5]%nat (set s 4 (top-48)).

Lemma execute o text off s c top rs:linked text (path off) -> 48<=top<2^64 -> regs s 5%nat=top-8 ->
 saved (mem s) top rs -> let u:=restored top s in
 run 7 (ScalarBytes.fetch o text) (State(Running off) s c)=Some(State(Running(off+14)) u c,[]) /\
 mem u=mem s /\ regs u 4%nat=top /\ (forall g,In g sysv_saved -> regs u g=rs g) /\
 (forall g,g<>4%nat -> ~In g sysv_saved -> regs u g=regs s g).
Proof.
 intros Code Fit BP Slots u.
 assert (Start:word(regs s 5%nat+0+ -40)=top-48) by (rewrite BP;replace (top-8+0+ -40) with (top-48) by ring;apply word_fits;unfold word64;lia).
 split.
 - apply (InstructionRoute.checked _ _ _ Code);cbn [path follow step loc cpu_state cf option_map app effective].
   repeat match goal with |- context[Z.eqb ?a ?b]=>rewrite (proj2(Z.eqb_eq a b) ltac:(change (a=b);lia)) end.
   cbn [option_map app];rewrite Start;replace (off+13+Z.of_nat 1) with (off+14) by ring;reflexivity.
 - unfold u,restored;cbn [fold_left pop stack_step apply_stack with_words result_regs result_mem set set_regs mem regs put Nat.eqb].
   unfold stack_top,advance_rsp;cbn [put Nat.eqb].
   repeat match goal with |-context[word ?v]=>rewrite (word_fits v ltac:(unfold word64 in *;lia)) end.
   split;[reflexivity|split;[ring|split]].
   + intros g [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];cbn [put Nat.eqb];
     match goal with |-read_word _ ?a=rs ?g =>
       replace a with (top-slot g) by (cbn [slot];ring);apply Slots;simpl;tauto end.
   + intros g Other Free;unfold sysv_saved in Free;cbn [In] in Free;unfold put;
     repeat match goal with |-context[Nat.eqb ?i g]=>destruct(Nat.eqb_spec i g);[intuition congruence|] end;reflexivity.
Qed.
