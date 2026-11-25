From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.StoreInstructions execution.MappedFetch execution.InstructionRoute memory.Alignment memory.ByteMemory memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* PUSH RBP; MOV RBP,RSP; PUSH RBX,R12,R13,R14,R15. Offsets are relative
   to the address where the caller found this sequence in the linked text. *)
Definition pushes:list line:=[(0,1%nat,SaveG 5);(1,3%nat,CopyG 5 4);
 (4,1%nat,SaveG 3);(5,2%nat,SaveG 12);(7,2%nat,SaveG 13);(9,2%nat,SaveG 14);(11,2%nat,SaveG 15)].
Definition stores origin top (rs:nat->Z):=[
 qword (word(origin+0)) (top-8) (rs 5%nat);qword (word(origin+4)) (top-16) (rs 3%nat);
 qword (word(origin+5)) (top-24) (rs 12%nat);qword (word(origin+7)) (top-32) (rs 13%nat);
 qword (word(origin+9)) (top-40) (rs 14%nat);qword (word(origin+11)) (top-48) (rs 15%nat)].
Lemma confined origin top rs : WriteTrace.confined (fun x=>top-48<=x<top) (stores origin top rs).
Proof.
 apply Forall_forall;intros w [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]] x X;unfold touches in X;
 cbn [qword address size] in X;change (Z.of_nat 8) with 8 in X;lia.
Qed.

Lemma save text origin s c top : linked text pushes -> regs s 4%nat=top -> 48<=top<2^64 ->
 exists u,run 7 (ScalarBytes.fetch origin text) (State(Running 0) s c)=Some(State(Running 13) u c,stores origin top (regs s)) /\
 regs u 4%nat=top-48 /\ regs u 5%nat=top-8 /\
 (forall r,r<>4%nat -> r<>5%nat -> regs u r=regs s r).
Proof.
 intros Code SP Fit;eexists;split.
 - apply (InstructionRoute.checked _ _ _ Code);cbn [pushes follow loc cf cpu_state step option_map app snd caller_stores caller_step apply_stack stack_step result_regs result_mem target_ip with_words
    push push_words set set_regs regs mem put Nat.eqb];rewrite SP.
   repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64 in *;lia)) end.
   replace (top-8-8) with (top-16) by ring;replace (top-16-8) with (top-24) by ring;
   replace (top-24-8) with (top-32) by ring;replace (top-32-8) with (top-40) by ring;
   replace (top-40-8) with (top-48) by ring;reflexivity.
 - cbn [snd with_words regs put set set_regs Nat.eqb];split;[reflexivity|split;[reflexivity|]].
   intros r S B;destruct r as [|[|[|[|[|[|r]]]]]];congruence || reflexivity.
Qed.

Definition allocation bytes:list line:=[(13,4%nat,AndImmediate 4 (-64));(17,7%nat,Sub64 4 bytes)].
Definition bottom top bytes:=top-48-(top-48) mod 64-bytes.
Lemma allocate text origin s c top bytes : linked text (allocation bytes) -> regs s 4%nat=top-48 ->
 0<=bytes -> bytes+112<=top<2^64 -> exists u flags,
 run 2 (ScalarBytes.fetch origin text) (State(Running 13) s c)=Some(State(Running 24) u flags,[]) /\
 regs u 4%nat=bottom top bytes /\ mem u=mem s /\ (forall r,r<>4%nat -> regs u r=regs s r).
Proof.
 intros Code SP N Fit;do 2 eexists;split.
 - apply (InstructionRoute.checked _ _ _ Code);reflexivity.
 - cbn [allocation follow loc cf cpu_state step option_map app with_zf set set_regs regs mem put Nat.eqb].
   rewrite SP,and_rsp_64;pose proof(Z.mod_pos_bound (top-48) 64 ltac:(lia)).
   repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64 in *;lia)) end.
   split;[reflexivity|split;[reflexivity|intros r R;destruct r as [|[|[|[|[|r]]]]];congruence || reflexivity]].
Qed.
