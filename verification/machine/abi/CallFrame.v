From Coq Require Import List ZArith Lia.
From Machine Require Import execution.ScalarRefinement execution.Blocks memory.FlatMemory execution.WordBounds memory.ByteMemory abi.SysV execution.LinkedCalls.
Open Scope Z_scope.

(* At callee entry, RSP points at the return address pushed by the caller. *)
Definition sysv_return (writable : Z -> Prop) (entry out : cpu) :=
 well_formed out /\ regs out 4%nat = regs entry 4%nat + 8 /\
 (forall r, In r sysv_saved -> regs out r = regs entry r) /\
 preserved (fun x => ~writable x) (mem entry) (mem out).

Lemma project_sysv_return loc s entry final after next_rsp writable :
 (forall r, scalar_value loc (gpr (fst entry) r) = Some (regs s r)) ->
 (forall r, word64 (regs s r)) -> word64 (regs s 4%nat + 8) ->
 pointer_at (fst entry) 4 8 = Some next_rsp ->
 address_of loc next_rsp = regs s 4%nat + 8 ->
 restores_rsp entry final -> preserves_sysv entry final ->
 well_formed (export_state loc final after) ->
 preserved (fun x => ~writable x) (mem s) after ->
 sysv_return writable s (export_state loc final after).
Proof.
 intros Entry Words End Addr Next Stack Saved W Frame.
 split; [exact W|]; split.
 - unfold restores_rsp in Stack; rewrite Addr in Stack; injection Stack as R.
   unfold export_state; cbn [regs]; rewrite R.
   change (word (address_of loc next_rsp) = regs s 4%nat + 8).
   now rewrite Next, word_fits.
 - split; [|exact Frame]. intros r S.
   unfold export_state; cbn [regs]; rewrite Saved by exact S.
   unfold decode; rewrite Entry; apply word_fits, Words.
Qed.

Lemma pushed_return_word s ip : word64 ip ->
 read_word (mem (push s ip)) (regs (push s ip) 4%nat) = ip.
Proof. apply write_read_word. Qed.

(* A caller may protect any bytes outside the callee's writable region
   and the eight bytes written by the call instruction itself. *)
Lemma resume_sysv_frame s ip out writable (protected : Z -> Prop) :
 word64 (regs s 4%nat - 8) ->
 (forall x, protected x -> ~writable x /\ ~(regs s 4%nat - 8 <= x < regs s 4%nat)) ->
 sysv_return writable (push s ip) out ->
 well_formed out /\ regs out 4%nat = regs s 4%nat /\
 (forall r, In r sysv_saved -> regs out r = regs s r) /\
 preserved protected (mem s) (mem out).
Proof.
 intros SP Disjoint [W [Rsp [Reg Frame]]]; split; [exact W|]; split.
 - rewrite Rsp; change (word (regs s 4%nat - 8) + 8 = regs s 4%nat).
   rewrite word_fits by exact SP; lia.
 - split.
   + intros r H; rewrite Reg by exact H.
     destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; reflexivity.
   + intros x H; destruct (Disjoint x H) as [Outside Slot].
     rewrite Frame by exact Outside; unfold push; cbn [mem].
     rewrite word_fits by exact SP; apply write_outside; lia.
Qed.
