From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.StoreInstructions execution.WordBounds memory.WriteTrace abi.TracedCalls.
From Machine Require execution.MaskTrace.
From Ed25519Simd.FullLadder Require Operands Audit Program LinkedBytes.
From Ed25519Simd.StageRound Require Audit Object ObjectBytes Program.
From Ed25519Simd.KeyTable Require Execution.
From Ed25519Simd.Radix16 Require Audit Object LinkedBytes.
From Ed25519Simd.PostHash Require Product.
From Ed25519Simd.SmallOrder Require Object Audit Program EntryBytes HelperBytes.
From Ed25519Simd.Torsion Require Object Audit Program.
From Ed25519Simd.VerifyBatch Require Import Rows Prepare Hash Candidate ProductRun Score Return CallWrites.
Local Open Scope Z_scope.

Definition stage_entry c flat n := let l:=ladder_with c flat in
 FullLadder.Operands.entry_for (FullLadder.Audit.pad_of l) l n.
Definition stage_pc c := slide c+FullLadder.LinkedBytes.stage_pc.
Definition stage_output c flat n := let s:=stage_entry c flat n in
 StageRound.Audit.placement (stage_pc c) (Z.of_nat (length StageRound.ObjectBytes.symbol_bytes)) s ->
 let ws:=StageRound.Audit.writes (stage_pc c) s in confined (nested_writable (entry c)) ws /\
 forall x,mem (snd (StageRound.Program.run (stage_pc c) s)) x=replay (mem s) ws x.

Lemma stage_writes c flat n : stage_output c flat n.
Proof.
 intro P;destruct(StageRound.Audit.write_footprint _ StageRound.Object.assembled_stage_round_correct _ _ P)
   as [W R];split;[|exact R]. eapply lend;[|exact W]. intros x X.
 apply (ladder_borrow c flat);left. set (s:=ladder_with c flat) in *.
 change (let sp:=regs s 4%nat in let pad:=sp mod 64 in
    sp+(-64-pad-3520)<=x<sp+(-64-pad-3520)+3520) in X.
 unfold span. pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia)). cbv zeta in X;lia.
Qed.

Definition digest_push c flat :=
 caller_stores (slide c) (digest_site (mode c)) digest_op (before_reducer c flat).
Definition digest_output c flat ip out := let s:=reducer c flat in
 ProductRun.geometry c -> ByteMemory.byte_memory flat -> Product.reduce_call (slide c) s ip out ->
 digest_binding (mode c) /\
 caller_step (slide c) (digest_site (mode c)) digest_op (before_reducer c flat)=
   (word (slide c+Radix16.LinkedBytes.wrapper_pc),s) /\ ip=word (digest_next c) /\
 exists ws,Radix16.Audit.traced (slide c) Radix16.LinkedBytes.wrapper_pc Radix16.LinkedBytes.reducer_pc
   (Radix16.Audit.size Radix16.LinkedBytes.symbol_bytes) s ip out ws /\
 let all:=digest_push c flat++ws in
 (forall x,mem out x=replay flat all x) /\
 forall pre suffix,all=pre++suffix -> confined (nested_writable (entry c)) pre.
Lemma digest_writes c flat ip out : digest_output c flat ip out.
Proof.
 intros Space M Run;destruct (ProductRun.reducer_layout _ Space flat M) as [P W].
 assert (Fit:word64 (k_addr c-8)) by exact (proj1 W 4%nat).
 pose proof (dispatched_reducer c flat Fit) as Dispatch.
 destruct (Radix16.Audit.run_correct _ _ _ _ Radix16.Object.assembled_digest_to_radix16_correct
   (slide c) _ P W) as [last [_ [Unique _]]].
 destruct (Unique _ _ Run) as [IP _];rewrite reducer_return in IP.
 destruct (Radix16.Audit.write_footprint _ _ _ _ Radix16.Object.assembled_digest_to_radix16_correct
   (slide c) _ _ _ P W Run) as [log [T [Replay Bounds]]].
 split;[apply linked_digest_call|split;[exact Dispatch|split;[exact IP|]]].
 exists log;split;[exact T|split].
 - intro x;rewrite replay_app. pose proof (caller_store_memory (slide c) (digest_site (mode c))
     digest_op (before_reducer c flat)) as Step;rewrite Dispatch in Step;cbn [snd] in Step.
   change (mem (reducer c flat)=replay flat (digest_push c flat)) in Step;rewrite <-Step;apply Replay.
 - assert (Protected:forall x,
      k_addr c<=x<k_addr c+512 \/ k_addr c-24<=x<k_addr c -> nested_writable (entry c) x).
   { intros x X;left;unfold k_addr,point_addr,stack_base,Rows.frame,span,sp in *.
     pose proof (Z.mod_pos_bound (regs(entry c) 4%nat-1000-8-48) 64 ltac:(lia));lia. }
   assert (All:confined (nested_writable (entry c)) (digest_push c flat++log)).
   { apply Forall_app;split.
     - apply Forall_cons;[|constructor]. intros x X;apply Protected;right.
       change (word (k_addr c-8)<=x<word (k_addr c-8)+8) in X;rewrite (word_fits _ Fit) in X;lia.
     - eapply lend;[|exact (Bounds log nil (eq_sym (app_nil_r _)))]. intros x X;apply Protected.
       change (k_addr c<=x<k_addr c+512 \/ k_addr c-8-16<=x<k_addr c-8) in X;lia. }
   intros pre suffix Eq;rewrite Eq in All;now apply Forall_app in All as [All _].
Qed.

Definition table_area c off n x := let base:=Hash.scratch c+3584+8*off in
 base<=x<base+8*Z.of_nat n.
Lemma table_writes c : exists log,KeyTable.Execution.returning 8=Some log /\
 forall off words,In (off,words) log ->
 includes (nested_writable (entry c)) (table_area c off (length words)).
Proof.
 destruct(KeyTable.Execution.returns 8 (or_intror eq_refl)) as [log [R [W _]]];exists log;split;[exact R|].
 intros off words I x X. unfold KeyTable.Execution.within in W.
 apply forallb_forall with (x:=(off,words)) in W;[|exact I].
 apply Bool.andb_true_iff in W as [L U];apply Z.leb_le in L,U;cbn [fst snd] in L,U.
 right;left;unfold table_area,Hash.scratch,p,preparation in X;cbn [PrepareChunk.Staging.scratch] in X.
 unfold span,Return.scratch;change (off+Z.of_nat(length words)<=2720) in U;lia.
Qed.

(* Stack offsets in the mask interpreter are relative to the aligned
   64-byte base of the callee's entry block. Convert every touched byte
   back to its absolute address at the actual decoded-policy call site. *)
Definition local_access c a x :=
 let addr:=scorer_sp c-(8+16*Z.of_nat (pad c))+MaskTrace.stack_offset a in
 addr<=x<addr+MaskTrace.byte_count a.
Definition score_writes c (tr:MaskTrace.trace MaskTrace.exit_registers) := forall input registers,
 Forall (fun a=>forall x, local_access c a x -> nested_writable (entry c) x)
   (MaskTrace.writes_on tr input registers) /\
 exists mask, MaskTrace.result tr input registers=Some mask.
Lemma score_enclosed c depth tree : 0<=depth<=1032 ->
 MaskTrace.stack_writes depth (pad c) tree -> score_writes c tree.
Proof.
 intros D Checked inputs registers.
 destruct (Checked inputs registers) as [W End];split;[|exact End].
 rewrite Forall_forall in *;intros a I x Touch;specialize (W _ I);destruct W as [_ [L U]].
 unfold local_access in Touch;left;unfold scorer_sp,point_addr,stack_base,Rows.frame,span,sp in *.
 pose proof (Z.mod_pos_bound (regs(entry c) 4%nat-1000-8-48) 64 ltac:(lia));lia.
Qed.

Definition torsion c := MaskTrace.program_writes 1500 1032 20 Torsion.Program.code (pad c).
Definition small_order c := SmallOrder.Audit.raw SmallOrder.EntryBytes.address SmallOrder.HelperBytes.address (pad c).
Record footprint : Prop := {
 digest : forall c flat ip out, digest_output c flat ip out;
 stage : forall c flat n, stage_output c flat n;
 key_table : forall c,exists log,KeyTable.Execution.returning 8=Some log /\
   forall off words,In (off,words) log -> includes (nested_writable (entry c)) (table_area c off (length words));
 scorer : forall c, score_writes c (match mode c with Policy.Zip215=>torsion c | Policy.Dalek=>small_order c end)
}.
Theorem embedded : footprint.
Proof.
 constructor;[apply digest_writes|apply stage_writes|apply table_writes|]. intro c;destruct(mode c).
 - apply (score_enclosed _ 1032);[lia|]. apply (Torsion.Audit.write_footprint _ Torsion.Object.assembled_torsion_correct).
   rewrite scorer_pad;lia.
 - apply (score_enclosed _ 24);[lia|]. apply (SmallOrder.Audit.write_footprint _ _ _ _ SmallOrder.Object.assembled_small_order_correct).
   rewrite scorer_pad;lia.
Qed.
