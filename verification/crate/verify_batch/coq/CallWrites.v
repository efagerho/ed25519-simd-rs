From Coq Require Import List ZArith Lia.
From Machine Require Import abi.TracedCalls execution.LinkedCalls execution.ScalarBytes
 execution.WordBounds memory.WriteTrace memory.ByteMemory.
From Machine Require execution.MappedFetch.
From Ed25519Simd.SignatureScalar Require Audit Object ObjectBytes OrderBytes Program.
From Ed25519Simd.PrepareChunk Require Staging Caller Audit Object.
From Ed25519Simd.Sha512Challenge Require Audit Object ObjectBytes LiteralBytes Frame
 Control Execution Writes.
From Ed25519Simd.Zip215 Require Audit Object ScatterBytes ScatterTrace.
From Ed25519Simd.VerifyBatch Require Import Lane Rows Prepare Hash Candidate Scatter Return.
Local Open Scope Z_scope.

(* A callee may borrow the frame below the wrapper's five saved GPRs.
   Its return and every byte of those saved words remain owned by the wrapper. *)
Definition nested_writable e x :=
 span (sp e-16384) (16384-40) x \/ span (Return.scratch e) 25344 x \/
 span (Return.output e) (Z.of_nat (count e)) x.

Lemma nested_in_root e : includes (Return.writable e) (nested_writable e).
Proof. intros x [S|Other];[left;unfold span in *;lia|now right]. Qed.

Lemma protected_slots e : placement e -> forall x,sp e-40<=x<sp e+8 -> ~nested_writable e x.
Proof.
 intros P x Limits [Stack|[Scratch|Out]];unfold span in *.
 - lia.
 - destruct (scratch_stack _ P);lia.
 - destruct (out_stack _ P);lia.
Qed.

Lemma saved_bytes e ws : placement e -> confined (nested_writable e) ws ->
 forall before x,sp e-40<=x<sp e+8 -> replay before ws x=before x.
Proof. intros P W before x X;eapply WriteTrace.frame;[exact W|exact (protected_slots _ P _ X)]. Qed.

(* Embed the callee's real argument ranges in the root's allocations. The
   count of descriptors and the load bias need no fixed upper bound here. *)
Lemma hash_borrow c :
 includes (nested_writable (entry c)) (Frame.writable (hash_entry c)).
Proof.
 intros x H;unfold Frame.writable,Frame.frame,Frame.sp,Frame.dst in H.
 change (let a:=stack_base c in
  a-8-8-(a-8-8) mod 64-704-8<=x<a-8 \/ a<=x<a+512) in H.
 unfold stack_base,Rows.frame in H. left;unfold span,sp.
 pose proof (Z.mod_pos_bound (regs (entry c) 4%nat-1000-8-8) 64 ltac:(lia));lia.
Qed.

Lemma prepare_borrow c a n : List.In (a,n)
 ((Staging.scratch (p c),25344)::(Staging.selected (p c),80)::(Staging.stack (p c)-4096,4120)::nil) ->
 includes (nested_writable (entry c)) (span a n).
Proof.
 intros [E|[E|[E|[]]]] x X;injection E as <- <-.
 - right;left;exact X.
 - left;change (sp (entry c)-1000+768<=x<sp (entry c)-1000+768+80) in X;unfold span;lia.
 - left. unfold p,preparation in X;cbn [Staging.stack] in X;unfold Rows.frame,sp,span in *.
   destruct (Lane.strict (mode c));lia.
Qed.

Lemma ladder_borrow c flat x :
 let s:=ladder_with c flat in
 span (regs s 4%nat-5032) 5040 x \/ span (regs s 7%nat) 1280 x ->
 nested_writable (entry c) x.
Proof.
 cbv zeta. intro X;left. change (span (k_addr c-8-5032) 5040 x \/ span (point_addr c) 1280 x) in X.
 unfold k_addr,point_addr,stack_base,Rows.frame,span,sp in *.
 pose proof (Z.mod_pos_bound (regs(entry c) 4%nat-1000-8-48) 64 ltac:(lia));lia.
Qed.

Definition hash_events c :=
 let pc:=Sha512Challenge.ObjectBytes.address in let ro:=LiteralBytes.address in
 let bias:=slide c in let s:=hash_entry c in let plan:=Control.expected pc ro in
 Writes.events (bias+pc) s (bias+Control.upper plan) (bias+Control.lower plan)
 (Execution.group_constants (mem s) bias (Control.keys plan))
 (fun _=>Execution.initial_at (mem s) (bias+ro)).
Definition digit_events c :=
 let site:=SignatureScalar.ObjectBytes.address in let ro:=OrderBytes.address in
 let n:=Z.of_nat(length SignatureScalar.ObjectBytes.symbol_bytes) in
 Staging.scalar_prefix PrepareChunk.Audit.common_pc (p c) (entry c) (slide c) ++
 SignatureScalar.Audit.digit_writes site n ro (slide c)
   (Staging.scalar_entry PrepareChunk.Audit.common_pc (p c) (entry c) (slide c)) (masks c).

Record footprint : Prop := {
 prepare_regions : forall c a n, In (a,n)
   ((Staging.scratch (p c),25344)::(Staging.selected (p c),80)::(Staging.stack (p c)-4096,4120)::nil) ->
   includes (nested_writable (entry c)) (span a n);
 ladder_regions : forall c m x, let s:=ladder_with c m in
   span (regs s 4%nat-5032) 5040 x \/ span (regs s 7%nat) 1280 x -> nested_writable (entry c) x;
 hash_stores : forall c, Hash.abi c ->
   confined (nested_writable (entry c)) (hash_events c) /\ forall result, Hash.runs c=Some result ->
   forall x, Execution.after result x=replay (mem (hash_entry c)) (hash_events c) x;
 scalar_stores : forall c, Prepare.placement c -> confined (nested_writable (entry c)) (digit_events c) /\
   forall x, mem (scalar_out c) x=replay (Staging.original (p c)) (digit_events c) x;
 scatter_stores : forall e s pc carry ws last, Return.placement e ->
   regs s 6%nat=output e -> regs s 2%nat=Z.of_nat (count e) ->
   MappedFetch.mapped (mem s) pc ScatterBytes.symbol_bytes ->
   (forall x,pc<=x<pc+Z.of_nat (length ScatterBytes.symbol_bytes) ->
      ~span (output e) (Z.of_nat (count e)) x) ->
   MappedFetch.steps pc (length ScatterBytes.symbol_bytes) (State (Running 0) s carry) ws last ->
   confined (nested_writable e) ws /\ mem (cpu_state last)=replay (mem s) ws
}.
Theorem embedded : footprint.
Proof.
 constructor;[apply prepare_borrow|apply ladder_borrow| | |].
 - intros c [P _]. destruct (Sha512Challenge.Audit.write_footprint _ _ _ _
     Sha512Challenge.Object.assembled_sha512_challenge_correct (slide c) (hash_entry c) P) as [Safe Replay].
   split;[eapply lend;[apply hash_borrow|exact Safe]|exact Replay].
 - intros c Place.
   pose proof (PrepareChunk.Audit.scalar_returns PrepareChunk.Object.assembled_prepare_chunk_correct
     (p c) (entry c) (masks c) (slide c) (Prepare.scalar_placement _ Place)) as H.
   unfold PrepareChunk.Audit.scalar_handoff in H;unfold scalar_out,Staging.scalar_run.
   destruct (SignatureScalar.Program.run _ _ _ _ _ _) as [ip out];cbn [snd].
   destruct H as [_ [_ [_ [Replay Safe]]]]. split;[|exact Replay].
   eapply lend;[|exact Safe]. intros x [Stack|Digits].
   + left;unfold Staging.workspace,Caller.frame,Caller.allocation,Caller.saves,p,preparation,Rows.frame,sp,span in *.
     cbn [Staging.stack length Z.of_nat Pos.of_succ_nat Pos.succ] in Stack.
     destruct (Lane.strict (mode c));lia.
   + right;left;change (Return.scratch (entry c)+512<=x<Return.scratch (entry c)+512+512) in Digits.
     unfold span;lia.
 - intros e s pc carry ws last P D N Image Apart Run.
   assert (Size:word64 (Z.of_nat (count e))).
   { unfold count;pose proof (proj1 (initial_cpu _ P) 6%nat) as W.
     unfold word64 in *;rewrite Z2Nat.id by lia;exact W. }
   assert (All:forall xs mid,steps pc ScatterBytes.symbol_bytes (State (Running 0) s carry) xs mid ->
      confined (span (output e) (Z.of_nat (count e))) xs).
   { intros xs mid Pfx.
     pose proof (Zip215.Audit.scatter_writes Zip215.Object.assembled_zip215_correct
       pc s carry xs mid) as H.
     unfold ScatterTrace.length64,ScatterTrace.destination in H;rewrite D,N in H.
     exact (proj1 (H Size (out_ok _ P) Pfx)). }
   apply (MappedFetch.same_prefixes pc ScatterBytes.symbol_bytes (State (Running 0) s carry) _ Image Apart All) in Run.
   split;[|exact (steps_memory _ _ _ _ _ Run)].
   eapply lend;[|exact (All _ _ Run)]. intros x X;right;right;exact X.
Qed.
