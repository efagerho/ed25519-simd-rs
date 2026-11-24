From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.ScalarWords execution.PreservedRegister execution.MappedFetch execution.LinkedRun memory.ByteMemory memory.FlatMemory
 memory.MemoryGeometry memory.WriteTrace memory.PackedMemory.
From Ed25519Simd.SignatureScalar Require ObjectBytes OrderBytes Object Audit Program.
From Ed25519Simd.PrepareChunk Require CommonBytes StrictBytes Staging.
From Ed25519Simd.VerifyBatch Require Import Policy Rows Image Return StageEntry LoadedImage PrepareNative.
From Ed25519Simd.VerifyBatch Require ScalarInputs.
Import ListNotations. Local Open Scope Z_scope.

Definition first_symbol pol := match pol with Zip215=>common | Dalek=>strict end.
Definition via_strict pol bias p := match pol with
 | Zip215=>Some p | Dalek=>segment (bias+strict) StrictBytes.symbol_bytes 3 p end.
Definition to_scalar bias := segment (bias+common) CommonBytes.symbol_bytes 17.
Definition scalar_code := SignatureScalar.ObjectBytes.symbol_bytes.
Definition scalar_size := Z.of_nat(length scalar_code).
Definition scalar_call bias ks p :=
 let s:=machine p in
 if ip p=?bias+scalar then
 if list_eq_dec Z.eq_dec (snapshot (mem s) (bias+scalar) (length scalar_code)) scalar_code then
   let '(back,t):=SignatureScalar.Program.run scalar scalar_size OrderBytes.address bias s ks in
   let writes:=SignatureScalar.Audit.digit_writes scalar scalar_size OrderBytes.address bias s ks in
   Some(Cursor back t (carry p) (log p++writes))
 else None else None.

Definition observe pol bias entry text e c ks :=
 bind (StageEntry.observe entry text e c) (fun r=>
 let p:=LinkedRun.finish entry (LinkedRun.initial entry e c) r in
 bind (via_strict pol bias p) (fun common_entry=>
 bind (to_scalar bias common_entry) (scalar_call bias ks))).

Definition common_top pol e := Rows.frame e-8-(match pol with Zip215=>0 | Dalek=>16 end).

Lemma in_common pol : In (common,CommonBytes.symbol_bytes) (children pol).
Proof. apply in_or_app;left;left;reflexivity. Qed.
Lemma in_strict : In (strict,StrictBytes.symbol_bytes) (children Dalek).
Proof. apply in_or_app;right;left;reflexivity. Qed.
Lemma in_scalar pol : In (scalar,scalar_code) (children pol).
Proof. apply in_or_app;left;right;left;reflexivity. Qed.

Section Loaded.
Variables (pol:policy) (bias:Z) (e:cpu).
Hypothesis image : loaded pol bias (mem e) (writable e).
Lemma mapped_now p addr text : accounted e (writable e) p ->
 In (addr,text) (children pol) ->
 mapped (mem(machine p)) (bias+addr) text /\
 (forall x,bias+addr<=x<bias+addr+Z.of_nat(length text)->~writable e x).
Proof.
 intros Acc InCode. assert (Sep: forall x,bias+addr<=x<bias+addr+Z.of_nat(length text)->~writable e x).
 { intros x X;apply (immutable _ _ _ _ image);left;exists addr,text;auto. }
 split;[eapply image_after;[exact Acc|exact (proj2 (symbols _ _ _ _ image _ _ InCode))|exact Sep]|exact Sep].
Qed.
Lemma mapped_word addr text : In (addr,text) (children pol) -> 0<Z.of_nat(length text) -> word64(bias+addr).
Proof. intros I N;destruct(proj1(symbols _ _ _ _ image _ _ I));unfold word64;lia. Qed.
End Loaded.

Local Lemma ret_memory slide pc s : mem(snd(caller_step slide pc LinkedCalls.Return s))=mem s.
Proof. reflexivity. Qed.
Lemma scalar_returns bias s ks ret top :
 word64 top -> regs s 4%nat=top -> read_word (mem s) top=ret -> word64 ret ->
 disjoint (regs s 7%nat) 512 top 8 ->
 let '(ip,out):=SignatureScalar.Program.run scalar scalar_size OrderBytes.address bias s ks in
 ip=ret /\ regs out 4%nat=word(top+8).
Proof.
 intros Top SP Return Ret Sep.
 set (last:=SignatureScalar.Program.body OrderBytes.address bias s ks).
 assert (Stack:regs last 4%nat=top).
 { unfold last,SignatureScalar.Program.body;rewrite upper_registers;exact SP. }
 change (word (read_word (mem last) (word(regs last 4%nat)))=ret /\ word(regs last 4%nat+8)=word(top+8)).
 rewrite Stack,(word_fits _ Top). split;[|reflexivity].
 pose proof (SignatureScalar.Audit.write_footprint _ _ _ _ SignatureScalar.Object.assembled_signature_scalar_correct bias s ks) as [W M].
 change (forall x,mem(snd(caller_step bias (scalar+scalar_size-1) LinkedCalls.Return last)) x=WriteTrace.replay (mem s) (SignatureScalar.Audit.digit_writes scalar scalar_size OrderBytes.address bias s ks) x) in M.
 rewrite ret_memory in M.
 assert (Same:read_word (mem last) top=read_word (mem s) top).
 { apply preserved_read with (outside:=fun x=>~SignatureScalar.Audit.output s x).
   - intros x Outside.
     rewrite M;apply (WriteTrace.frame _ _ W),Outside.
   - intros k K;unfold SignatureScalar.Audit.output,disjoint in *;change (0<=k<8) in K;lia. }
 now rewrite Same, Return, (word_fits _ Ret).
Qed.

Definition input_view e p := well_formed(machine p) /\
 ScalarInputs.matrix e (machine p) /\ StageEntry.metadata e (mem(machine p)) /\ StageEntry.saved_caller e (machine p).
Definition arguments e p top :=
 regs (machine p) 4%nat=top /\ regs (machine p) 7%nat=Return.scratch e /\
 regs (machine p) 6%nat=Rows.frame e+512 /\ Prologue.output_registers e (machine p) /\
 regs(machine p) 12%nat=Prologue.rows_left (regs e 6%nat) /\ input_view e p.

Definition caller_word entry e m :=
 read_word m (Rows.frame e-8)=word(entry+offset Prepared).
Definition return_slots pol bias entry e m :=
 caller_word entry e m /\ match pol with
 | Zip215=>True | Dalek=>read_word m (common_top Dalek e)=word(bias+strict+9) end.

Lemma slots_preserved pol bias entry e m m' :
 (forall x,common_top pol e<=x<Rows.frame e -> m' x=m x) ->
 return_slots pol bias entry e m -> return_slots pol bias entry e m'.
Proof.
 intros Same [Root Shim];split.
 - unfold caller_word in *;rewrite <-Root;apply PrepareChunk.Staging.read_block.
   intros k K;apply Same;unfold common_top;destruct pol;lia.
 - destruct pol;[exact I|]. rewrite <-Shim;apply PrepareChunk.Staging.read_block.
   intros k K;apply Same;unfold common_top;lia.
Qed.

Lemma reach_common pol bias entry e p : Return.placement e -> loaded pol bias (mem e) (writable e) ->
 accounted e (writable e) p -> ip p=bias+first_symbol pol -> arguments e p (Rows.frame e-8) ->
 caller_word entry e (mem(machine p)) ->
 exists q,via_strict pol bias p=Some q /\ accounted e (writable e) q /\
 ip q=bias+common /\ arguments e q (common_top pol e) /\ return_slots pol bias entry e (mem(machine q)).
Proof.
 intros P Image Acc At Args Root. destruct pol.
 - exists p;split;[reflexivity|split;[exact Acc|split;[exact At|]]]. split;[unfold common_top;replace (Rows.frame e-8-0) with (Rows.frame e-8) by ring;exact Args|exact (conj Root I)].
 - destruct Args as [SP [DI [SI [[N Out] [Left [Words [Matrix [Indices [Spills BP]]]]]]]]].
   assert (Fit:words_fit (Rows.frame e-8)) by (destruct (stack_ok _ P) as [[L U] _];unfold words_fit,Rows.frame,sp in *;lia).
   destruct (strict_dispatch bias (machine p) (carry p) (Rows.frame e-8) SP Fit
       (mapped_word _ _ _ Image _ _ (in_common _) ltac:(vm_compute;reflexivity))) as [t [ws [R [PC [Stack [D [S [Ret [Bounds [Count [Dst R12]]]]]]]]]]].
   destruct(mapped_now _ _ _ Image _ _ _ Acc in_strict) as [Map Sep].
   assert (Safe:confined (writable e) ws).
   { eapply Forall_impl;[|exact Bounds];intros w W x X;left;specialize(W x X);unfold stack_range,Rows.frame,span,sp in *;lia. }
   pose proof(at_segment _ _ _ _ _ _ 0 _ _ Acc ltac:(rewrite Z.add_0_r;exact At) Map Sep R Safe) as [Next A].
   exists (LinkedRun.finish (bias+strict) p (t,ws));split;[exact Next|split;[exact A|]].
   cbn [LinkedRun.finish ip machine];unfold absolute;rewrite PC;split;[ring|].
   pose proof (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)) as M.
   cbn [at_pc cpu_state] in M.
   assert (Frame:forall x,Rows.frame e-8<=x -> mem(cpu_state t) x=mem(machine p) x).
   { intros x X;rewrite M;apply (WriteTrace.frame _ _ Bounds);unfold stack_range;lia. }
   split.
   + split;[exact Stack|split;[exact (eq_trans D DI)|split;[exact (eq_trans S SI)|]]].
     split;[exact (conj (eq_trans Count N) (eq_trans Dst Out))|split;[exact (eq_trans R12 Left)|]].
     split;[exact (segment_wf _ _ _ _ _ Words Next)|].
     split;[intros j sig J;rewrite <- (Matrix j sig J);apply PrepareChunk.Staging.read_block;intros k K;apply Frame;destruct sig;lia|].
     split;[eapply IndexStores.metadata_preserved;[|exact Indices];intros x X;apply Frame;lia|].
     split;[intros x X;change (mem(cpu_state t) x=Return.saved_memory e x);rewrite Frame by (unfold Rows.frame,sp in *;lia);apply Spills,X|].
     exact (eq_trans (PreservedRegister.run_keeps 5 _ StrictBytes.symbol_bytes _ _ _ _ ltac:(vm_compute;reflexivity) R) BP).
   + split;[|exact Ret]. unfold caller_word in *;rewrite <-Root.
     apply PrepareChunk.Staging.read_block;intros k K;apply Frame;lia.
Qed.

Definition saved_outputs pol e m :=
 let top:=common_top pol e in
 read_word m (top-24)=regs e 6%nat /\ read_word m (top-32)=Return.output e /\ read_word m (top-16)=Prologue.rows_left (regs e 6%nat).

Definition post pol bias entry e p :=
 ip p=bias+common+65 /\ regs (machine p) 4%nat=common_top pol e-104 /\
 accounted e (writable e) p /\ return_slots pol bias entry e (mem(machine p)) /\ saved_outputs pol e (mem(machine p)) /\
 ((0<Scatter.count e)%nat -> ScalarInputs.borrowed e -> ScalarInputs.recoded e (machine p) /\ ScalarInputs.copy_ready e (machine p) /\ StageEntry.metadata e (mem(machine p)) /\ StageEntry.saved_caller e (machine p)).
Lemma through_scalar pol bias entry e p ks : Return.placement e -> loaded pol bias (mem e) (writable e) ->
 accounted e (writable e) p -> ip p=bias+common -> arguments e p (common_top pol e) ->
 return_slots pol bias entry e (mem(machine p)) ->
 exists q, bind (to_scalar bias p) (scalar_call bias ks)=Some q /\ post pol bias entry e q.
Proof.
 intros Place Image Acc At [SP [DI [SI [[Count Out] [Left [Words [Matrix [Indices [Spills BP]]]]]]]]] Slots.
 set (top:=common_top pol e) in *.
 destruct (stack_ok _ Place) as [[Lo Hi] _]. assert (Pos:words_fit top).
 { unfold top,common_top,words_fit,Rows.frame,sp in *;destruct pol;lia. }
 assert (Table:fits64 (regs (machine p) 6%nat) 128) by (rewrite SI;unfold fits64,Rows.frame,sp in *;lia).
 assert (Apart:disjoint (top-40) 40 (regs (machine p) 6%nat+64) 64).
 { rewrite SI;unfold disjoint,top,common_top;destruct pol;lia. }
 destruct (common_dispatch bias _ (carry p) top SP Pos
     (mapped_word _ _ _ Image _ _ (in_scalar _) ltac:(vm_compute;reflexivity)) Table Apart) as [t [ws [R [[PC [Stack [Src [Dst [Ret [BX R15]]]]]] [W [Spilled Fields]]]]]].
 destruct(mapped_now _ _ _ Image _ _ _ Acc (in_common _)) as [Map Sep].
 assert (Safe:confined (writable e) ws).
 { eapply Forall_impl;[|exact W];intros w K x X;specialize(K x X);left.
   unfold span,stack_range,top,common_top,Rows.frame,sp in *;destruct pol;lia. }
 destruct(at_segment _ _ _ _ _ _ 0 _ _ Acc ltac:(rewrite Z.add_0_r;exact At) Map Sep R Safe) as [Next A].
 set (v:=LinkedRun.finish (bias+common) p (t,ws)) in *.
 assert (Target:ip v=bias+scalar) by (unfold v;cbn [LinkedRun.finish ip];unfold absolute;rewrite PC;ring).
 destruct(mapped_now _ _ _ Image _ _ _ A (in_scalar _)) as [ImageScalar _].
 assert (StackRet:word64(bias+common+65)).
 { destruct(proj1(symbols _ _ _ _ Image _ _ (in_common _))) as [L U].
   change (Z.of_nat(length CommonBytes.symbol_bytes)) with 290 in U;unfold word64;lia. }
 assert (Dest:regs (machine v) 7%nat=Return.scratch e+512).
 { change (regs (cpu_state t) 7%nat=Return.scratch e+512);rewrite Dst,DI.
   apply word_fits;destruct(scratch_ok _ Place) as [[L U] _];unfold word64;lia. }
 assert (Enough:disjoint (regs(machine v) 7%nat) 512 (top-112) 8).
 { rewrite Dest;destruct (scratch_stack _ Place);unfold disjoint,top,common_top,Rows.frame,sp in *;destruct pol;lia. }
 pose proof (scalar_returns bias (machine v) ks (bias+common+65) (top-112)
    ltac:(unfold words_fit,word64 in *;lia) Stack ltac:(change (read_word (mem(cpu_state t)) (top-112)=bias+common+65);rewrite Ret;apply word_fits,StackRet)
    StackRet Enough) as Back.
 pose proof (SignatureScalar.Audit.write_footprint _ _ _ _ SignatureScalar.Object.assembled_signature_scalar_correct
      bias (machine v) ks) as [Inside Memory].
 fold scalar_code in Inside,Memory;fold scalar_size scalar in Inside,Memory.
 destruct(SignatureScalar.Program.run scalar scalar_size OrderBytes.address bias (machine v) ks) as [resume_ip out] eqn:Call.
 destruct Back as [Back Rest].
 unfold to_scalar;rewrite Next;cbn [bind];unfold scalar_call;rewrite Target,Z.eqb_refl,(snapshot_mapped _ _ _ ImageScalar).
 destruct (list_eq_dec _ _ _) as [_|Bad];[|contradiction].
 rewrite Call; eexists;split;[reflexivity|]. unfold post;cbn [ip machine];split;[exact Back|].
 split;[rewrite Rest,word_fits;unfold words_fit,word64 in *;lia|].
 split.
 - apply append_accounted;[exact A| |exact Memory]. eapply Forall_impl;[|exact Inside].
   intros w K x X;specialize (K x X);right;left;unfold SignatureScalar.Audit.output in K;rewrite Dest in K;unfold span;lia.
 - split.
   + eapply slots_preserved;[|exact Slots]. intros x X;cbn [machine].
   rewrite Memory,(WriteTrace.frame _ _ Inside).
     * change (mem (cpu_state t) x=mem (machine p) x).
     rewrite (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R));apply (WriteTrace.frame _ _ W).
     unfold stack_range;fold top in X;lia.
     * unfold SignatureScalar.Audit.output;rewrite Dest;destruct (scratch_stack _ Place);
     unfold common_top,Rows.frame,sp in *;destruct pol;lia.
   + split.
     * unfold saved_outputs;fold top;destruct Spilled as [C [O L12]].
     rewrite Count,(word_fits _ (proj1(initial_cpu _ Place) 6%nat)) in C.
     rewrite Out in O;rewrite (word_fits (Return.output e) (proj1(initial_cpu _ Place) 2%nat)) in O.
     rewrite Left in L12;assert (Fit:word64(Prologue.rows_left(regs e 6%nat))) by
       (unfold Prologue.rows_left;destruct (_<?8);[unfold word64;lia|apply mod64_word]).
     rewrite (word_fits _ Fit) in L12;repeat split;[rewrite <-C|rewrite <-O|rewrite <-L12].
     all: apply preserved_read with (outside:=fun x=>~SignatureScalar.Audit.output (machine v) x).
     all: try (intros x X;cbn [machine];rewrite Memory;apply (WriteTrace.frame _ _ Inside),X).
     all: intros k K;change (0<=k<8) in K;unfold SignatureScalar.Audit.output;rewrite Dest;
       destruct(scratch_stack _ Place);unfold top,common_top,Rows.frame,sp in *;destruct pol;lia.
     * intros Full Borrow. assert (Data:byte_memory (mem out) /\ ScalarInputs.recoded e out).
       { eapply (ScalarInputs.from_call pol bias e v ks top resume_ip out);
         [exact Place|exact Image|exact A|exact (segment_wf _ _ _ _ _ Words Next)|
          unfold top,common_top,Rows.frame,sp in *;destruct pol;lia|exact Dest|exact Src|exact Stack|exact Borrow|exact Full| |exact Call].
       intros j J;unfold SignatureScalar.Audit.ptr;change (read_word (mem(cpu_state t)) (regs(cpu_state t) 6%nat+8*Z.of_nat j)=word(32+ScalarInputs.sig_ptr e (TailCopy.row_index e j))).
       rewrite Src,Fields by exact J;unfold ptr_row;rewrite SI.
       exact (f_equal (fun a=>word(32+a)) (Matrix j true J)). }
       assert (FrameBytes:forall x,Rows.frame e+512<=x<sp e -> mem out x=mem(machine p) x).
       { intros x X;rewrite Memory,(WriteTrace.frame _ _ Inside).
         - change (mem (cpu_state t) x=mem(machine p) x).
           rewrite (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R));apply (WriteTrace.frame _ _ W).
           unfold stack_range,top,common_top;destruct pol;lia.
         - unfold SignatureScalar.Audit.output;rewrite Dest;destruct (scratch_stack _ Place);
           unfold Rows.frame,sp in *;lia. }
       split;[exact (proj2 Data)|]. split.
       2:{ split;[eapply IndexStores.metadata_preserved;[|exact Indices];intros x X;apply FrameBytes;unfold Rows.frame,sp in *;lia|].
           split;[intros x X;rewrite FrameBytes by (unfold Rows.frame,sp in *;lia);apply Spills,X|].
           assert (BPout:regs out 5%nat=regs(machine v) 5%nat) by
             (change (regs(snd(resume_ip,out)) 5%nat=regs(machine v) 5%nat);rewrite <-Call;reflexivity).
           exact (eq_trans BPout (eq_trans (PreservedRegister.run_keeps 5 _ CommonBytes.symbol_bytes _ _ _ _ ltac:(vm_compute;reflexivity) R) BP)). }
       split;[exact (proj1 Data)|]. split.
       { intros j sig J;rewrite <- (Matrix j sig J);apply PrepareChunk.Staging.read_block;
         intros k K;apply FrameBytes;destruct sig;unfold Rows.frame,sp in *;lia. }
       assert (Keep:regs out 3%nat=regs (machine v) 3%nat /\ regs out 15%nat=regs(machine v) 15%nat).
       { change (regs (snd (resume_ip,out)) 3%nat=regs(machine v) 3%nat /\ regs (snd(resume_ip,out)) 15%nat=regs(machine v) 15%nat).
         rewrite <- Call;split;reflexivity. }
       exact (conj (eq_trans (proj1 Keep) (eq_trans BX DI)) (eq_trans (proj2 Keep) (eq_trans R15 SI))).
Qed.

Theorem from_entry pol bias pc text e c ks :
 Return.placement e -> loaded pol bias (mem e) (writable e) ->
 StageEntry.physical (bias+pc) text (first_symbol pol-pc) e ->
 exists q,observe pol bias (bias+pc) text e c ks=Some q /\ post pol bias (bias+pc) e q.
Proof.
 intros Place Loaded Start.
 destruct(Start c) as [n [N [Budget [last [writes [Run [[ABI [Matrix [Indices [Kept _]]]] [Replay Prefix]]]]]]]].
 destruct(Prefix n ltac:(lia)) as [u [pre [R Safe]]];rewrite Run in R;injection R as <- <-.
 set (p:=LinkedRun.finish (bias+pc) (LinkedRun.initial (bias+pc) e c) (last,writes)).
 assert (Acc:accounted e (writable e) p) by (split;[exact Safe|intro x;unfold p;cbn [LinkedRun.finish log machine LinkedRun.initial];now rewrite Replay]).
 destruct ABI as [Dest [SP [Ret [SI [Meta [DI Output]]]]]].
 assert (Entry:ip p=bias+first_symbol pol).
 { unfold p;cbn [LinkedRun.finish ip];unfold absolute;rewrite Dest.
   replace (bias+pc+(first_symbol pol-pc)) with (bias+first_symbol pol) by ring.
   assert (Fit:word64(bias+first_symbol pol)) by (destruct pol;
    [exact (mapped_word _ _ _ Loaded _ _ (in_common _) ltac:(vm_compute;reflexivity))|
     exact (mapped_word _ _ _ Loaded _ _ in_strict ltac:(vm_compute;reflexivity))]).
   rewrite (word_fits _ Fit);ring. }
 assert (View:input_view e p).
 { split;[exact (mapped_run_wf _ _ _ (State (Running 0) e c) _ _ (initial_cpu _ Place) Run)|].
   split;[|exact (conj Indices Kept)]. intros j sig J;unfold ScalarInputs.encoding_ptr,descriptor.
   apply PrepareChunk.Staging.read_block;intros k K. destruct sig.
   - exact (Matrix j 1%nat k J ltac:(lia) K).
   - exact (Matrix j 0%nat k J ltac:(lia) K). }
 destruct(reach_common pol bias (bias+pc) e p Place Loaded Acc Entry (conj SP (conj DI (conj SI (conj (proj1 Output) (conj (proj2 Output) View))))) Ret) as [q [Q [Acct [IP [Args Slots]]]]].
 destruct(through_scalar pol bias (bias+pc) e q ks Place Loaded Acct IP Args Slots) as [f [S Post]].
 exists f;split;[|exact Post].
 unfold observe,StageEntry.observe;rewrite Budget,Run;cbn [bind];fold p;rewrite Q;exact S.
Qed.

(* Store replay depends only on the execution. Separation is needed for the
   bounds on those stores and for progress at the expected continuation. *)
Lemma observed_memory pol bias entry text e c masks p :
 observe pol bias entry text e c masks=Some p -> replays e p.
Proof.
 unfold observe,StageEntry.observe. destruct (StageEntry.budget entry text e c) as [n|];[|discriminate].
 destruct (run n _ _) as [[stage ws]|] eqn:Prefix;[|discriminate];cbn [bind].
 set (start:=LinkedRun.finish entry (LinkedRun.initial entry e c) (stage,ws)).
 assert (P:replays e start).
 { intros x;unfold start;cbn [LinkedRun.finish LinkedRun.initial machine log].
   now rewrite (run_memory _ _ _ _ _ _ Prefix). }
 destruct (via_strict pol bias start) as [a|] eqn:Shim;[|discriminate];cbn [bind].
 assert (A:replays e a) by (destruct pol;[injection Shim as <-;exact P|eapply segment_memory;[exact P|exact Shim]]).
 destruct (to_scalar bias a) as [b|] eqn:Common;[|discriminate];cbn [bind].
 pose proof (segment_memory _ _ _ _ _ _ A Common) as B.
 unfold scalar_call;destruct (_=?_);[|discriminate]. destruct(list_eq_dec _ _ _);[|discriminate].
 pose proof (SignatureScalar.Audit.write_footprint _ _ _ _ SignatureScalar.Object.assembled_signature_scalar_correct
      bias (machine b) masks) as [_ Memory].
 fold scalar_code in Memory;fold scalar_size scalar in Memory.
 destruct(SignatureScalar.Program.run _ _ _ _ _ _) as [back out] eqn:Call.
 intro F;injection F as <-;intro x;cbn [machine log];rewrite replay_app;rewrite Memory.
 apply replay_equal,B.
Qed.
