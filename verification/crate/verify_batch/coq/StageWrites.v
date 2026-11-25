From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.MappedFetch execution.FrameInstructions memory.MemoryGeometry
 memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require isa.VectorMoves isa.IndexedLoad isa.Move.
From Ed25519Simd.VerifyBatch Require Import Image Rows Return EntryWrites Prologue Routing.
From Ed25519Simd.VerifyBatch Require Import DescriptorStores.
Import ListNotations. Local Open Scope Z_scope.

Definition indices : list line := flat_map (fun j=>
 let src:=40*Z.of_nat j+32 in
 [(if src<?128 then 4%nat else 7%nat,Load64 0 (Address 3 None src));
  (8%nat,Store64 0 (Address 4 None (864+8*Z.of_nat j)))]) (seq 0 8).
Definition setup : list line := [(3%nat,CopyG 7 15);(8%nat,LeaG 6 (Address 4 None 512));
 (8%nat,Load64 2 (Address 4 None 936));(8%nat,LeaG 1 (Address 4 None 768))].
Definition suffix := indices++[(7%nat,Add64 3 320)]++setup.
Definition body := inputs++publish++suffix.
Definition delta_call delta := delta-offset Prepared.
Definition bound text delta :=
 decoded text (offset Stage) body /\ Prologue.at_offset text (offset CallPrepare) 5 (CallRelative (delta_call delta)).
Definition entered_with ip delta e remaining t :=
 loc t=Running (word(ip+delta)-ip) /\ regs (cpu_state t) 4%nat=Rows.frame e-8 /\
 read_word (mem (cpu_state t)) (Rows.frame e-8)=word(ip+offset Prepared) /\
 regs (cpu_state t) 6%nat=Rows.frame e+512 /\ regs (cpu_state t) 1%nat=Rows.frame e+768 /\
 regs (cpu_state t) 7%nat=Return.scratch e /\ Prologue.output_registers e (cpu_state t) /\
 regs(cpu_state t) 12%nat=remaining.
Definition entered ip delta e:=entered_with ip delta e (Prologue.rows_left (regs e 6%nat)).

Definition body_prefix := inputs++publish++indices++[(7%nat,Add64 3 320)].
Lemma setup_args origin text off s c e : decoded text off setup -> 0<=off -> placement e ->
 regs s 4%nat=Rows.frame e -> exists t,
 MappedFetch.run 4 (ScalarBytes.fetch origin text) (State (Running off) s c)=
 Some(State (Running (off+27)) t c,[]) /\ regs t 4%nat=Rows.frame e /\
 regs t 6%nat=Rows.frame e+512 /\ regs t 1%nat=Rows.frame e+768 /\
 regs t 7%nat=regs s 15%nat /\ regs t 2%nat=read_word (mem s) (Rows.frame e+936).
Proof.
 intros [A [B [C [D _]]]] O P SP.
 cbn [MappedFetch.run]. rewrite (fetch_at _ _ _ _ _ _ _ O A);cbn [ScalarBytes.step].
 rewrite (fetch_at origin text (off+3) _ _ _ _ ltac:(lia) B);cbn [ScalarBytes.step].
 rewrite (fetch_at origin text (off+3+8) _ _ _ _ ltac:(lia) C);cbn [ScalarBytes.step].
 rewrite (fetch_at origin text (off+3+8+8) _ _ _ _ ltac:(lia) D);cbn [ScalarBytes.step option_map app].
 eexists;split;[replace (off+27) with (off+3+8+8+8) by ring;reflexivity|].
 cbn [set set_regs regs mem effective Instructions.put Nat.eqb];rewrite SP,Z.add_0_r.
 repeat rewrite word_fits by (destruct (stack_ok _ P) as [[L H] _];unfold word64,Rows.frame,sp in *;lia).
 repeat split.
Qed.

Definition matrix frame s (m:bytes) := forall j f k, (j<8)%nat -> (f<4)%nat -> 0<=k<8 ->
 m (bank frame f+8*Z.of_nat j+k)=word_byte (value s j f) k.

Lemma transferred ip text e s c args cf ws : decoded text (offset Stage) body ->
 fits64 (Rows.frame e) 960 -> regs s 4%nat=Rows.frame e ->
 MappedFetch.run 41 (ScalarBytes.fetch ip text) (State (Running (offset Stage)) s c)=
 Some (State (Running (offset CallPrepare)) args cf,ws) -> matrix (Rows.frame e) s (mem args).
Proof.
 intros Code Fit SP R. destruct (prefix_decoded _ _ inputs _ Code) as [Loads Rest].
 set (after_load:=offset Stage+FrameInstructions.width inputs) in *.
 destruct (prefix_decoded _ after_load publish _ Rest) as [Stores Tail].
 set (after_store:=after_load+FrameInstructions.width publish) in *.
 pose proof (read_block ip text transpose (offset Stage) s c ltac:(change (0<=82);lia) Loads) as L.
 set (loaded:=load_vectors transpose s) in *.
 destruct (store_block ip text (Rows.frame e) (seq 0 4) Fit ltac:(repeat constructor;lia)
   after_load loaded c ltac:(change (0<=166);lia) Stores SP) as [writes V].
 set (out:=stored (Rows.frame e) (seq 0 4) loaded) in *.
 destruct (sequence ip text 864 960 (Rows.frame e) suffix ltac:(lia) Fit ltac:(reflexivity)
    after_store out c ltac:(vm_compute;discriminate) Tail SP) as [mid [cf' [rest [F [_ Bounds]]]]].
 pose proof (MappedFetch.run_append _ _ _ _ _ L _ _ _ V) as Front.
 pose proof (MappedFetch.run_append _ _ _ _ _ Front _ _ _ F) as All.
 change (MappedFetch.run 41 (ScalarBytes.fetch ip text) (State (Running (offset Stage)) s c)=
   Some (State (Running (offset CallPrepare)) mid cf',([]++writes)++rest)) in All.
 rewrite R in All;injection All as <- <- _.
 pose proof (steps_memory _ _ _ _ _ (MappedFetch.run_steps _ _ _ _ _ _ F)) as M.
 cbn [cpu_state] in M. intros j f k J H K;rewrite M,WriteTrace.frame with
   (region:=fun x=>Rows.frame e+864<=x<Rows.frame e+960) by (auto;unfold bank;lia).
 unfold out;rewrite store_payload by assumption. unfold loaded;rewrite lane_loaded by assumption;reflexivity.
Qed.

Theorem instructions_with ip text delta e remaining s c : bound text delta -> placement e ->
 regs s 4%nat=Rows.frame e -> Prologue.context_registers e s -> regs s 12%nat=remaining -> Prologue.segment ip text e 42 (offset Stage) s c (fun child=>entered_with ip delta e remaining child /\
 matrix (Rows.frame e) s (mem (cpu_state child)) /\ regs(cpu_state child) 2%nat=read_word (mem s) (Rows.frame e+936) /\
 regs(cpu_state child) 15%nat=Return.scratch e).
Proof.
 intros [Bytes Call] P SP [Scratch [Count Out]] Left. pose proof Bytes as Code.
 change (decoded text (offset Stage) (body_prefix++setup)) in Bytes.
 destruct (prefix_decoded _ _ _ _ Bytes) as [Front Args].
 assert (Frame:fits64 (Rows.frame e) 960) by
   (destruct (stack_ok _ P) as [[Lo Hi] _];unfold fits64,Rows.frame,sp in *;lia).
 destruct (sequence ip text 0 928 (Rows.frame e) body_prefix ltac:(lia) ltac:(unfold fits64 in *;lia) ltac:(reflexivity)
   (offset Stage) s c ltac:(change (0<=82);lia) Front SP) as [mid [cf [head [F [R W]]]]].
 change (offset Stage+FrameInstructions.width body_prefix) with (offset PrepareArgs) in F,Args.
 destruct (setup_args ip text (offset PrepareArgs) mid cf e Args ltac:(change (0<=353);lia) P R) as [args [A [SP' [RSI [RCX [RDI Table]]]]]].
 pose proof (kept_sequence ip text 15 body_prefix (offset Stage) s c _ _ ltac:(change (0<=82);lia)
   Front ltac:(reflexivity) F) as Keep;cbn [cpu_state] in Keep.
 assert (Live:forall r,(r=12%nat \/ r=13%nat \/ r=14%nat) -> regs args r=regs s r).
 { intros r Reg. pose proof (kept_sequence ip text r setup (offset PrepareArgs) mid cf _ _
     ltac:(change (0<=353);lia) Args ltac:(destruct Reg as [->|[->| ->]];reflexivity) A) as H.
   pose proof (kept_sequence ip text r body_prefix (offset Stage) s c _ _
     ltac:(change (0<=82);lia) Front ltac:(destruct Reg as [->|[->| ->]];reflexivity) F) as G.
   exact (eq_trans H G). }
 change (offset PrepareArgs+27) with (offset CallPrepare) in A.
 set (pc:=offset CallPrepare). set (ret:=ip+offset Prepared).
 assert (Slot:word(Rows.frame e-8)=Rows.frame e-8) by (apply word_fits;destruct (stack_ok _ P) as [[Lo Hi] _];
   unfold Rows.frame,sp,word64 in *;lia).
 set (w:=qword (word (ip+pc)) (word(regs args 4%nat-8)) ret).
 set (child:=push args ret).
 assert (Next:MappedFetch.run 1 (ScalarBytes.fetch ip text) (State (Running pc) args cf)=
   Some(State (Running (word(ip+delta)-ip)) child cf,[w])).
 { cbn [MappedFetch.run];rewrite (fetch_at ip text pc _ _ _ _ ltac:(change (0<=380);lia) Call).
   cbn [ScalarBytes.step option_map app]. change (pc+Z.of_nat 5) with (offset Prepared).
   unfold delta_call;replace (offset Prepared+(delta-offset Prepared)) with delta by ring;reflexivity. }
 pose proof (MappedFetch.run_append _ _ _ _ _ F _ _ _ A) as Prefix.
 pose proof (MappedFetch.run_append _ _ _ _ _ Prefix _ _ _ Next) as All.
 exists (State (Running (word(ip+delta)-ip)) child cf),((head++[])++[w]);split;[exact All|].
 split.
 - rewrite app_nil_r;apply Forall_app;split.
   + eapply Forall_impl;[|exact W];intros v V x X;specialize (V x X);unfold Prologue.stack_region,Rows.frame,sp,span in *;lia.
   + constructor;[|constructor]. intros x X;change (word(regs args 4%nat-8)<=x<word(regs args 4%nat-8)+8) in X.
     rewrite SP',Slot in X;unfold Prologue.stack_region,Rows.frame,sp,span in *;lia.
 - split.
   2:{ split.
     - intros j f k J H K;change (store_word (mem args) (word(regs args 4%nat-8)) ret (bank (Rows.frame e) f+8*Z.of_nat j+k)=word_byte (value s j f) k);
     rewrite SP',Slot;unfold store_word;rewrite write_outside by (unfold bank;lia);
     exact (transferred _ _ _ _ _ _ _ _ Code Frame SP Prefix j f k J H K).
     - split.
       + change (regs args 2%nat=read_word (mem s) (Rows.frame e+936));rewrite Table.
         pose proof(steps_memory _ _ _ _ _ (MappedFetch.run_steps _ _ _ _ _ _ F)) as M;cbn [cpu_state] in M;rewrite M.
         apply preserved_read with (outside:=fun x=>~(Rows.frame e+0<=x<Rows.frame e+928));
           [exact (WriteTrace.frame _ _ W _)|intros k K;change (0<=k<8) in K;lia].
       + change (regs args 15%nat=Return.scratch e).
         exact (eq_trans (kept_sequence ip text 15 setup (offset PrepareArgs) mid cf _ _ ltac:(change (0<=353);lia) Args eq_refl A) (eq_trans Keep Scratch)). }
   unfold entered_with. cbn [loc cpu_state]. split;[reflexivity|].
   assert (ChildSP:regs child 4%nat=Rows.frame e-8) by (change (word(regs args 4%nat-8)=Rows.frame e-8);rewrite SP';exact Slot).
   split;[exact ChildSP|]. split;[|exact (conj RSI (conj RCX (conj (eq_trans RDI (eq_trans Keep Scratch)) (conj (conj (eq_trans (Live 13%nat (or_intror (or_introl eq_refl))) Count) (eq_trans (Live 14%nat (or_intror (or_intror eq_refl))) Out)) (eq_trans (Live 12%nat (or_introl eq_refl)) Left)))) )].
   apply read_word_encoded;intros k K. change (store_word (mem args) (word(regs args 4%nat-8)) ret
      (Rows.frame e-8+k)=word_byte ret k). rewrite SP',Slot;unfold store_word;apply write_at,K.
Qed.

Theorem instructions ip text delta e s c : bound text delta -> placement e ->
 regs s 4%nat=Rows.frame e -> Prologue.context_registers e s -> regs s 12%nat=Prologue.rows_left (regs e 6%nat) -> Prologue.segment ip text e 42 (offset Stage) s c (fun child=>entered ip delta e child /\
 matrix (Rows.frame e) s (mem (cpu_state child)) /\ regs(cpu_state child) 2%nat=read_word (mem s) (Rows.frame e+936) /\
 regs(cpu_state child) 15%nat=Return.scratch e).
Proof. apply instructions_with. Qed.
