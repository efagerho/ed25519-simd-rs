From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.MappedFetch execution.FrameInstructions memory.MemoryGeometry
 memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require isa.VectorMoves isa.IndexedLoad isa.Move.
From Ed25519Simd.VerifyBatch Require Import Image Rows Return EntryWrites Prologue Routing.
Import ListNotations. Local Open Scope Z_scope.

Definition inputs : list line := map (fun i=>(length (IndexedLoad.encode i),
  VectorMove (VectorMoves.Input i))) transpose.
Definition publish : list line := map (fun f=>
 let d:=512+64*Z.of_nat f in
 (length (Move.encode_store f 4 d),VectorMove (VectorMoves.Output f 4 d))) (seq 0 4).
Definition indices : list line := flat_map (fun j=>
 let src:=40*Z.of_nat j+32 in
 [(if src<?128 then 4%nat else 7%nat,Load64 0 (Address 3 None src));
  (8%nat,Store64 0 (Address 4 None (864+8*Z.of_nat j)))]) (seq 0 8).
Definition setup : list line := [(3%nat,CopyG 7 15);(8%nat,LeaG 6 (Address 4 None 512));
 (8%nat,Load64 2 (Address 4 None 936));(8%nat,LeaG 1 (Address 4 None 768))].
Definition body := inputs++publish++indices++[(7%nat,Add64 3 320)]++setup.
Definition delta_call delta := delta-offset Prepared.
Definition bound text delta :=
 decoded text (offset Stage) body /\ Prologue.at_offset text (offset CallPrepare) 5 (CallRelative (delta_call delta)).
Definition entered ip delta e t :=
 loc t=Running (word(ip+delta)-ip) /\ regs (cpu_state t) 4%nat=Rows.frame e-8 /\
 read_word (mem (cpu_state t)) (Rows.frame e-8)=word(ip+offset Prepared) /\
 regs (cpu_state t) 6%nat=Rows.frame e+512 /\ regs (cpu_state t) 1%nat=Rows.frame e+768.

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

Theorem instructions ip text delta e s c : bound text delta -> placement e ->
 regs s 4%nat=Rows.frame e -> Prologue.segment ip text e 42 (offset Stage) s c (entered ip delta e).
Proof.
 intros [Bytes Call] P SP.
 change (decoded text (offset Stage) (body_prefix++setup)) in Bytes.
 destruct (prefix_decoded _ _ _ _ Bytes) as [Front Args].
 assert (Frame:fits64 (Rows.frame e) 960) by
   (destruct (stack_ok _ P) as [[Lo Hi] _];unfold fits64,Rows.frame,sp in *;lia).
 destruct (sequence ip text 0 960 (Rows.frame e) body_prefix ltac:(lia) Frame ltac:(reflexivity)
   (offset Stage) s c ltac:(change (0<=82);lia) Front SP) as [mid [cf [head [F [R W]]]]].
 change (offset Stage+FrameInstructions.width body_prefix) with (offset PrepareArgs) in F,Args.
 destruct (setup_args ip text (offset PrepareArgs) mid cf e Args ltac:(change (0<=353);lia) P R) as [args [A [SP' [RSI [RCX _]]]]].
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
   + eapply Forall_impl;[|exact W];intros v V x X;left;specialize (V x X);unfold Rows.frame,sp,span in *;lia.
   + constructor;[|constructor]. intros x X;left;change (word(regs args 4%nat-8)<=x<word(regs args 4%nat-8)+8) in X.
     rewrite SP',Slot in X;unfold Rows.frame,sp,span in *;lia.
 - unfold entered. cbn [loc cpu_state]. split;[reflexivity|].
   assert (ChildSP:regs child 4%nat=Rows.frame e-8) by (change (word(regs args 4%nat-8)=Rows.frame e-8);rewrite SP';exact Slot).
   split;[exact ChildSP|]. split;[|exact (conj RSI RCX)].
   apply read_word_encoded;intros k K. change (store_word (mem args) (word(regs args 4%nat-8)) ret
      (Rows.frame e-8+k)=word_byte ret k). rewrite SP',Slot;unfold store_word;apply write_at,K.
Qed.
