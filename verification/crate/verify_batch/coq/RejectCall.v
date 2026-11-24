From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.StoreInstructions abi.CallFrame abi.TracedCalls memory.FlatMemory
 memory.ByteMemory memory.WriteTrace memory.MemoryGeometry.
From Machine Require execution.MappedFetch.
From Ed25519Simd.Zip215 Require Import ScatterReturn.
From Ed25519Simd.Zip215 Require ScatterBytes.
From Ed25519Simd.VerifyBatch Require Import Image Rows Scatter Return LoadedImage CallWrites.
Local Open Scope Z_scope.

Definition op := Invoke Zip215.ScatterBytes.address.
Definition site pc := pc+offset CallScatter.
Definition bound pc text := firstn 5 (skipn (Z.to_nat (offset CallScatter)) text)=encoding (site pc) op /\
 encodable (site pc) op=true /\ 0<=offset CallScatter /\ offset Continue<Z.of_nat(length text) /\
 offset Continue=offset CallScatter+5.
Definition contract bias pc (text:list Z) e := forall prior s carry,
 confined (writable e) prior -> mem s=WriteTrace.replay (mem e) prior ->
 regs s 4%nat=Rows.frame e -> regs s 6%nat=output e -> regs s 2%nat=Z.of_nat (count e) ->
 let '(dest,child):=caller_step bias (site pc) op s in
 let own:=caller_stores bias (site pc) op s in
 let start:=State (Running 0) child carry in
 (exists k t ws,(k<=88)%nat /\
    MappedFetch.run k (MappedFetch.fetch dest (length Zip215.ScatterBytes.symbol_bytes)) start=Some(t,ws) /\
    loc t=Returned (bias+pc+offset Continue)) /\
 forall ws last,MappedFetch.steps dest (length Zip215.ScatterBytes.symbol_bytes) (State (Running 0) child carry) ws last ->
 firstn 5 (skipn (Z.to_nat (offset CallScatter)) (MappedFetch.snapshot (mem s) (bias+pc) (length text)))=
   encoding (site pc) op /\ dest=bias+Zip215.ScatterBytes.address /\
 confined (nested_writable e) (own++ws) /\
 mem (cpu_state last)=WriteTrace.replay (mem e) (prior++own++ws) /\
 stack_position (Rows.frame e-8) (bias+pc+offset Continue) last /\
 match loc last with Returned _=>True | Running _=>
 exists next writes,MappedFetch.fetch dest (length Zip215.ScatterBytes.symbol_bytes) last=Some(next,writes) end.

Theorem checked mode bias pc text e : bound pc text -> placement e ->
 fits64 (bias+pc) (Z.of_nat(length text)) -> MappedFetch.mapped (mem e) (bias+pc) text ->
 (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text) -> ~writable e x) ->
 LoadedImage.loaded mode bias (mem e) (writable e) -> contract bias pc text e.
Proof.
 intros [Bytes [Fit [Pos [Len End]]]] Place Range Wrapper Apart Loaded prior s c Past Memory SP D L.
 set (ret:=bias+pc+offset Continue).
 assert (Ret:word64 ret) by (unfold ret,word64,fits64 in *;lia).
 assert (IP:bias+next_pc (site pc) op=ret).
 { change (bias+(pc+offset CallScatter+5)=ret);unfold ret;rewrite End;ring. }
 pose proof(LoadedImage.scatter mode) as InCode.
 destruct(LoadedImage.symbols _ _ _ _ Loaded _ _ InCode) as [Fits _].
 assert (Dest:word (bias+Zip215.ScatterBytes.address)=bias+Zip215.ScatterBytes.address).
 { apply word_fits;unfold fits64,word64 in *.
   change (Z.of_nat(length Zip215.ScatterBytes.symbol_bytes)) with 58 in Fits;lia. }
 assert (Dispatch:caller_step bias (site pc) op s=(bias+Zip215.ScatterBytes.address,push s ret)).
 { change ((word (bias+call_destination (site pc) Zip215.ScatterBytes.address),
     push s (bias+next_pc (site pc) op))=(bias+Zip215.ScatterBytes.address,push s ret)).
   rewrite (call_destination_correct _ _ Fit),IP,Dest;reflexivity. }
 rewrite Dispatch;cbv zeta.
 pose proof(caller_store_memory bias (site pc) op s) as Store;rewrite Dispatch in Store;cbn [snd] in Store.
 set (own:=caller_stores bias (site pc) op s) in *.
 assert (Word:word (Rows.frame e-8)=Rows.frame e-8).
 { apply word_fits;destruct(stack_ok _ Place) as [[Lo Hi] _];unfold Rows.frame,sp,word64 in *;lia. }
 assert (Top:regs (push s ret) 4%nat=Rows.frame e-8) by
   (change (word (regs s 4%nat-8)=Rows.frame e-8);now rewrite SP).
 assert (Saved:read_word (mem (push s ret)) (Rows.frame e-8)=ret)
   by (rewrite <-Top;apply pushed_return_word,Ret).
 assert (Own:confined (nested_writable e) own).
 { apply Forall_cons;[|constructor]. intros x X;left.
   change (word(regs s 4%nat-8)<=x<word(regs s 4%nat-8)+8) in X.
   rewrite SP,Word in X;unfold span,Rows.frame,sp in *;lia. }
 assert (Earlier:confined (writable e) (prior++own)) by
   (apply Forall_app;split;[exact Past|eapply lend;[apply nested_in_root|exact Own]]).
 pose proof(LoadedImage.after _ _ _ _ _ Loaded Earlier) as LoadedNow.
 rewrite WriteTrace.replay_app,<-Memory,<-Store in LoadedNow.
 destruct(LoadedImage.symbols _ _ _ _ LoadedNow _ _ InCode) as [_ Map].
 assert (Const:forall x, bias+Zip215.ScatterBytes.address<=x<bias+Zip215.ScatterBytes.address+
   Z.of_nat(length Zip215.ScatterBytes.symbol_bytes) -> ~S.output (output e) (Z.of_nat(count e)) x).
 { intros x At Inside;apply (LoadedImage.immutable _ _ _ _ LoadedNow x);
   [left;eexists _,_;split;[exact InCode|exact At]|right;right;exact Inside]. }
 assert (Count:word64 (Z.of_nat(count e))) by (rewrite <-L;unfold count in L|-*;
   pose proof (proj1(initial_cpu _ Place) 6%nat) as Bound;unfold word64 in *;lia).
 assert (Protected:forall k,0<=k<8 -> ~S.output (output e) (Z.of_nat(count e)) (Rows.frame e-8+k)).
 { intros k K X;destruct(out_stack _ Place);unfold S.output,Rows.frame,sp in *;lia. }
 assert (TopWord:word64 (Rows.frame e-8)).
 { destruct(stack_ok _ Place) as [[Lo Hi] _];unfold Rows.frame,sp,word64 in *;lia. }
 pose proof (fun ws last=>mapped_prefix (bias+Zip215.ScatterBytes.address) (push s ret) c ws last (output e) (Z.of_nat(count e)) (Rows.frame e-8) ret
     eq_refl Count (out_ok _ Place) TopWord D L Top Saved Protected Map Const) as Prefix.
 split.
 { destruct (mapped_termination (bias+Zip215.ScatterBytes.address) (push s ret) c
     (output e) (Z.of_nat(count e)) eq_refl Count (out_ok _ Place) D L Map Const)
     as [k [t [ws [back [K [Steps [Native Ended]]]]]]].
   destruct (Prefix ws t Native) as [Back _];unfold stack_position in Back;rewrite Ended in Back.
   destruct Back as [E _];rewrite (word_fits _ Ret) in E;exists k,t,ws;split;[exact K|split;[exact Steps|now rewrite Ended,E]]. }
 intros ws last Run;destruct (Prefix ws last Run) as [Back [Safe [Replay Live]]].
 split.
 - rewrite Memory,(MappedFetch.snapshot_mapped _ _ _ (MappedFetch.keep_image _ _ _ _ _ Wrapper Apart Past));exact Bytes.
 - split;[reflexivity|split].
   + apply Forall_app;split;[exact Own|eapply lend;[|exact Safe];intros x X;right;right;exact X].
   + split;[rewrite !WriteTrace.replay_app,<-Memory,<-Store;exact Replay|split;assumption].
Qed.
