From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute execution.LinkedRun
 memory.ByteMemory memory.FlatMemory memory.WriteTrace memory.MemoryGeometry.
From Ed25519Simd.Zip215 Require ScatterBytes ScatterTrace ScatterReturn.
From Ed25519Simd.VerifyBatch Require Import Policy Image Rows Return LoadedImage Prologue BatchScalar PrepareUnwind.
From Ed25519Simd.VerifyBatch Require RejectOutputs.
Import ListNotations. Local Open Scope Z_scope.

Definition scatter := Zip215.ScatterBytes.address.
Definition path pc : list line :=
 [(385,2%nat,Test32 0);(387,6%nat,Branch ScalarBytes.Equal (541-393));
  (541,12%nat,StoreImmediate (Address 4 None 856) 0);(553,8%nat,LeaG 7 (Address 4 None 856));
  (561,3%nat,CopyG 6 14);(564,3%nat,CopyG 2 13);(567,2%nat,Zero32 0);
  (569,5%nat,CallRelative (scatter-(pc+574)))].
Definition bound pc text := linked text (path pc).
Definition pending top x := top-8<=x<top \/ top+856<=x<top+864.

Lemma dispatch bias pc text s c top : bound pc text -> regs s 0%nat mod 2^32=0 -> regs s 4%nat=top ->
 8<=top -> top+864<2^64 -> word64(bias+scatter) ->
 exists last ws,run 8 (ScalarBytes.fetch (bias+pc) text) (State (Running 385) s c)=Some(last,ws) /\
 loc last=Running (scatter-pc) /\ regs(cpu_state last) 4%nat=top-8 /\
 regs(cpu_state last) 6%nat=regs s 14%nat /\ regs(cpu_state last) 2%nat=regs s 13%nat /\
 read_word (mem(cpu_state last)) (top-8)=word(bias+pc+574) /\
 regs(cpu_state last) 12%nat=regs s 12%nat /\ confined (pending top) ws /\
 regs(cpu_state last) 7%nat=top+856 /\ regs(cpu_state last) 0%nat=0.
Proof.
 intros Bound Zero SP Lo Hi Dest;do 2 eexists;split.
 - apply (checked _ _ _ Bound);cbn [path follow loc cpu_state cf step option_map eval_condition with_zf flag];
     rewrite Zero;reflexivity.
 - cbn [path follow loc cpu_state cf step option_map eval_condition with_zf flag];rewrite ?Zero.
   cbn [loc cpu_state regs mem with_zf with_words set set_regs effective push push_words put Nat.eqb app].
   rewrite SP. repeat match goal with |-context[word ?a]=>rewrite (word_fits a ltac:(unfold word64 in *;lia)) end.
   split;[f_equal;replace (bias+pc+(569+Z.of_nat 5+(scatter-(pc+574)))) with (bias+scatter) by ring;
       rewrite ?(word_fits _ Dest);ring|].
   split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|]. split.
   + apply read_word_encoded;intros k K;unfold store_word;rewrite write_at by lia;reflexivity.
   + split;[reflexivity|]. split;[|split;[f_equal;ring|reflexivity]]. apply Forall_cons;[|apply Forall_cons;[|apply Forall_nil]].
     * intros x X;right;change (top+0+856<=x<top+0+856+8) in X;lia.
     * intros x X;left;change (top-8<=x<top-8+8) in X;lia.
Qed.

Module S := Zip215.ScatterTrace.

Local Lemma keeps_counter o l s c t ws :
 ScalarBytes.fetch o S.code (State (Running (S.offset l)) s c)=Some(t,ws) ->
 regs(cpu_state t) 12%nat=regs s 12%nat.
Proof.
 rewrite S.fetched;destruct l;
 match goal with |-context[S.fetch_at ?lab]=>let op:=eval vm_compute in (S.fetch_at lab) in
   change (S.fetch_at lab) with op end;cbn [step];intro Run.
 all: try match type of Run with context[option_map _ ?flag]=>destruct flag as [[]|];try discriminate end.
 all: injection Run as <- <-;reflexivity.
Qed.

Local Lemma counter_after o a n s ws t : ScalarBytes.steps o S.code s ws t ->
 word64 n -> fits64 a n -> S.invariant a n s -> regs(cpu_state t) 12%nat=regs(cpu_state s) 12%nat.
Proof.
 induction 1 as [s|s mid last own tail F R IH];intros N Range Inv;[reflexivity|].
 destruct s as [[off|back] s c];[|discriminate]. destruct Inv as [D [L [l [PC Guard]]]].
 cbn [loc] in PC;subst off.
 destruct(S.live_step o a n l s c N Range D L Guard) as [u [log [Step [_ Next]]]].
 rewrite F in Step;injection Step as <- <-. rewrite (IH N Range Next);exact (keeps_counter _ _ _ _ _ _ F).
Qed.

Definition scatter_stores bias pc text p :=
 bind (LinkedRun.segment (bias+pc) text 8 p)
      (returning (bias+scatter) (length Zip215.ScatterBytes.symbol_bytes) 88).
Definition continued bias pc e q := ip q=bias+pc+offset Continue /\
 regs(machine q) 4%nat=Rows.frame e /\ accounted e (writable e) q /\ regs(machine q) 12%nat=Prologue.rows_left (regs e 6%nat).

Theorem resume pol bias pc text e p :
 bound pc text -> placement e -> loaded pol bias (mem e) (writable e) ->
 fits64 (bias+pc) (Z.of_nat(length text)) -> offset Continue<Z.of_nat(length text) ->
 mapped (mem e) (bias+pc) text ->
 (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text)->~writable e x) ->
 accounted e (writable e) p -> ip p=word(bias+pc+offset Prepared) ->
 regs(machine p) 4%nat=Rows.frame e -> Prologue.output_registers e (machine p) ->
 regs(machine p) 12%nat=Prologue.rows_left (regs e 6%nat) -> regs(machine p) 0%nat mod 2^32=0 ->
 (0<Scatter.count e)%nat -> Scatter.indices e -> StageEntry.metadata e (mem(machine p)) ->
 exists q,scatter_stores bias pc text p=Some q /\ continued bias pc e q /\ RejectOutputs.outputs e (machine q).
Proof.
 intros Code Place Image Range Length Bytes Apart Prev IP SP [Count Out] Left Zero Live Indices Meta.
 change 574 with (offset Continue) in *.
 assert (R:word64(bias+pc+574) /\ word64(bias+pc+385)) by
   (change (574<Z.of_nat(length text)) in Length;unfold fits64,word64 in *;lia).
 destruct (stack_ok _ Place) as [[Lo Hi] _].
 destruct (dispatch bias pc text (machine p) (carry p) (Rows.frame e) Code Zero SP
  ltac:(unfold Rows.frame,sp in *;lia) ltac:(unfold Rows.frame,sp in *;lia)
  (mapped_word _ _ _ Image _ _ (LoadedImage.scatter _) ltac:(vm_compute;reflexivity)))
   as [s [w [Step [Target [Stack [D [N [Back [CarryLeft [Safe [MetaPtr Cleared]]]]]]]]]]].
 assert (W:confined (writable e) w) by (eapply Forall_impl;[|exact Safe];intros z K x X;left;
     specialize(K x X);unfold pending,Rows.frame,sp,span in *;lia).
 change (ip p=word(bias+pc+385)) in IP;rewrite (word_fits _ (proj2 R)) in IP.
 destruct (at_segment _ _ _ _ _ _ 385 _ _ Prev IP (image_after _ _ _ _ _ Prev Bytes Apart) Apart Step W) as [Dispatch Paid].
 set (s0:=LinkedRun.finish (bias+pc) p (s,w)) in *.
 assert (At:ip s0=bias+scatter) by (unfold s0;cbn [LinkedRun.finish ip];unfold absolute;rewrite Target;ring).
 destruct(mapped_now _ _ _ Image _ _ _ Paid (LoadedImage.scatter _)) as [Map Separate].
 set (len:=Z.of_nat(Scatter.count e)).
 assert (Len:regs e 6%nat=len).
 { unfold len,Scatter.count;rewrite Z2Nat.id by (pose proof (proj1(initial_cpu _ Place) 6%nat);unfold word64 in *;lia);
   reflexivity. }
 assert (L:word64 len) by (rewrite <-Len;apply (initial_cpu _ Place)).
 assert (Const:forall x,bias+scatter<=x<bias+scatter+Z.of_nat(length Zip215.ScatterBytes.symbol_bytes)->
     ~Zip215.ScatterTrace.output (output e) len x).
 { intros x X H;apply (Separate x X);right;right;exact H. }
 assert (RegD:regs(machine s0) 6%nat=output e) by exact (eq_trans D Out).
 assert (RegN:regs(machine s0) 2%nat=len) by exact (eq_trans N (eq_trans Count Len)).
 destruct (Zip215.ScatterReturn.mapped_termination _ _ (carry s0) _ _ eq_refl L (out_ok _ Place) RegD RegN Map Const)
    as [k [t [ws [back [Bound [Steps [Run Ret]]]]]]].
 assert (Top:word64(Rows.frame e-8)) by (unfold Rows.frame,sp,word64 in *;lia).
 assert (Protected:forall j,0<=j<8 -> ~Zip215.ScatterTrace.output (output e) len (Rows.frame e-8+j))
    by (intros j J H;destruct(out_stack _ Place);unfold Zip215.ScatterTrace.output,len,Rows.frame,sp in *;lia).
 destruct (Zip215.ScatterReturn.mapped_prefix _ _ _ _ _ _ _ _ _ eq_refl L (out_ok _ Place)
   Top RegD RegN Stack Back Protected Map Const Run) as [Return [Child [M _]]].
 unfold Zip215.ScatterReturn.stack_position in Return;rewrite Ret in Return.
 destruct Return as [Dest NextSP].
 assert (Keep:regs(cpu_state t) 12%nat=regs(machine s0) 12%nat).
 { assert (All:forall xs u,ScalarBytes.steps (bias+scatter) S.code (State (Running 0) (machine s0) (carry s0)) xs u ->
          confined (S.output (output e) len) xs).
   { intros xs u Trace. pose proof(S.scatter_confined (bias+scatter) (machine s0) (carry s0) xs u) as H.
     unfold S.destination,S.length64 in H;rewrite RegD,RegN in H;exact (proj1 (H L (out_ok _ Place) Trace)). }
   apply (MappedFetch.same_prefixes (bias+scatter) S.code (State (Running 0) (machine s0) (carry s0)) _ Map Const All) in Run.
   apply (counter_after (bias+scatter) (output e) len (State (Running 0) (machine s0) (carry s0)) ws t Run L (out_ok _ Place)).
   split;[exact RegD|split;[exact RegN|exists S.Count;split;[reflexivity|exact I]]]. }
 set (q:=LinkedRun.finish (bias+scatter) s0 (t,ws)).
 assert (Returned:returning (bias+scatter) (length Zip215.ScatterBytes.symbol_bytes) 88 s0=Some q).
 { unfold returning;pose proof (until_exact _ _ _ _ _ _ _ _ Bound Steps Ret) as ToRet;
   fold scatter in ToRet;rewrite At,Z.sub_diag,ToRet;reflexivity. }
 exists q;split.
 - unfold scatter_stores;rewrite Dispatch;exact Returned.
 - split.
   2:{ apply (RejectOutputs.published (bias+scatter) e s0 q Place Live Indices At MetaPtr RegD RegN Cleared).
       - eapply IndexStores.metadata_preserved;[|exact Meta].
         intros x X;change (mem (cpu_state s) x=mem(machine p) x).
         rewrite (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Step));apply (WriteTrace.frame _ _ Safe);
           unfold pending;lia.
       - exact Map.
       - exact Const.
       - exact Returned. }
   unfold q,continued;cbn [LinkedRun.finish ip machine];unfold absolute;rewrite Ret.
   split;[rewrite Dest,ScalarRefinement.word_idempotent,(word_fits _ (proj1 R));reflexivity|].
   split;[rewrite NextSP;replace (Rows.frame e-8+8) with (Rows.frame e) by ring;
       apply word_fits;unfold Rows.frame,sp,word64 in *;lia|].
   split;[|exact (eq_trans Keep (eq_trans CarryLeft Left))]. apply append_accounted;[exact Paid| |intro x;rewrite M;reflexivity].
   eapply Forall_impl;[|exact Child];intros v K x X;right;right;exact (K x X).
Qed.
