From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute execution.AlignedRows
 memory.ByteMemory memory.WriteTrace memory.MemoryGeometry.
From Curve25519 Require Import Radix51.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode.
From Ed25519Simd.VerifyBatch Require DecoderFrame.
Local Open Scope Z_scope.

Definition other_scratch signature e x :=
 span (scratch e) 25344 x /\ ~span (point e signature) 1280 x.
Definition address signature e := point e signature+320.
Definition preserve bias := segment (bias+DecoderFrame.origin) DecoderFrame.code 5.
Definition digits signature e s j i := read_word (mem s) (address signature e+64*Z.of_nat i+8*Z.of_nat j).
Definition saved signature bias e p := ip p=bias+DecoderFrame.origin+497 /\ accounted e (writable e) p /\
 0<=regs(machine p) 0%nat<256 /\ forall j,(j<8)%nat ->
 split_field (digits signature e (machine p) j) /\ limbs (digits signature e (machine p) j)=original_encoding signature e j mod 2^255 /\
 Z.testbit (regs(machine p) 0%nat) (Z.of_nat j)=Z.testbit (original_encoding signature e j) 255.
Lemma bytes : linked DecoderFrame.code (AlignedRows.route true 462 0 7 320 5).
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Theorem from_limbs signature pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 regs(machine p) 7%nat=point e signature -> unpacked signature bias e p ->
 exists q,preserve bias p=Some q /\ saved signature bias e q /\ regs(machine q)=regs(machine p) /\
 vectors(machine q)=vectors(machine p) /\
 (forall j i,(j<8)%nat -> (i<5)%nat -> digits signature e (machine q) j i=vectors(machine p) j i) /\
 forall x,~range (address signature e) 5 x -> mem(machine q) x=mem(machine p) x.
Proof.
 intros Place Image DI [PC [Acc [Mask Data]]];set (o:=bias+DecoderFrame.origin) in *.
 destruct(scratch_ok _ Place) as [[Lo Hi] Al].
 destruct(mapped_now _ _ _ Image _ _ _ Acc (decode_in pol)) as [Map Apart].
 assert (Base:regs(machine p) 7%nat+320=address signature e) by (unfold address;lia).
 assert (Aligned:address signature e mod 64=0) by (unfold address;replace 320 with (5*64) by reflexivity;rewrite Z.mod_add by lia;apply point_aligned,Al).
 destruct (stores o _ 5 462 0 7 320 (address signature e) (machine p) (carry p) bytes Base Aligned
    ltac:(unfold fits64,address,point,point_offset;destruct signature;lia)
    ltac:(intros i j I J;pose proof (proj1(Data j J) i I) as B;change (0<=vectors(machine p) j i<=2^52-1) in B;change (0<=vectors(machine p) j i<2^64);lia))
    as [s [ws [Run [Regs [Vec [_ [Safe Rows]]]]]]].
 assert (W:confined (writable e) ws).
 { apply Forall_impl with (P:=permits (range (address signature e) 5));[|exact Safe].
   intros w R x X;specialize(R x X);right;left;unfold span,range,address,point,point_offset in *;destruct signature;lia. }
 destruct (at_segment _ _ _ o DecoderFrame.code _ 462 _ _ Acc PC Map Apart Run W) as [Next Paid].
 eexists;split;[exact Next|split].
 - split;[reflexivity|split;[exact Paid|]]. cbn [LinkedRun.finish machine cpu_state].
   rewrite Regs;split;[exact Mask|]. intros j J;destruct(Data j J) as [Bound [Y Sign]].
   assert (D:forall i,(i<5)%nat -> digits signature e s j i=vectors(machine p) j i) by (intros i I;apply Rows;assumption).
   split;[intros i I;rewrite D by exact I;apply Bound,I|split;[rewrite <-Y;apply limbs_ext,D|exact Sign]].
 - split;[exact Regs|split;[exact Vec|split;[intros j i J I;apply Rows;assumption|]]].
   pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)) as Replay.
   change (mem s=WriteTrace.replay (mem(machine p)) ws) in Replay.
   intros x X;change (mem s x=mem(machine p) x);rewrite Replay;apply (WriteTrace.frame _ _ Safe),X.
Qed.

Definition save_input bias s incoming :=
 bind (transpose bias s) (fun words=>bind (unpack bias words incoming)
   (fun '(y,k)=>option_map (fun p=>(p,k)) (preserve bias y))).
Definition frame signature pol bias e s := let sp:=common_top pol e-112 in
 regs s 7%nat=point e signature /\ regs s 4%nat=DecoderFrame.top sp-8 /\
 read_word (mem s) (DecoderFrame.top sp-8)=word(bias+DecoderFrame.origin+resume_offset signature) /\
 (forall i j,(i<4)%nat -> vectors s j (28+i)%nat=DecoderFrame.constant i) /\ setup_caller signature pol bias e s.

Theorem from_setup signature pol bias e p incoming : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> setup signature pol bias e p ->
 exists q updated,save_input bias p incoming=Some(q,updated) /\ saved signature bias e q /\
 frame signature pol bias e (machine q) /\
 (forall j i,(j<8)%nat -> (i<5)%nat -> digits signature e (machine q) j i=vectors(machine q) j i) /\
 preserved (other_scratch signature e) (mem(machine p)) (mem(machine q)).
Proof.
 intros P M Al Setup.
 destruct(BatchDecode.from_setup signature _ _ _ _ P M Al Setup) as [v [Next [Words [_ [WordsMem G]]]]].
 destruct(BatchDecode.from_words signature _ _ _ _ incoming P M Words) as [y [k [Unpack [Value [_ [UnpackMem [Other Constants]]]]]]].
 pose proof(environment _ _ _ _ _ Setup) as Caller.
 destruct Setup as [_ [_ [SP [_ [_ [DI [_ [_ [Link _]]]]]]]]].
 assert (Dest:regs(machine y) 7%nat=point e signature) by (rewrite Other,G by discriminate;exact DI).
 destruct(from_limbs signature _ _ _ _ P M Dest Value) as [q [Save [Saved [Regs [Vec [Data Keep]]]]]].
 exists q,k;split;[unfold save_input;rewrite Next;cbn [bind];rewrite Unpack;cbn [bind];now rewrite Save|].
 split;[exact Saved|split].
 - unfold frame;rewrite Regs;split;[exact Dest|split;[rewrite Other,G by discriminate;exact SP|split]].
   + rewrite <-Link,<-WordsMem,<-UnpackMem;apply preserved_read with (outside:=fun x=>~range (address signature e) 5 x).
     * exact Keep.
     * intros off K;change (0<=off<8) in K;pose proof(Z.mod_pos_bound (common_top pol e-112-40) 64 ltac:(lia)).
     destruct(scratch_stack _ P);unfold range,address,point,point_offset,DecoderFrame.top,FlatMemory.disjoint,common_top,Rows.frame,sp in *;destruct pol,signature;lia.
   + split;[intros i j I;rewrite Vec;apply Constants,I|].
     apply (keep_caller _ _ _ _ _ _ Caller).
     * intros r R;rewrite Regs,Other,G;[reflexivity|intros ->;unfold caller_reg in R;cbn in R;lia].
     * intros x X;rewrite Keep,UnpackMem,WordsMem;[reflexivity|].
       unfold caller_bytes in X;pose proof(Z.mod_pos_bound (common_top pol e-112-40) 64 ltac:(lia)).
       destruct(scratch_stack _ P);unfold range,address,point,point_offset,FlatMemory.disjoint,common_top,Rows.frame,sp in *;destruct pol,signature;lia.
 - split;[intros j i J I;rewrite Vec;exact (Data j i J I)|].
   intros x [_ X];rewrite Keep,UnpackMem,WordsMem;[reflexivity|].
   unfold range,address,span in *;change (Z.of_nat 5) with 5;lia.
Qed.
