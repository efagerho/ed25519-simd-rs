From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords
 execution.WordBounds execution.WordSemantics execution.AlignedRows execution.QwordBlock execution.MappedFetch
 execution.InstructionRoute memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictSeeded ScorePoint.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).
Definition off (y:bool):=if y then 320 else 0.
Definition start (y:bool):=if y then 236 else 398.
Definition z_at (y:bool):=if y then 271 else 432.
Definition sub_at (y:bool):=if y then 306 else 467.
Definition seeds y:=map (fun i=>WithMemory true (10+i) (if Nat.eqb i 0 then 30 else 31) 7 (off y+64*Z.of_nat i)) (seq 0 5).
Lemma image y:linked text (AlignedRows.route false (start y) 0 3 (off y) 5) /\
 linked text (AlignedRows.route false (z_at y) 5 7 640 5) /\ linked text (QwordBlock.route (sub_at y) (seeds y)).
Proof. destruct y;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition limb s base off j i:=read_word (mem s) (base+off+64*Z.of_nat i+8*Z.of_nat j).
Definition inputs y e s t:=forall j i,(j<8)%nat -> (i<5)%nat ->
 vectors t j i=limb s (BatchDecode.point e true) (off y) j i /\
 vectors t j (5+i)%nat=limb s (ScoreFrame.buffer e) 640 j i /\
 vectors t j (10+i)%nat=Arithmetic.vpsubq (vectors s j (if Nat.eqb i 0 then 30 else 31)%nat)
    (limb s (ScoreFrame.buffer e) (off y) j i).
Definition execute bias:=segment (bias+pc) text 15.

Lemma rows y o e s c:placement e -> regs s 3%nat=BatchDecode.point e true -> regs s 7%nat=ScoreFrame.buffer e ->
 exists v,run 10 (ScalarBytes.fetch o text) (State(Running(start y)) s c)=Some(State(Running(sub_at y)) v c,[]) /\
 regs v=regs s /\ mem v=mem s /\
 (forall j i,(i<5)%nat -> vectors v j i=limb s (BatchDecode.point e true) (off y) j i /\
     vectors v j (5+i)%nat=limb s (ScoreFrame.buffer e) 640 j i) /\
 forall j i,(10<=i)%nat -> vectors v j i=vectors s j i.
Proof.
 intros P R Q;destruct(image y) as [A [B _]];set(a:=BatchDecode.point e true);set(b:=ScoreFrame.buffer e).
 destruct(stack_ok _ P) as [[L H] _];destruct(scratch_ok _ P) as [[D DH] DA].
 pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)) as Pad.
 assert (Bound:0<=b /\ b+1280<2^64) by (unfold b,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia).
 assert (Align:b mod 64=0).
 { unfold b,ScoreFrame.buffer,FramePointer.bottom;set(t:=ScoreFrame.top e-48).
   replace (t-t mod 64-1280) with ((t/64-20)*64) by (pose proof(Z.div_mod t 64 ltac:(lia));lia);apply Z.mod_mul;lia. }
 assert (RAlign:(a+off y) mod 64=0).
 { unfold a;rewrite Z.add_mod,(BatchDecode.point_aligned _ true DA) by lia;destruct y;reflexivity. }
 destruct(AlignedRows.loads o text 5 (start y) 0 3 (off y) (a+off y) s c A ltac:(now rewrite R) RAlign
    ltac:(unfold fits64,a,BatchDecode.point,BatchDecode.point_offset,off;destruct y;lia)) as [u [RA [G [M [_ [Rows Other]]]]]].
 destruct(AlignedRows.loads o text 5 (z_at y) 5 7 640 (b+640) u c B ltac:(now rewrite G,Q)
   ltac:(replace 640 with (10*64) by ring;now rewrite Z.mod_add by lia) ltac:(unfold fits64;lia)) as [v [RB [G' [M' [_ [Zs Keep]]]]]].
 replace (AlignedRows.after false (start y) 0 3 (off y) 5) with (z_at y) in RA by (destruct y;reflexivity).
 replace (AlignedRows.after false (z_at y) 5 7 640 5) with (sub_at y) in RB by (destruct y;reflexivity).
 exists v;split;[exact (run_append _ _ _ _ _ RA _ _ _ RB)|split;[now rewrite G'|split;[now rewrite M'|split]]].
 - intros j i I;split;[rewrite Keep by lia;exact (Rows j i I)|rewrite Zs,M by exact I;reflexivity].
 - intros j i I;rewrite Keep,Other by lia;reflexivity.
Qed.

Lemma subtraction y v : forall j i,(i<5)%nat ->
 let next:=lane (vector_load v j) (vectors v j) (seeds y) in
 next (10+i)%nat=Arithmetic.vpsubq (vectors v j (if Nat.eqb i 0 then 30 else 31)%nat)
   (vector_load v j 7%nat (off y+64*Z.of_nat i)).
Proof. intros j [|[|[|[|[|i]]]]] I;try lia;reflexivity. Qed.
Lemma kept y v j i : (i<10 \/ 15<=i)%nat -> lane (vector_load v j) (vectors v j) (seeds y) i=vectors v j i.
Proof.
 intro K;unfold seeds;cbn [map seq lane lane_step];unfold put;repeat match goal with |-context[Nat.eqb ?d i] =>
   destruct(Nat.eqb_spec d i);[lia|] end;reflexivity.
Qed.

Theorem checked y bias e p:placement e -> loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+pc+start y -> regs(machine p) 3%nat=BatchDecode.point e true -> regs(machine p) 7%nat=ScoreFrame.buffer e ->
 accounted e (writable e) p -> well_formed(machine p) ->
 exists q,execute bias p=Some q /\ ip q=bias+pc+StrictSeeded.start y /\ accounted e (writable e) q /\ well_formed(machine q) /\
 regs(machine q)=regs(machine p) /\ mem(machine q)=mem(machine p) /\ inputs y e (machine p) (machine q) /\
 forall j i,(15<=i)%nat -> vectors(machine q) j i=vectors(machine p) j i.
Proof.
 intros P I PC R Q Paid W;set(o:=bias+pc);set(s:=machine p).
 destruct(rows y o e s (carry p) P R Q) as [v [Read [G [M [Row High]]]]].
 destruct(QwordBlock.execute o _ _ _ v (carry p) (proj2(proj2(image y)))) as [u [Sub [G' [M' [_ Vec]]]]].
 replace (QwordBlock.after (sub_at y) (seeds y)) with (StrictSeeded.start y) in Sub by (destruct y;reflexivity).
 pose proof(run_append _ _ _ _ _ Read _ _ _ Sub) as Run.
 destruct(mapped_now _ _ _ I _ _ _ Paid (ScoreSetup.image Dalek)) as [Map Sep].
 destruct(at_segment _ _ p o text 15 _ _ _ Paid PC Map Sep Run (Forall_nil _)) as [Next End].
 eexists;split;[exact Next|split;[reflexivity|split;[exact End|split;[exact (segment_wf _ _ _ _ _ W Next)|]]]].
 change (regs u=regs s /\ mem u=mem s /\ inputs y e s u /\ (forall j i,(15<=i)%nat -> vectors u j i=vectors s j i));split;[now rewrite G'|split;[now rewrite M'|split]].
 - intros j i J K;rewrite !Vec;rewrite (kept y v j i ltac:(lia)),(kept y v j (5+i)%nat ltac:(lia));destruct(Row j i K) as [X Z];split;[exact X|split;[exact Z|]].
   rewrite subtraction by exact K;rewrite High by (destruct (Nat.eqb i 0);lia).
   unfold vector_load,limb;fold s in Q;rewrite G,M,Q.
   destruct(stack_ok _ P) as [[Lo Hi] _];pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)).
   rewrite word_fits by (destruct y;unfold off,word64,ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia);replace (ScoreFrame.buffer e+(off y+64*Z.of_nat i)) with (ScoreFrame.buffer e+off y+64*Z.of_nat i) by ring;reflexivity.
 - intros j i K;rewrite Vec,kept,High by lia;reflexivity.
Qed.
