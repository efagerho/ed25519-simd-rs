From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.MappedFetch memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.Decode Require DecoderBytes.
From Ed25519Simd.PrepareChunk Require CommonBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Rows Return LoadedImage ScalarInputs BatchScalar.
From Ed25519Simd.VerifyBatch Require PrepareCopies TailCopy.
Local Open Scope Z_scope.

Definition readable e := forall j sig,(j<8)%nat ->
 let p:=encoding_ptr e j sig in fits64 p 32 /\ forall x,p<=x<p+32 -> ~writable e x.
Definition enter bias p := segment (bias+PrepareNative.common) CommonBytes.symbol_bytes 88 p.
Definition observe pol bias pc text e c ks :=
 bind (BatchScalar.observe pol bias (bias+pc) text e c ks) (fun p=>
 if regs(machine p) 0%nat mod 2^32=?0 then None else enter bias p).
Definition entry pol bias e p :=
 ip p=bias+DecoderBytes.address /\ accounted e (writable e) p /\
 regs(machine p) 7%nat=scratch e+1024 /\ regs(machine p) 6%nat=scratch e /\ regs(machine p) 2%nat=2 /\
 regs(machine p) 4%nat=common_top pol e-112 /\
 read_word (mem(machine p)) (common_top pol e-112)=word(bias+PrepareNative.common+142) /\
 PrepareCopies.staged (mem e) (mem(machine p)) (scratch e) (encoding_ptr e) 8.

Lemma decode_in pol : In (DecoderBytes.address,DecoderBytes.symbol_bytes) (children pol).
Proof. apply in_or_app;left;do 5 right;left;reflexivity. Qed.

Theorem from_scalar pol bias pc text e c ks p :
 placement e -> loaded pol bias (mem e) (writable e) -> readable e ->
 BatchScalar.observe pol bias (bias+pc) text e c ks=Some p -> BatchScalar.post pol bias (bias+pc) e p ->
 copy_ready e (machine p) -> regs(machine p) 0%nat mod 2^32<>0 ->
 exists q,observe pol bias pc text e c ks=Some q /\ entry pol bias e q.
Proof.
 intros Place Image Inputs Prefix [PC [SP [Acc _]]] [Bytes [Ptr [BX Rows]]] Live.
 set (frame:=common_top pol e-104) in *;set (dst:=scratch e) in *.
 set (table:=Rows.frame e+512) in *.
 destruct(stack_ok _ Place) as [[Lo Hi] _];destruct(scratch_ok _ Place) as [[D U] Al].
 assert (Frame:sp e-1200<=frame<sp e-1000) by (unfold frame,common_top,Rows.frame,sp;destruct pol;lia).
 assert (T:fits64 table 128) by (unfold table,Rows.frame,sp,fits64 in *;lia).
 assert (Apart:disjoint dst 512 table 128) by
   (destruct (scratch_stack _ Place);unfold disjoint,dst,table,Rows.frame,sp in *;lia).
 assert (Aligned:dst mod 32=0).
 { unfold dst;apply Z.mod_divide in Al as [u Eq];[rewrite Eq;apply Z.mod_divide;[lia|exists (2*u);ring]|lia]. }
 assert (Ranges:forall j (sig:bool),(j<8)%nat ->
   fits64 (encoding_ptr e j sig) 32 /\ disjoint dst 512 (encoding_ptr e j sig) 32).
 { intros j sig J;destruct(Inputs j sig J) as [Fit Safe];split;[exact Fit|].
   apply ScalarInputs.apart;[lia|lia|]. intros x X Touch;apply (Safe x X);right;left;unfold span;fold dst;lia. }
 assert (Original:PrepareCopies.source_view (mem e) (mem(machine p)) (encoding_ptr e)).
 { intros j sig k J K;rewrite (proj2 Acc);apply (WriteTrace.frame _ _ (proj1 Acc)),(proj2 (Inputs j sig J));lia. }
 pose proof (BatchScalar.mapped_word _ _ _ Image _ _ (decode_in _) ltac:(vm_compute;reflexivity)) as Target.
 destruct (PrepareCopies.to_decoder bias frame dst table (mem e) (encoding_ptr e) (machine p) (carry p)
    Live SP BX Rows ltac:(unfold fits64;lia) Aligned T Apart ltac:(unfold word64;lia) Target
    ltac:(destruct (scratch_stack _ Place);unfold disjoint,dst in *;lia)
    Ranges Bytes Ptr Original) as [t [ws [R [[IP [DI [SI [DX [Top [Ret Data]]]]]] Writes]]]].
 destruct (mapped_now _ _ _ Image _ _ _ Acc (in_common _)) as [Map Sep].
 assert (Safe:confined (writable e) ws).
 { eapply Forall_impl;[|exact Writes];intros w H x X;destruct (H x X);[right;left|left];unfold span;fold dst;lia. }
 pose proof (at_segment _ _ _ _ _ _ 65 _ _ Acc PC Map Sep R Safe) as [Next A].
 eexists;split.
 - unfold observe;rewrite Prefix;cbn [bind];rewrite (proj2 (Z.eqb_neq _ _) Live);exact Next.
 - split;[|split;[exact A|]].
   + cbn [LinkedRun.finish ip];unfold absolute;rewrite IP;unfold PrepareCopies.common,PrepareCopies.decoder,PrepareNative.common;ring.
   + cbn [LinkedRun.finish machine];split;[exact DI|split;[exact SI|split;[exact DX|]]].
     replace (common_top pol e-112) with (frame-8) by (unfold frame;ring).
     exact (conj Top (conj Ret Data)).
Qed.

From Ed25519Simd.VerifyBatch Require DecoderFrame.
From Ed25519Simd.Decode Require HelperBytes.
From Machine Require execution.ScalarByteMemory.
Definition inner bias := segment (bias+DecoderFrame.origin) DecoderFrame.code 15.
(* The decoder invokes the same local subroutine on its two staged inputs. *)
Definition source_offset (signature:bool) : Z := if signature then 256 else 0.
Definition point_offset (signature:bool) : Z := if signature then 2304 else 1024.
Definition resume_offset (signature:bool) : Z := if signature then 101 else 73.
Definition source e signature := scratch e+source_offset signature.
Definition point e signature := scratch e+point_offset signature.
Lemma point_aligned e signature : scratch e mod 64=0 -> point e signature mod 64=0.
Proof. intro A;unfold point,point_offset;destruct signature;[replace 2304 with (36*64) by reflexivity|replace 1024 with (16*64) by reflexivity];now rewrite Z.mod_add by lia. Qed.
Definition original_encoding (signature:bool) e j := let input:=read_input (mem e) (regs e 7%nat) (TailCopy.row_index e j) in
 little_endian (if signature then r_bytes input else key_bytes input).
Definition key_signs e s := forall j,(j<8)%nat ->
 Z.testbit (regs s 13%nat) (Z.of_nat j)=Z.testbit (original_encoding false e j) 255.
Definition caller_bytes pol e x := scratch e<=x<scratch e+512 \/
 common_top pol e-112<=x<common_top pol e-104.
Definition caller_reg (r:nat) := In r (3::5::6::12::13::nil)%nat.
Record setup_caller signature pol bias e s : Prop := {
 caller_base : regs s 3%nat=scratch e+1024;
 caller_bp : regs s 5%nat=common_top pol e-120;
 caller_source : regs s 6%nat=source e signature;
 caller_count : regs s 12%nat=2;
 caller_return : read_word (mem s) (common_top pol e-112)=word(bias+PrepareNative.common+142);
 caller_inputs : PrepareCopies.staged (mem e) (mem s) (scratch e) (encoding_ptr e) 8;
 caller_signs : signature=true -> key_signs e s
}.
Lemma keep_caller signature pol bias e s t : setup_caller signature pol bias e s ->
 (forall r,caller_reg r -> regs t r=regs s r) ->
 preserved (caller_bytes pol e) (mem s) (mem t) -> setup_caller signature pol bias e t.
Proof.
 intros [Base BP SI Count Back Data Signs] G M;constructor.
 - rewrite G;[exact Base|cbn;tauto].
 - rewrite G;[exact BP|cbn;tauto].
 - rewrite G;[exact SI|cbn;tauto].
 - rewrite G;[exact Count|cbn;tauto].
 - rewrite <-Back;apply preserved_read with (outside:=caller_bytes pol e);[exact M|intros k K;right;lia].
 - intros j sig k J K;rewrite M;[exact (Data j sig k J K)|left;unfold PrepareCopies.dest;destruct sig;lia].
 - intros Eq j J;unfold key_signs in Signs;rewrite G;[apply Signs;assumption|cbn;tauto].
Qed.
Definition setup (signature:bool) pol bias e p := let stack:=common_top pol e-112 in let s:=machine p in
 ip p=bias+DecoderFrame.origin+244 /\ accounted e (writable e) p /\
 regs s 4%nat=DecoderFrame.top stack-8 /\ regs s 5%nat=stack-8 /\
 regs s 3%nat=scratch e+1024 /\ regs s 7%nat=point e signature /\ regs s 6%nat=source e signature /\
 regs s 12%nat=2 /\ read_word (mem s) (DecoderFrame.top stack-8)=word(bias+DecoderFrame.origin+resume_offset signature) /\
 read_word (mem s) stack=word(bias+PrepareNative.common+142) /\
 PrepareCopies.staged (mem e) (mem s) (scratch e) (encoding_ptr e) 8 /\
 (forall i j,(i<4)%nat -> vectors s j (28+i)%nat=DecoderFrame.constant i) /\
 (signature=true -> key_signs e s).

Lemma environment signature pol bias e p : setup signature pol bias e p -> setup_caller signature pol bias e (machine p).
Proof. intros [_ [_ [_ [BP [BX [_ [SI [N [_ [Back [Data [_ Signs]]]]]]]]]]]];constructor;try assumption;lia. Qed.

Lemma helper_in pol : In (Decode.HelperBytes.address,Decode.HelperBytes.symbol_bytes) (children pol).
Proof. apply in_or_app;left;do 7 right;left;reflexivity. Qed.

Theorem from_decoder pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 entry pol bias e p -> exists q,inner bias p=Some q /\ setup false pol bias e q.
Proof.
 intros Place Image [PC [Acc [DI [SI [DX [SP [Ret Staged]]]]]]].
 set (origin:=bias+DecoderFrame.origin) in *;set (stack:=common_top pol e-112) in *.
 destruct (stack_ok _ Place) as [[Lo Hi] _].
 assert (Bounds:sp e-1200<=stack<sp e-1000) by (unfold stack,common_top,Rows.frame,sp;destruct pol;lia).
 assert (Private:forall x,DecoderFrame.private_stack stack x -> sp e-2048<=x<stack).
 { intros x H;unfold DecoderFrame.private_stack,DecoderFrame.slot,DecoderFrame.top in H;
   pose proof(Z.mod_pos_bound (stack-40) 64 ltac:(lia));lia. }
 pose proof(proj1(symbols _ _ _ _ Image _ _ (decode_in pol))) as DecodeRange.
 assert (Fits:word64(origin+244)).
 { unfold origin,DecoderFrame.origin,word64;destruct DecodeRange as [L H].
   assert (244<Z.of_nat(length DecoderBytes.symbol_bytes)) by (vm_compute;reflexivity);lia. }
 destruct(mapped_now _ _ _ Image _ _ _ Acc (helper_in pol)) as [Helper Away].
 pose proof(proj1(symbols _ _ _ _ Image _ _ (helper_in pol))) as HelperRange.
 assert (Lit:forall i,(i<4)%nat -> word64(bias+DecoderFrame.at_literal i)).
 { intros i I;pose proof(DecoderFrame.offsets i I) as [L H];unfold DecoderFrame.at_literal,DecoderFrame.helper;
   unfold DecoderFrame.field_offset in *;unfold word64;destruct HelperRange;lia. }
 destruct(DecoderFrame.to_setup origin (machine p) (carry p) stack SP ltac:(lia) Fits)
   as [t [cf [ws [Run [[Stack [BP [Dest [Src [BX Count]]]]] [Back [Writes Values]]]]]]].
 { intros i k I K;unfold origin;replace (bias+DecoderFrame.origin+DecoderFrame.at_literal i-DecoderFrame.origin)
     with (bias+DecoderFrame.at_literal i) by ring;rewrite (word_fits _ (Lit i I)).
   intro X;apply (Away (bias+DecoderFrame.at_literal i+k)).
   - pose proof(DecoderFrame.offsets i I);unfold DecoderFrame.field_offset,DecoderFrame.at_literal,DecoderFrame.helper in *;lia.
   - left;unfold DecoderFrame.slot,span in *;lia. }
 assert (Safe:confined (writable e) ws) by (eapply Forall_impl;[|exact Writes];intros w W x X;left;
    specialize(Private x (W x X));unfold span;lia).
 destruct(mapped_now _ _ _ Image _ _ _ Acc (decode_in pol)) as [Map Apart].
 assert (Start:ip p=origin+0) by (rewrite Z.add_0_r;exact PC).
 destruct(at_segment _ _ _ _ DecoderFrame.code _ 0 _ _ Acc Start Map Apart Run Safe) as [Next Paid].
 eexists;split;[exact Next|]. unfold setup;fold stack;cbn [LinkedRun.finish ip machine absolute cpu_state loc];
   split;[reflexivity|split;[exact Paid|]].
 split;[exact Stack|split;[exact BP|split;[exact (eq_trans BX DI)|split;[exact (eq_trans Dest DI)|split;[unfold source,source_offset;rewrite Z.add_0_r;exact (eq_trans Src SI)|]]]]].
 split;[rewrite Count,DX;reflexivity|split;[exact Back|]]. pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)) as M.
 change (mem t=WriteTrace.replay (mem(machine p)) ws) in M.
 assert (Unchanged:forall x,~DecoderFrame.private_stack stack x -> mem t x=mem(machine p) x)
    by (intros x H;rewrite M;apply (WriteTrace.frame _ _ Writes),H).
 split;[rewrite <-Ret;apply preserved_read with (outside:=fun x=>~DecoderFrame.private_stack stack x);
   [exact Unchanged|intros k K H;specialize(Private _ H);change (0<=k<8) in K;lia]|].
 split.
 - intros j sig k J K;rewrite Unchanged;[exact (Staged j sig k J K)|].
   intro T;specialize(Private _ T);destruct(scratch_stack _ Place);unfold PrepareCopies.dest in *;destruct sig;lia.
 - split;[intros i j I;rewrite (Values _ _ I);exact (DecoderFrame.mapped_value _ bias i I Helper (Lit _ I))|discriminate].
Qed.

From Ed25519Simd.VerifyBatch Require DecoderWords.
Definition transpose bias := segment (bias+DecoderFrame.origin) DecoderFrame.code 16.
Definition input_words signature e s := forall j w,(j<8)%nat -> (w<4)%nat ->
 vectors s j (DecoderWords.result_reg w)=read_word (mem e) (encoding_ptr e j signature+8*Z.of_nat w).
Definition transposed signature bias e p := ip p=bias+DecoderFrame.origin+355 /\ accounted e (writable e) p /\ input_words signature e (machine p) /\
 (forall i j,(i<4)%nat -> vectors(machine p) j (28+i)%nat=DecoderFrame.constant i).

Theorem from_setup signature pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> setup signature pol bias e p ->
 exists q,transpose bias p=Some q /\ transposed signature bias e q /\
 (log q=log p /\ mem(machine q)=mem(machine p) /\ regs(machine q)=regs(machine p)).
Proof.
 intros Place Image Al [PC [Acc [_ [_ [_ [_ [SI [_ [_ [_ [Data [Constants _]]]]]]]]]]]].
 set (o:=bias+DecoderFrame.origin) in *.
 destruct(mapped_now _ _ _ Image _ _ _ Acc (decode_in pol)) as [Map Apart].
 destruct(DecoderWords.mapped_indices _ o Al (proj1(symbols _ _ _ _ Image _ _ (decode_in pol))) Map) as [Aligned L].
 destruct (DecoderWords.read_words o (machine p) (carry p) Aligned L) as [v [Run [Same [Regs [C29 Words]]]]].
 destruct(at_segment _ _ _ o DecoderFrame.code _ 244 _ _ Acc PC Map Apart Run (Forall_nil _)) as [Next Paid].
 eexists;split;[exact Next|split].
 - split;[reflexivity|split;[exact Paid|]].
   split.
   2:{ intros i j I;cbn [LinkedRun.finish machine cpu_state];rewrite C29 by exact I;apply Constants,I. }
   intros j w J W;cbn [LinkedRun.finish machine cpu_state];rewrite Words by assumption.
   rewrite (DecoderWords.contiguous _ _ _ _ SI) by (try assumption;destruct(scratch_ok _ Place) as [[Lo Hi] _];unfold fits64,source,source_offset;destruct signature;lia).
   apply PrepareChunk.Staging.read_block;intros k K.
   replace (source e signature+32*Z.of_nat j+8*Z.of_nat w+k) with
     (PrepareCopies.dest (scratch e) j signature+(8*Z.of_nat w+k)) by (unfold source,source_offset,PrepareCopies.dest;destruct signature;ring).
   rewrite Data by (try exact J;change (0<=k<8) in K;lia);f_equal;ring.
 - cbn [LinkedRun.finish log machine cpu_state];rewrite app_nil_r;auto.
Qed.

From Curve25519 Require Radix51.
From Ed25519Simd.Decode Require Unpack.
From Ed25519Simd.VerifyBatch Require DecoderUnpack.
Definition unpack bias p ks := match DecoderUnpack.take_signs p ks with
 | Some (q,updated)=>option_map (fun r=>(r,updated)) (segment (bias+DecoderFrame.origin) DecoderFrame.code 15 q)
 | None=>None end.
Definition unpacked signature bias e p := ip p=bias+DecoderFrame.origin+462 /\ accounted e (writable e) p /\
 0<=regs(machine p) 0%nat<256 /\ forall j,(j<8)%nat -> let y:=vectors(machine p) j in
 Radix51.split_field y /\ Radix51.limbs y=original_encoding signature e j mod 2^255 /\
 Z.testbit (regs(machine p) 0%nat) (Z.of_nat j)=Z.testbit (original_encoding signature e j) 255.

Theorem from_words signature pol bias e p ks : placement e -> loaded pol bias (mem e) (writable e) ->
 transposed signature bias e p -> exists q updated,unpack bias p ks=Some(q,updated) /\ unpacked signature bias e q /\
 log q=log p /\ mem(machine q)=mem(machine p) /\
 (forall r,r<>0%nat -> regs(machine q) r=regs(machine p) r) /\
 (forall i j,(i<4)%nat -> vectors(machine q) j (28+i)%nat=DecoderFrame.constant i).
Proof.
 intros Place Image [PC [Acc [Keys Mask]]];set (o:=bias+DecoderFrame.origin) in *.
 destruct(mapped_now _ _ _ Image _ _ _ Acc (decode_in pol)) as [Map Apart].
 destruct(DecoderUnpack.signs o p ks PC (proj1(symbols _ _ _ _ Image _ _ (decode_in pol))) Map)
   as [sg [updated [Signs [At [Log [Mem [Vec [Other [_ [Range Bits]]]]]]]]]].
 assert (A:accounted e (writable e) sg) by (split;[rewrite Log;apply Acc|intros x;rewrite Mem,Log;apply Acc]).
 set (src:=fun j=>encoding_ptr e j signature).
 assert (View:forall j w,(j<8)%nat -> (w<4)%nat -> vectors(machine sg) j (DecoderWords.result_reg w)=Unpack.qword (mem e) (src j) w 0%nat).
 { intros j w J W;rewrite Vec,(Keys _ _ J W);unfold Unpack.qword;rewrite Unpack.transpose_ok by lia;reflexivity. }
 destruct(DecoderUnpack.limbs o (machine sg) (carry sg) (mem e) src
   ltac:(intros j J;rewrite Vec;exact (Mask 1%nat j ltac:(lia))) View) as [v [Run [Regs [Flat [Constants Values]]]]].
 destruct(at_segment _ _ _ o DecoderFrame.code _ 365 _ _ A At ltac:(rewrite Mem;exact Map) Apart Run (Forall_nil _)) as [Next Paid].
 eexists;exists updated;split;[unfold unpack;rewrite Signs;fold o;rewrite Next;reflexivity|split].
 - split;[reflexivity|split;[exact Paid|]];cbn [LinkedRun.finish machine cpu_state];rewrite Regs;split;[exact Range|].
   intros j J. pose proof (Ed25519Simd.Decode.Unpack.unpack_correct (mem e) (src j) 0%nat (proj2(proj2(initial_cpu _ Place))) ltac:(lia)) as [Bound [Y Sign]].
   assert (Encoding:Unpack.encoded (mem e) (src j) 0%nat=original_encoding signature e j).
   { destruct signature;unfold original_encoding;cbn [read_input r_bytes key_bytes];rewrite Digest.read_octets by exact (proj2(proj2(initial_cpu _ Place)));unfold Unpack.encoded,src,encoding_ptr;cbn [read_input r_bytes key_bytes];now rewrite Z.add_0_r. }
   rewrite Encoding in Y,Sign;split.
   + intros i I;rewrite Values by assumption;apply Bound,I.
   + split;[rewrite <-Y;apply Radix51.limbs_ext;intros i I;apply Values;assumption|].
     rewrite Bits by exact J;rewrite <-Sign;unfold Unpack.sign.
     change (Z.testbit (vectors(machine p) j (DecoderWords.result_reg 3)) 63=
             Z.testbit (Unpack.qword (mem e) (src j) 3%nat 0%nat) 63).
     rewrite <- (View _ 3%nat J ltac:(lia)),Vec;reflexivity.
 - split;[exact (eq_trans (app_nil_r _) Log)|split;[exact (eq_trans Flat Mem)|split]].
   + intros r R;change (regs v r=regs(machine p) r);rewrite Regs;apply Other,R.
   + intros i j I;change (vectors v j (28+i)%nat=DecoderFrame.constant i);rewrite Constants,Vec by exact I;apply Mask,I.
Qed.
