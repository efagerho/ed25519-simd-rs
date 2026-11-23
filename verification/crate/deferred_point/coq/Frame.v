From Coq Require Import List Bool ZArith Lia.
From Machine Require Import execution.Blocks execution.ExecutionProperties execution.WordBounds
  memory.MemoryTrace memory.FlatMemory memory.MemoryCoverage memory.ByteMemory memory.ByteExecution abi.SysV.
From Ed25519Simd Require Import PointFrame.
From Ed25519Simd.Double4 Require Double4ABI Double4Memory FrameProof Double4Bytes ReadFootprint.
From Ed25519Simd.CachedAdd Require CachedAddABI CachedAddMemory FrameProof CachedAddBytes ReadFootprint.
From Ed25519Simd.Point Require Import Double DoubleBytes Add AddBytes DoublePath AddPath.
Import ListNotations. Local Open Scope Z_scope.

Inductive routine := Doubling (private:bool) | Addition (m:add_mode).
Definition body k := match k with Doubling _=>Double.program | Addition _=>Add.program end.
Definition layout_for k := match k with Doubling _=>Double4ABI.abi_layout | Addition m=>CachedAddABI.abi_layout (affine m) end.
Definition fuel k := match k with Doubling _=>250%nat | Addition _=>180%nat end.
Definition events k := match k with Doubling b=>double_effects b | Addition m=>add_effects m end.
Definition entry k := match k with Doubling b=>double_entry b | Addition m=>add_entry m end.
Definition tracked k pad := match k with Doubling _=>Double4Memory.mapped pad | Addition m=>CachedAddMemory.mapped (affine m) pad end.
Definition size k := Z.of_nat(length (image (body k))).
Definition placement_ok k loc pad := match k with
 | Doubling _=>point_placement loc (size k) pad
 | Addition m=>CachedAddMemory.valid_placement (affine m) loc (size k) pad end.
Definition read_ok k := match k with Doubling _=>Double4.ReadFootprint.point_reads_xyz
 | Addition m=>CachedAdd.ReadFootprint.cache_reads_bounded (affine m) end.
Definition observation pad (result:control*list event) := let '(c,es):=result in
  (map (gpr c) sysv_saved, forallb(write_ok pad)es && check_stack[(caller_slot pad,Caller)]es).
Lemma frame_checked k incoming pad bp : permitted_padding pad ->word64 bp ->
 let c:=entry k incoming pad bp in
 option_map(observation pad)(record_path (fuel k) (body k) (layout_for k) c)=
 Some(map(gpr c)sysv_saved,true).
Proof.
 intros Pad BP;destruct Pad as[<-|[<-|[<-|[<-|[]]]]];destruct k as [[]|[[] []|]];
 lazy -[stack_word];
 change (Some([gpr incoming 3%nat;Int(stack_word(stack_word bp));gpr incoming 12%nat;
 gpr incoming 13%nat;gpr incoming 14%nat;gpr incoming 15%nat],
 if Z.eqb(stack_word bp)(stack_word bp)then true else false)=
 Some([gpr incoming 3%nat;Int bp;gpr incoming 12%nat;gpr incoming 13%nat;
 gpr incoming 14%nat;gpr incoming 15%nat],true));
 rewrite Z.eqb_refl;unfold stack_word;rewrite Z.mod_mod by lia;rewrite Z.mod_small by exact BP;reflexivity.
Qed.
Lemma control_checked k incoming pad bp : permitted_padding pad ->
 observe(path (fuel k) (body k) (layout_for k) (entry k incoming pad bp))=
 Some(Caller,Ptr(scratch,1296+pad),events k).
Proof. destruct k;[apply double_path|apply add_path]. Qed.
Lemma access_checked k :
 forallb (read_ok k) (flat_map (read_addresses (body k)) (events k))=true /\
 forallb(fun i=>existsb(ptr_eq(point,64*Z.of_nat i))(written_vectors(events k)))(seq 0 20)=true.
Proof. destruct k as [[]|[[] []|]];split;vm_compute;reflexivity. Qed.
Lemma place_point k loc pad : placement_ok k loc pad -> point_placement loc (size k) pad.
Proof. destruct k;[auto|apply proj1]. Qed.
Lemma separate k loc pad : placement_ok k loc pad ->separated loc (allowed_write pad) (tracked k pad).
Proof. destruct k;[apply Double4.FrameProof.placement_separates|apply CachedAdd.FrameProof.placement_separates]. Qed.
Definition footprint k loc es :=
 (forall a,In a(flat_map(read_addresses(body k))(data_effects es)) ->read_ok k a=true) /\
 (forall off,0<=off<1280 ->writes_at loc es(origin loc point+off)).

Theorem point_frame k incoming pad bp d loc before :
 let c:=entry k incoming pad bp in
 placement_ok k loc pad ->word64 bp ->state_words(c,d) ->byte_memory before ->
 agrees loc(tracked k pad)d(return_memory c)before ->
 exists last es, let final:=(last,effects (body k) (events k) d) in
 let after:=replay (body k) loc es d before in
 record_path (fuel k) (body k) (layout_for k) c=Some(last,es) /\
 call_result (body k) (layout_for k) (c,d) final (footprint k loc es)
   (byte_execution (body k) (layout_for k) loc (tracked k pad) (writable_byte loc pad)
     (c,d) final before after) True.
Proof.
 intros c Place BP W Bytes Agree. pose proof(place_point _ _ _ Place)as Place0.
 pose proof(proj1 Place0)as Pad. pose proof(frame_checked k incoming pad bp Pad BP) as Check.
 cbn zeta in Check;fold c in Check. destruct(record_path _ _ _ c)as[[last es]|]eqn:R;[|discriminate].
 apply (f_equal (fun x=>match x with Some z=>fst z | None=>[] end)) in Check as Saved.
 apply (f_equal (fun x=>match x with Some z=>snd z | None=>false end)) in Check as Safe.
 change (forallb (write_ok pad) es && check_stack [(caller_slot pad,Caller)] es=true) in Safe.
 apply andb_true_iff in Safe as [Writes Balanced];apply write_ok_sound in Writes;apply check_stack_sound in Balanced.
 pose proof(proj1(record_path_sound _ _ _ _ _ _ R))as P.
 pose proof(control_checked k incoming pad bp Pad)as Path;fold c in Path;rewrite P in Path.
 cbn [observe] in Path;injection Path as End SP Ops.
 pose proof(path_returns _ _ _ _ _ _ P d)as Ret. rewrite Ops in Ret.
 exists last,es;split;[reflexivity|];constructor.
 - exact Ret.
 - unfold restores_rsp;cbn [fst];rewrite SP;unfold c;destruct k as [[]|[[] []|]];change (Some (Ptr (scratch,1296+pad))=Some (Ptr (scratch,1288+pad+8)));f_equal;f_equal;f_equal;lia.
 - unfold preserves_sysv;cbn [fst];apply ext_in_map;exact Saved.
 - split;[rewrite Ops;apply forallb_forall, (proj1(access_checked k))|].
   apply (MemoryCoverage.output_trace_covered point 20 es);rewrite Ops;apply access_checked.
 - pose proof (recorded_frame _ _ _ _ _ _ d loc _ (tracked k pad) (writable_byte loc pad)
     (entry_rsp loc pad) _ before R Writes Balanced Agree (separate _ _ _ Place)
     (fun ops x=>permitted_bytes loc pad ops x Pad)
     (fun k H=>caller_byte_protected loc _ pad k Place0 H))as F.
   assert(L:forall a,In a(map fst [(caller_slot pad,Caller)]) ->tracked k pad(ReturnSlot a)).
   { intros a [<-|[]];destruct k;right;reflexivity. }
   assert(S:forall a,allowed_write pad(ReturnSlot a)->tracked k pad(ReturnSlot a)).
   { intros a H;destruct k;now left. }
   destruct(F L S)as[A [Outside [Pre Pop]]]. rewrite Ops in A.
   eapply recorded_bytes;[apply Ret|exact W|exact Bytes|exact R|exact A|exact Outside| |exact Pop].
   intros;apply (proj1 (Pre _ _ H)).
 - exact I.
Qed.
