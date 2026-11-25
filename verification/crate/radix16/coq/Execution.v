From Machine Require memory.BlockWrites memory.PackedWrites memory.WriteTrace abi.TracedCalls.
From Machine Require execution.ProjectionWords execution.ScalarWords.
From Curve25519 Require Import SignedRadix16.
From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Blocks execution.WordBounds execution.WordSemantics
 execution.LinkedCalls execution.Packed memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.PackedMemory
 abi.SysV abi.CallFrame execution.KnownRegisters.
From Ed25519Simd.Scalar Require Import ScalarSpec ScalarMemory ScalarABI ScalarBytes.
From Ed25519Simd.Scalar Require Audit Object.
From Ed25519Simd.Radix16 Require Import Program LinkedBytes Packing Routing Audit.
Import ListNotations. Local Open Scope Z_scope.

Local Notation pc := wrapper_pc. Local Notation target := reducer_pc.
Local Notation n := (size LinkedBytes.symbol_bytes).
Local Notation m := (size Ed25519Simd.Scalar.Object.object_bytes).

Lemma child_events_unique a s xs ys : child_events a s xs -> child_events a s ys -> xs=ys.
Proof.
 intros [n [f [es [R ->]]]] [m [g [ts [S ->]]]].
 pose proof (walk_unique _ _ _ _ _ _ R S) as E;injection E as _ ->;reflexivity.
Qed.

Lemma traced_unique slide entry ip out xs ys : traced slide pc target n entry ip out xs ->
 traced slide pc target n entry ip out ys -> xs=ys.
Proof.
 unfold traced;cbv zeta;destruct (caller_step slide (pc+1) (Invoke target) _) as [a s].
 intros [_ [m [u [A [U [_ ->]]]]]] [_ [f [v [B [V [_ ->]]]]]].
 destruct(callee_unique _ _ _ _ _ _ _ _ _ A B) as [_ ->].
 now rewrite (child_events_unique _ _ _ _ U V).
Qed.

Local Lemma reduce_ok addr s : well_formed s -> word64 (regs s 4%nat+8) ->
 valid_placement (location addr s) m ->
 exists out, reduce addr s (caller_pc (location addr s)) out /\
 sysv_return (writable_byte (location addr s)) s out /\
 scalar_spec (ByteMemory.buffer_words (mem s) (regs s 6%nat))
             (ByteMemory.buffer_words (mem out) (regs s 7%nat)) /\
 exists ws,child_events addr s ws /\ mem out=WriteTrace.replay (mem s) ws /\
 WriteTrace.confined (writable_byte (location addr s)) ws.
Proof.
 intros [Words [Vec Bytes]] SP Place; set (loc:=location addr s).
 assert (E:concrete_entry loc m (regs s) (vectors s) (mem s)) by
   (constructor;try assumption;reflexivity).
 destruct (Ed25519Simd.Scalar.Audit.run_concrete Ed25519Simd.Scalar.Object.assembled_scalar_correct
             loc _ _ (flag s) _ E) as [final [after R]].
 destruct(concrete_entry_representable _ _ _ _ (flag s) _ E) as [_ [_ [_ Entry]]].
 pose proof (did_return R) as Run; pose proof (byte_guarantee R) as Frame.
 assert (Known:known_registers (fst (entry_from_bytes loc (regs s) (vectors s) (flag s) (mem s)))).
 { intros r U;specialize (Entry r);rewrite U in Entry;discriminate. }
 destruct (lift_return _ _ _ _ _ _ _ _ _ Known Run Frame) as [C [W F]].
 destruct (BlockWrites.byte_execution_writes _ _ _ _ _ _ _ _ _ Frame) as [fuel [es [Trace [Replay Bound]]]].
 exists (export_state loc final after);split;[exact C|];split.
 2: { split;[exact (computed_output R)|].
      eexists;split;[unfold child_events;eexists _,_,_;split;[exact Trace|reflexivity]|].
      split;[exact Replay|apply (Bound es nil);symmetry;apply app_nil_r]. }
 eapply project_sysv_return with (next_rsp:=(0%nat,8));try eassumption;
 [reflexivity|reflexivity|apply (SysV.restored_stack R)|apply (SysV.saved_registers R)].
Qed.

Local Lemma call_step slide s :
 caller_step slide (pc+1) (Invoke target) s=
 (word (slide+target),push s (slide+(pc+6))).
Proof.
 change ((word (slide+call_destination (pc+1) target),push s (slide+(pc+1+5)))=(word (slide+target),push s (slide+(pc+6)))).
 rewrite call_destination_correct by (vm_compute; reflexivity).
 replace (pc+1+5) with (pc+6) by ring;reflexivity.
Qed.

Section Run.
Variable slide:Z. Variable entry:cpu.
Let sp:=regs entry 4%nat. Let dst:=regs entry 7%nat. Let src:=regs entry 6%nat.
Hypothesis P:placement sp dst src (slide+pc) n (slide+target) m.
Hypothesis W:well_formed entry.
Let ret:=read_word (mem entry) sp.
Let saved:=push entry dst.
Let next:=slide+(pc+6).
Let invoked:=push saved next.

Local Lemma code_facts : 6<n /\ 0<m /\ disjoint pc n target m.
Proof. vm_compute; intuition discriminate. Qed.
Local Ltac geom :=
 let D:=fresh in let S:=fresh in
 destruct P as [Stack Align D S DS DT ST Codes];
 destruct (Codes _ _ (or_introl eq_refl)) as [WC [WD [WS WT]]];
 destruct (Codes _ _ (or_intror (or_introl eq_refl))) as [HC [HD [HS HT]]];
 destruct code_facts as [Width [Helper ApartCode]];
 unfold fits64,disjoint,word64 in *; unfold next in *;lia.
Local Lemma sp1 : regs saved 4%nat=sp-8.
Proof. change (word (sp-8)=sp-8); apply word_fits;geom. Qed.
Local Lemma sp2 : regs invoked 4%nat=sp-16.
Proof. change (word (regs saved 4%nat-8)=sp-16);rewrite sp1,word_fits by geom;lia. Qed.
Local Lemma image_mem :
 mem invoked=store_word (store_word (mem entry) (sp-8) dst) (sp-16) next.
Proof. lazymatch goal with |- _ = ?rhs => change (store_word (store_word (mem entry) (word (sp-8)) dst) (word (regs saved 4%nat-8)) next=rhs) end.
 rewrite sp1, !word_fits by geom. replace (sp-8-8) with (sp-16) by ring;reflexivity.
Qed.
Local Lemma call_ret : caller_pc (location (slide+target) invoked)=next.
Proof. apply pushed_return_word;geom. Qed.
Local Lemma reducer_placement : valid_placement (location (slide+target) invoked) m.
Proof.
 unfold valid_placement;rewrite call_ret.
 change (origin (location (slide+target) invoked) output) with dst.
 change (origin (location (slide+target) invoked) input) with src.
 change (origin (location (slide+target) invoked) stack) with (regs invoked 4%nat).
 change (code_base (location (slide+target) invoked)) with (slide+target).
 rewrite sp2;repeat split;try geom.
 - replace (sp-16) with (sp+(-1)*16) by ring;rewrite Z.mod_add by lia;apply P.
Qed.
Local Lemma initial_frame : preserved (fun x=>~(sp-16<=x<sp)) (mem entry) (mem invoked).
Proof. intros x A;rewrite image_mem; unfold store_word;repeat rewrite write_outside by lia;reflexivity. Qed.

Local Lemma read_input j : (j<8)%nat ->
 lane_input (ByteMemory.buffer_words (mem invoked) src) j =
 lane_input (ByteMemory.buffer_words (mem entry) src) j.
Proof.
 intro J;unfold lane_input;f_equal;apply map_ext_in;intros i I; apply in_seq in I.
 unfold ByteMemory.buffer_words;apply preserved_read with(outside:=fun x=>~(sp-16<=x<sp)).
 - apply initial_frame.
 - intros k K; change (0<=k<8) in K;rewrite Nat2Z.inj_add,Nat2Z.inj_mul;
   change (Z.of_nat 8) with 8;geom.
Qed.
Local Lemma tail_output s j k : (j<8)%nat -> (k<64)%nat ->
 (forall i,(i<5)%nat ->0<=limb_words s (8*i+j)%nat<B) ->
 mem (execute 8 tail s) (regs s 7%nat+64*Z.of_nat j+Z.of_nat k)=
 (digit (lane_output (limb_words s) j) k) mod 256.
Proof.
 intros J K Bnd;destruct(routed j k J K) as [v [Store Byte]].
 unfold execute;rewrite row_byte by assumption;fold result_state.
 rewrite Store,Byte;apply expected_digit;assumption.
Qed.

Local Lemma tail_frame s :
 preserved (fun x=>~(regs s 7%nat<=x<regs s 7%nat+512)) (mem s) (mem(execute 8 tail s)).
Proof.
 intros x Outside;apply outside_rows,Outside.
Qed.
Lemma run_view ip out :
 run slide pc target n entry ip out <->
 exists mid,reduce (slide+target) invoked next mid /\
 caller_step slide (pc+n-1) Return (execute 8 tail (pop mid 7))=(ip,out).
Proof.
 unfold run; cbn zeta. change (snd (caller_step slide pc (Save 7) entry)) with saved.
 rewrite call_step. change (push saved (slide+(pc+6))) with invoked.
 rewrite (word_fits (slide+target)), (word_fits (slide+(pc+6))) by geom.
 split;[tauto|intros;split;[reflexivity|assumption]].
Qed.
Local Lemma unique_run ip out ip' out' :
 run slide pc target n entry ip out -> run slide pc target n entry ip' out' ->
 ip=ip' /\ out=out'.
Proof.
 rewrite !run_view; intros [a[A X]][b[B Y]];
 destruct(callee_unique _ _ _ _ _ _ _ _ _ A B)as[_ ->];congruence || (rewrite X in Y;inversion Y;auto).
Qed.

Local Lemma restored_destination mid : regs mid 4%nat=sp-8 ->
 preserved (fun x=>~(dst<=x<dst+320)) (mem invoked) (mem mid) -> regs (pop mid 7) 7%nat=dst.
Proof.
 intros S Frame. change (read_word (mem mid) (word (regs mid 4%nat))=dst).
 rewrite S,(word_fits (sp-8)) by geom.
 assert (Read:read_word (mem mid) (sp-8)=read_word (mem invoked) (sp-8)).
 { apply preserved_read with (outside:=fun x=>~(dst<=x<dst+320));[exact Frame|].
   intros k K;change (0<=k<8) in K;geom. }
 rewrite Read,image_mem,read_other_word by (unfold disjoint;lia). apply write_read_word,W.
Qed.

Theorem traced_digest ip out : run slide pc target n entry ip out ->
 exists ws,traced slide pc target n entry ip out ws /\
 (forall x,mem out x=WriteTrace.replay (mem entry) ws x) /\
 forall pre rest,ws=pre++rest -> WriteTrace.confined (writable sp dst) pre.
Proof.
 intro Run;apply run_view in Run as [other [Exec End]].
 assert (Wcall:well_formed invoked) by (apply push_wf,push_wf,W).
 destruct (reduce_ok _ _ Wcall ltac:(rewrite sp2;geom) reducer_placement) as
   [mid [Call [[_ [SP [_ _]]] [_ [child [Trace [Replay Bound]]]]]]].
 rewrite call_ret in Call. destruct(callee_unique _ _ _ _ _ _ _ _ _ Exec Call) as [_ ->].
 set (back:=pop mid 7).
 assert (Dest:regs back 7%nat=dst).
 { apply restored_destination;[rewrite SP,sp2;ring|]. intros x X;rewrite Replay;apply (WriteTrace.frame _ _ Bound);exact X. }
 set (tail_writes:=PackedWrites.trace (slide+pc+7) back Packed.initial tail).
 destruct (PackedWrites.execution false 8 (slide+pc+7) tail back ltac:(vm_compute;reflexivity)) as [Tail TailReplay].
 set (own:=StoreInstructions.caller_stores slide pc (Save 7) entry ++
    StoreInstructions.caller_stores slide (pc+1) (Invoke target) saved).
 exists (own++child++tail_writes);split.
 - unfold traced;cbn zeta;change (snd (caller_step slide pc (Save 7) entry)) with saved.
   rewrite call_step,(word_fits (slide+target)),(word_fits (slide+(pc+6))) by geom.
   split;[reflexivity|exists mid,child;split;[exact Call|split;[exact Trace|split;[exact End|reflexivity]]]].
 - assert (OwnMem:WriteTrace.replay (mem entry) own=mem invoked).
   { unfold own;rewrite WriteTrace.replay_app;reflexivity. }
   split.
   + intros x;rewrite !WriteTrace.replay_app,OwnMem,<-Replay.
     change (mem out x=WriteTrace.replay (mem back) tail_writes x).
     assert (M:mem out=mem (execute 8 tail back)).
     { pose proof(f_equal (fun res=>mem (snd res)) End) as H;symmetry;exact H. }
     rewrite M;apply TailReplay.
   + assert (All:WriteTrace.confined (writable sp dst) (own++child++tail_writes)).
     { apply Forall_app;split.
       - unfold own,StoreInstructions.caller_stores;cbn [app]. fold sp;rewrite sp1.
         rewrite (word_fits (sp-8)),(word_fits (sp-8-8)) by geom.
         repeat apply Forall_cons;try apply Forall_nil;intros x X;right;
           unfold WriteTrace.touches in X;cbn [WriteTrace.address WriteTrace.size WriteTrace.qword] in X;lia.
       - apply Forall_app;split.
         + eapply TracedCalls.lend;[|exact Bound]. intros x X;left;change (dst<=x<dst+320) in X;lia.
         + eapply TracedCalls.lend;[|exact Tail]. intros x X;left;unfold PackedWrites.region in X;now rewrite Dest in X. }
     intros pre rest Eq;rewrite Eq in All;now apply Forall_app in All as [A _].
Qed.

(* Range-check the register expressions left by the linked packing tail,
   including registers it leaves untouched. *)
Local Lemma tail_registers s : well_formed s ->
 let t:=returning (execute 8 tail s) in (forall r,word64(regs t r)) /\
 (forall j r,(j<8)%nat -> word64(vectors t j r)).
Proof.
 intros Valid t;split.
 - intros r;apply put_words;[|apply mod64_word].
   intro g;change (word64 (update (regs s) 0 (value s (acc result_state)) g)).
   unfold update;destruct (g=?0)%nat;[apply ProjectionWords.packed_ok;[exact Valid|vm_compute;reflexivity]|apply Valid].
 - intros j r J;apply ProjectionWords.packed_ok;[exact Valid|].
   destruct(Nat.lt_ge_cases r 32) as [R|R].
   + assert (Rows:forallb (fun k=>forallb (fun i=>ProjectionWords.packed (qword (zmm result_state i) k))
         (seq 0 32)) (seq 0 8)=true) by (vm_compute;reflexivity).
     apply forallb_forall with (x:=j) in Rows;[|apply in_seq;lia].
     apply forallb_forall with (x:=r) in Rows;[exact Rows|apply in_seq;lia].
   + do 32 (destruct r as [|r];[lia|]);change ((j<?8)%nat=true);apply Nat.ltb_lt,J.
Qed.

Theorem digest_returns : exists out,
 run slide pc target n entry ret out /\
 (forall ip oth,run slide pc target n entry ip oth ->ip=ret /\ oth=out) /\
 regs out 4%nat=sp+8 /\ (forall r,In r sysv_saved -> regs out r=regs entry r) /\
 preserved (fun x=>~writable sp dst x) (mem entry)(mem out) /\
 well_formed out /\
 (forall j,(j<8)%nat ->let ds:=signed_digits (mem out) dst j in
   Forall (fun d=> -8<=d<8) ds /\ number 16 ds=lane_input (ByteMemory.buffer_words (mem entry) src) j mod L).
Proof.
 assert (Wcall:well_formed invoked) by (apply push_wf,push_wf,W).
 destruct(reduce_ok _ _ Wcall ltac:(rewrite sp2;geom) reducer_placement)
   as [mid [Call [[Wmid [SP [Saved Frame]]] [Spec _]]]].
 rewrite call_ret in Call. rewrite sp2 in SP;replace (sp-16+8) with (sp-8) in SP by ring.
 change (preserved (fun x=>~(dst<=x<dst+320)) (mem invoked) (mem mid)) in Frame.
 change (scalar_spec (ByteMemory.buffer_words (mem invoked) src)
                     (ByteMemory.buffer_words (mem mid) dst)) in Spec.
 set (resume:=pop mid 7).
 assert (D:regs resume 7%nat=dst) by (apply restored_destination;assumption).
 assert (S:regs resume 4%nat=sp).
 { change (word (regs mid 4%nat+8)=sp). rewrite SP,word_fits by geom;lia. }
 set (body:=execute 8 tail resume).
 assert (BS:regs body 4%nat=sp) by exact S.
 assert (F:preserved (fun x=>~writable sp dst x) (mem entry) (mem body)).
 { intros x X; transitivity (mem resume x).
   - apply tail_frame;rewrite D;unfold writable in X;tauto.
   - change (mem mid x=mem entry x);unfold writable in X;
     rewrite Frame by lia;apply initial_frame;lia. }
 assert (BC:read_word (mem body) sp=ret).
 { unfold ret;apply preserved_read with(outside:=fun x=>~writable sp dst x);[exact F|].
   intros k K;change(0<=k<8)in K;unfold writable;geom. }
 assert (End:caller_step slide (pc+n-1) Return body=(ret,returning body)).
 { change ((word (read_word (mem body) (word (regs body 4%nat))),returning body)=(ret,returning body)).
   rewrite BS,(word_fits sp) by geom;rewrite BC,word_fits;[reflexivity|apply read_word_bound,W]. }
 assert (Run: run slide pc target n entry ret (returning body)).
 { apply run_view;exists mid;auto. }
 exists (returning body);split;[exact Run|];split;[intros;eapply unique_run;eassumption|].
 split.
 - change (word (regs body 4%nat+8)=sp+8);rewrite BS;apply word_fits;geom.
 - split.
   + intros r H;specialize (Saved r H);destruct H as[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];exact Saved.
   + split;[exact F|]. split.
     { destruct (tail_registers resume (ScalarWords.pop_words mid 7 Wmid)) as [G V].
       split;[exact G|split;[exact V|]]. intro a. change (0<=mem body a<256).
       destruct (Z_lt_ge_dec a dst), (Z_lt_ge_dec a (dst+512));
         try (unfold body;rewrite tail_frame by (rewrite D;lia);apply Wmid).
       set (j:=Z.to_nat ((a-dst)/64));set (k:=Z.to_nat ((a-dst) mod 64)).
       pose proof (Z.mod_pos_bound (a-dst) 64 ltac:(lia)) as K.
       assert (Q:0<=(a-dst)/64<8) by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
       assert (A:a=dst+64*Z.of_nat j+Z.of_nat k) by
         (unfold j,k;rewrite !Z2Nat.id by lia;pose proof (Z.div_mod (a-dst) 64 ltac:(lia));lia).
       rewrite A;unfold body;rewrite <-D,tail_output.
       - apply Z.mod_pos_bound;lia.
       - unfold j;lia.
       - unfold k;lia.
       - unfold limb_words;rewrite D;apply Spec;unfold j;lia. }
     intros j J;cbn zeta.
     set (x:=lane_input (ByteMemory.buffer_words (mem entry) src) j mod L).
     destruct(Spec j J) as [Val Bounds];rewrite read_input in Val by exact J;fold x in Val.
     assert (V:lane_output (limb_words resume) j=x) by (unfold limb_words;rewrite D;exact Val).
     assert (Digit:forall k,(k<64)%nat ->
       signed_byte (mem (returning body) (dst+64*Z.of_nat j+Z.of_nat k))=digit x k).
     { intros k K;change (signed_byte (mem body (dst+64*Z.of_nat j+Z.of_nat k))=digit x k).
       unfold body;rewrite <-D,tail_output by
        (auto;unfold limb_words;rewrite D;apply Bounds).
       rewrite V,signed_encoding;[reflexivity|apply digit_range]. }
     unfold signed_digits;rewrite (map_ext_in _ (digit x)) by (intros k K;apply Digit;apply in_seq in K;lia).
     split;[apply Forall_forall;intros d H;apply in_map_iff in H as[k[<- _]];apply digit_range|].
     apply reconstruct,canonical_residue.
Qed.
End Run.
