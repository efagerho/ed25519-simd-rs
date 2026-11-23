From Ed25519Simd Require Import PointResults.
From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.Blocks memory.FlatMemory memory.ByteMemory execution.WordBounds memory.MemoryGeometry execution.ScalarRefinement abi.SysV execution.LinkedCalls abi.CallFrame.
From Ed25519Simd.Double4 Require Double4Spec Double4Memory.
From Ed25519Simd.CachedAdd Require CachedAddSpec CachedAddABI CachedAddMemory.
From Ed25519Simd.LadderStep Require Import Callees Schedule LinkedBytes Audit.
Import ListNotations. Open Scope Z_scope.

Inductive kernel := Double | Plus (full affine:bool) (offset:Z).
Definition target k := match k with Double=>double4_pc | Plus f a _=>add_target cached_pc f a end.
Definition parameters k s pt cache := regs s 7%nat=pt /\ match k with
 | Double=>True
 | Plus f a d=>regs s 6%nat=cache+d /\ mode_args f a s /\ 0<=d /\ d+CachedAddABI.cache_length a<=3520 /\ d mod 64=0 end.
Definition operation_spec k before after pt cache := match k with
 | Double=>double_spec defer_double (buffer_words before pt)(buffer_words after pt)
 | Plus f a d=>addition_spec (defer_add f a) f a (buffer_words before pt)
    (buffer_words before(cache+d)) (buffer_words after pt) end.

Lemma linked_regions_separate : separate_images.
Proof. vm_compute;intuition discriminate. Qed.

Section Step.
Variables slide scratch pad pt cache : Z.
Hypothesis Place : placement_ok slide scratch pad pt cache.
Let sp := scratch+1296+pad. (* after the three wrapper pushes *)
Definition protected x := ~(pt<=x<pt+1280 \/ scratch-16<=x<sp).
Local Ltac geometry :=
 unfold fits64, disjoint,word64,sp in *;try lia.
Lemma padding_bounds : 0<=pad<=48.
Proof. destruct Place as [H _];cbn in H;unfold PointFrame.permitted_padding in H;
 destruct H as [<-|[<-|[<-|[<-|[]]]]];lia. Qed.

(* All calls push into the same eight-byte slot. Convert the callee's
   frame to the caller's protected region and remove that push from its
   arithmetic inputs. *)
Lemma call_once k pc s : wrapper_pc<=pc -> pc+5<wrapper_pc+wrapper_size ->
 well_formed s -> regs s 4%nat=sp -> parameters k s pt cache ->
 let ci:=push s (slide+(pc+5)) in
 exists out,
 dispatch (slide+double4_pc)(slide+cached_pc) scratch pad (slide+target k)
   ci (slide+(pc+5)) out /\ well_formed out /\ regs out 4%nat=sp /\
 (forall r,In r sysv_saved -> regs out r=regs s r) /\
 preserved protected (mem s)(mem out) /\ operation_spec k (mem s)(mem out) pt cache.
Proof.
 intros Lo Hi WF SP [Pt Args] ci.
 destruct linked_regions_separate as [WD [WA DA]].
 pose proof padding_bounds as PadBounds;destruct Place as [Pad SA PA CA SF PF CF PS CS CP Code].
 pose proof(Code _ _ (or_introl eq_refl)) as [WFits _].
 assert (PW:word64(slide+(pc+5))) by geometry.
 assert (SW:word64(sp-8)) by geometry.
 assert (SW':word64(sp)) by geometry.
 assert (Pushed:well_formed ci) by (apply push_wf;exact WF).
 assert (RS:regs ci 4%nat=scratch+1288+pad).
 { change (word(regs s 4%nat-8)=scratch+1288+pad);rewrite SP,word_fits by exact SW;unfold sp;ring. }
 assert (M:mem ci=store_word(mem s)(sp-8)(slide+(pc+5))).
 { unfold ci,push,push_words;rewrite SP,word_fits by exact SW;reflexivity. }
 assert (PC:read_word(mem ci)(regs ci 4%nat)=slide+(pc+5)).
 { now apply pushed_return_word. }
 assert (End:word64(regs ci 4%nat+8)) by (rewrite RS;geometry).
 assert (Point:forall i,(i<160)%nat ->buffer_words(mem ci)pt i=buffer_words(mem s)pt i).
 { intros;rewrite M;apply read_store_away;geometry. }
 assert (Finish:forall out,call_post scratch ci out ->
   well_formed out /\ regs out 4%nat=sp /\
   (forall r,In r sysv_saved ->regs out r=regs s r) /\ preserved protected (mem s)(mem out)).
 { intros out F. rewrite <-SP. eapply resume_sysv_frame; [now rewrite SP| |exact F].
   intros x H; unfold callee_writable; rewrite RS.
   change (regs ci 7%nat) with (regs s 7%nat); rewrite Pt,SP.
   unfold protected,sp in H; geometry. }
 destruct k as [|f a d].
 - pose proof(Code _ _ (or_intror(or_introl eq_refl))) as [Fits [PD [_ SD]]].
   assert (P:Double4Memory.valid_placement(call_loc scratch (slide+double4_pc) ci)dsize pad).
   { unfold Double4Memory.valid_placement,PointFrame.point_placement,call_loc,layout_at;cbn [origin code_base caller_pc PointFrame.scratch PointFrame.point];rewrite PC.
     change(regs ci 7%nat)with(regs s 7%nat);rewrite Pt;repeat apply conj;try assumption;geometry. }
   destruct(mode_double_call _ (slide+cached_pc) _ _ _ Pushed RS End P)as[out [R [F Spec]]].
   exists out;split;[exact (eq_ind_r (fun ret=>dispatch _ _ _ _ _ ci ret out) R (eq_sym PC))|].
   destruct(Finish out F)as[W[S[G T]]];split;[exact W|];split;[exact S|];split;[exact G|];split;[exact T|].
   unfold point_words in Spec;change(regs ci 7%nat)with(regs s 7%nat) in Spec;rewrite Pt in Spec.
   eapply double_spec_ext;unfold agrees_words;[intros;symmetry;apply Point;assumption|intros;reflexivity|exact Spec].
 - destruct Args as [Cache [Modes [Off [Len Al]]]].
   pose proof(Code _ _ (or_intror(or_intror(or_introl eq_refl)))) as [Fits [PD [CD SD]]].
   assert (P:CachedAddMemory.valid_placement a (call_loc scratch (slide+cached_pc) ci)asize pad).
   { unfold CachedAddMemory.valid_placement,PointFrame.point_placement,call_loc,layout_at;cbn [origin caller_pc code_base PointFrame.scratch PointFrame.point CachedAddABI.cached];rewrite PC.
     change(regs ci 7%nat)with(regs s 7%nat);change(regs ci 6%nat)with(regs s 6%nat);rewrite Pt,Cache.
     rewrite Z.add_mod,CA,Al by lia;repeat apply conj;try assumption;geometry;reflexivity. }
   assert (Dist:slide+double4_pc<>add_target (slide+cached_pc) f a).
   { unfold add_target;assert (N:double4_pc<>cached_pc+add_offset f a) by (destruct f,a;vm_compute;discriminate);lia. }
   destruct(mode_add_call (slide+double4_pc) _ _ _ _ f a Dist Pushed RS End Modes P)as[out [R [F Spec]]].
   exists out;split;[change (caller_pc(call_loc scratch (slide+cached_pc) ci)) with
     (read_word(mem ci)(regs ci 4%nat)) in R;rewrite PC in R;replace (slide+target (Plus f a d)) with (add_target (slide+cached_pc) f a) by (unfold target,add_target;ring);exact R|].
   destruct(Finish out F)as[W[S[G T]]];split;[exact W|];split;[exact S|];split;[exact G|];split;[exact T|].
   unfold point_words in Spec;change(regs ci 7%nat)with(regs s 7%nat) in Spec;
   change(regs ci 6%nat)with(regs s 6%nat) in Spec;rewrite Pt,Cache in Spec.
   eapply addition_spec_ext;unfold agrees_words;[intros;symmetry;apply Point;assumption| |intros;reflexivity|exact Spec].
   intros i I;symmetry;rewrite M;apply read_store_away;destruct a;cbn [CachedAddABI.cache_length] in *;geometry.
Qed.
End Step.
