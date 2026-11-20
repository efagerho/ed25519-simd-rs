From Coq Require Import List ZArith Lia.
From Machine Require Import Instructions Blocks FlatMemory ByteMemory WordBounds MemoryGeometry ScalarRefinement SysV LinkedCalls.
From Ed25519Simd.Double4 Require Double4Spec Double4Memory.
From Ed25519Simd.CachedAdd Require CachedAddSpec CachedAddABI CachedAddMemory.
From Ed25519Simd.LadderStep Require Import Callees Schedule LinkedBytes Audit.
Import ListNotations. Open Scope Z_scope.

Inductive kernel := Double | Plus (full affine:bool) (offset:Z).
Definition target k := match k with Double=>double4_pc | _=>cached_pc end.
Definition parameters k s pt cache := regs s 7%nat=pt /\ match k with
 | Double=>True
 | Plus f a d=>regs s 6%nat=cache+d /\ regs s 2%nat=CachedAddABI.flag_word f /\
    regs s 1%nat=CachedAddABI.flag_word a /\ 0<=d /\ d+CachedAddABI.cache_length a<=3520 /\ d mod 64=0 end.
Definition operation_spec k before after pt cache := match k with
 | Double=>Double4Spec.double4_spec(buffer_words before pt)(buffer_words after pt)
 | Plus f a d=>CachedAddSpec.cached_add_spec f a (buffer_words before pt)
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
Proof. destruct Place as [H _];cbn in H;unfold Ed25519Simd.Double4.Double4ABI.permitted_padding in H;
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
 { unfold ci,push;rewrite SP,word_fits by exact SW;reflexivity. }
 assert (PC:read_word(mem ci)(regs ci 4%nat)=slide+(pc+5)).
 { rewrite M,RS;replace(scratch+1288+pad)with(sp-8)by(unfold sp;ring);now apply write_read_word. }
 assert (End:word64(regs ci 4%nat+8)) by (rewrite RS;geometry).
 assert (Point:forall i,(i<160)%nat ->buffer_words(mem ci)pt i=buffer_words(mem s)pt i).
 { intros;rewrite M;apply read_store_away;geometry. }
 assert (Finish:forall out,call_post scratch ci out ->
   well_formed out /\ regs out 4%nat=sp /\
   (forall r,In r sysv_saved ->regs out r=regs s r) /\ preserved protected (mem s)(mem out)).
 { intros out [W [Rsp [Reg Frame]]];split;[exact W|];split;[rewrite Rsp,RS;unfold sp;ring|].
   split.
   - intros r H;rewrite Reg by exact H;destruct H as[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity.
   - intros x H;rewrite Frame.
     + rewrite M;apply write_outside;unfold protected,sp in H;geometry.
     + rewrite RS;change (~(regs s 7%nat<=x<regs s 7%nat+1280 \/ scratch-16<=x<scratch+1288+pad));rewrite Pt;
       unfold protected,sp in H;geometry. }
 destruct k as [|f a d].
 - pose proof(Code _ _ (or_intror(or_introl eq_refl))) as [Fits [PD [_ SD]]].
   assert (P:Double4Memory.valid_placement(call_loc scratch (slide+double4_pc) ci)dsize pad).
   { unfold Double4Memory.valid_placement,call_loc,layout_at;cbn [origin code_base caller_pc Double4ABI.scratch Double4ABI.point];rewrite PC.
     change(regs ci 7%nat)with(regs s 7%nat);rewrite Pt;repeat apply conj;try assumption;geometry. }
   destruct(double_call _ (slide+cached_pc) _ _ _ Pushed RS End P)as[out [R [F Spec]]].
   exists out;split;[exact (eq_ind_r (fun ret=>dispatch _ _ _ _ _ ci ret out) R (eq_sym PC))|].
   destruct(Finish out F)as[W[S[G T]]];split;[exact W|];split;[exact S|];split;[exact G|];split;[exact T|].
   unfold point_words in Spec;change(regs ci 7%nat)with(regs s 7%nat) in Spec;rewrite Pt in Spec.
   eapply Double4Spec.spec_ext;[intros;symmetry;apply Point;assumption|intros;reflexivity|exact Spec].
 - destruct Args as [Cache [Full [Affine [Off [Len Al]]]]].
   pose proof(Code _ _ (or_intror(or_intror(or_introl eq_refl)))) as [Fits [PD [CD SD]]].
   assert (P:CachedAddMemory.valid_placement a (call_loc scratch (slide+cached_pc) ci)asize pad).
   { unfold CachedAddMemory.valid_placement,call_loc,layout_at;cbn [origin caller_pc code_base CachedAddABI.scratch CachedAddABI.point CachedAddABI.cached];rewrite PC.
     change(regs ci 7%nat)with(regs s 7%nat);change(regs ci 6%nat)with(regs s 6%nat);rewrite Pt,Cache.
     rewrite Z.add_mod,CA,Al by lia;repeat apply conj;try assumption;geometry;reflexivity. }
   destruct(add_call (slide+double4_pc) _ _ _ _ f a Pushed RS End Full Affine P)as[out [R [F Spec]]].
   exists out;split;[change (caller_pc(call_loc scratch (slide+cached_pc) ci)) with
     (read_word(mem ci)(regs ci 4%nat)) in R;now rewrite PC in R|].
   destruct(Finish out F)as[W[S[G T]]];split;[exact W|];split;[exact S|];split;[exact G|];split;[exact T|].
   unfold point_words in Spec;change(regs ci 7%nat)with(regs s 7%nat) in Spec;
   change(regs ci 6%nat)with(regs s 6%nat) in Spec;rewrite Pt,Cache in Spec.
   eapply CachedAddSpec.spec_ext;[intros;symmetry;apply Point;assumption| |intros;reflexivity|exact Spec].
   intros i I;symmetry;rewrite M;apply read_store_away;destruct a;cbn [CachedAddABI.cache_length] in *;geometry.
Qed.
End Step.
