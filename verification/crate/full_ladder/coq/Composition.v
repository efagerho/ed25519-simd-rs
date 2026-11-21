From Coq Require Import ZArith List Lia Bool.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.ByteMemory
 memory.FlatMemory memory.MemoryGeometry execution.WordSemantics.
From Curve25519 Require Import Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Import Program Operands Seed Execution Native.
From Ed25519Simd.LadderStep Require Audit.
Import ListNotations. Local Open Scope Z_scope.

Definition agrees n (w v:buffer) := forall i,(i<n)%nat -> w i=v i.
Definition words n (w:buffer) := forall i,(i<n)%nat -> word64(w i).
Definition overlay (m:bytes) addr n (w:buffer) x :=
 let d:=x-addr in if (0<=?d)&&(d<?8*Z.of_nat n)
 then word_byte (w (Z.to_nat (d/8))) (d mod 8) else m x.
Lemma overlay_out m a n w x : ~(a<=x<a+8*Z.of_nat n) -> overlay m a n w x=m x.
Proof. unfold overlay;intro H;destruct (_ && _)%bool eqn:E;[|reflexivity].
 apply andb_true_iff in E as [L U];apply Z.leb_le in L;apply Z.ltb_lt in U;lia. Qed.
Lemma overlay_byte m a n w i k : (i<n)%nat -> 0<=k<8 ->
 overlay m a n w (a+8*Z.of_nat i+k)=word_byte (w i) k.
Proof.
 intros I K;unfold overlay;replace (a+8*Z.of_nat i+k-a) with (k+Z.of_nat i*8) by ring.
 assert (((0<=?k+Z.of_nat i*8)&&(k+Z.of_nat i*8<?8*Z.of_nat n))%bool=true)
  as E by (apply andb_true_iff;split;[apply Z.leb_le|apply Z.ltb_lt];lia).
 rewrite E,Z.div_add,Z.mod_add,Z.div_small,Z.mod_small by lia.
 now rewrite Z.add_0_l,Nat2Z.id.
Qed.
Lemma overlay_bytes m a n w : byte_memory m -> byte_memory (overlay m a n w).
Proof. intros M x;unfold overlay;destruct (_ && _)%bool;[apply word_byte_bound|apply M]. Qed.

(* Arbitrary concrete child entries may realize the two live buffers.
   A witness only identifies input bytes, entry registers and the return
   slot. It never asserts the child's arithmetic result. *)
Record views slide pt base e w t (m:bytes) := {
 point_view : agrees 160 (buffer_words m pt) w;
 staged_view : agrees 440 (buffer_words m base) t;
 return_view : read_word m (base-8)=slide+continuation e
}.
Definition direct e := match e with DoubleFour | Cached _ _ _ | Ladder _=>True|_=>False end.
Definition native_call slide pt base e w t v :=
 exists rs vs flags m out, views slide pt base e w t m /\
 let ci:=CPU (child_regs pt base e rs) vs flags m in
 well_formed ci /\ child_run slide base e ci (slide+continuation e) out /\ v=buffer_words (mem out) pt.
Definition native_action slide pt base pc pad s e (b z:buffers) :=
 match e with
 | Stage n=>z=(fst b,staged pc pad s n)
 | SeedXYZ=>exists initial,z=(seed_buffer (snd b) initial,snd b)
 | _=>snd z=snd b /\ native_call slide pt base e (fst b) (snd b) (fst z) end.
Fixpoint native_runs slide pt base pc pad s ops b z := match ops with
 | nil=>b=z | e::rest=>exists m,native_action slide pt base pc pad s e b m /\
 native_runs slide pt base pc pad s rest m z end.

Lemma slice_eq t u row n : agrees 440 t u -> (8*row+n<=440)%nat ->
 agrees n (slice t row) (slice u row).
Proof. intros E N i I;unfold slice;apply E;lia. Qed.
Lemma cache_eq f w v : agrees (if f:bool then 120 else 160) w v -> cache_bounds f w -> cache_bounds f v.
Proof. intros E H i j I J;unfold cell;rewrite <-E by (destruct f;lia);apply H;assumption. Qed.
Lemma strict_eq w v : agrees 160 w v -> strict w -> strict v.
Proof. intros E H c j C J i I;unfold cell;rewrite <-E by lia;apply(H c j C J i I). Qed.
Lemma loose_eq w v : agrees 160 w v -> loose_xyz w -> loose_xyz v.
Proof. intros E H c j C J;eapply loose_ext;[|exact (H c j C J)];intros i I;unfold cell;apply E;lia. Qed.
Lemma agrees_sym n w v : agrees n w v -> agrees n v w.
Proof. intros H i I;symmetry;apply H,I. Qed.

Lemma transport_pre e w t p b : agrees 160 p w -> agrees 440 b t -> pre e w t -> pre e p b.
Proof.
 intros P B H;apply agrees_sym in P;apply agrees_sym in B.
 destruct e as [| | |f a row|f];try contradiction.
 - eapply loose_eq;eauto.
 - destruct H as [W [C Len]];split;[eapply strict_eq;eauto|];split;[|exact Len].
   eapply cache_eq;[apply slice_eq;[exact B|destruct a;cbn [footprint] in Len;lia]|exact C].
 - destruct H as [W [O [A E]]];split;[eapply loose_eq;eauto|];split;[|split];
   [eapply cache_eq;[|exact O]|eapply cache_eq;[|exact A]|eapply cache_eq;[|exact E]];apply slice_eq;try exact B;cbn;lia.
Qed.
Lemma transport_post e w t p b v : agrees 160 p w -> agrees 440 b t -> pre e w t ->
 post e p b v -> post e w t v.
Proof.
 intros P B Pre H;destruct e as [| | |f a row|f];try contradiction.
 - eapply Double4Spec.spec_ext;[apply agrees_sym,P|intros;reflexivity|exact H].
 - destruct Pre as [_ [_ Len]]. eapply CachedAddSpec.spec_ext;[apply agrees_sym,P| |intros;reflexivity|exact H].
   apply agrees_sym,slice_eq;[exact B|destruct a;cbn [footprint] in Len;lia].
 - destruct H as [Strict [V T]];split;[exact Strict|split;[|exact T]].
   intros j J;specialize(V j J);cbv beta in V;rewrite (point_values_ext _ _ _ P J) in V.
   assert (E:forall f row,(8*row+(if f:bool then 120 else 160)<=440)%nat ->
    cache_values f (slice b row) j=cache_values f (slice t row) j).
   { intros;apply cache_values_ext;[apply slice_eq;assumption|exact J]. }
   rewrite !E in V by (cbn;lia);exact V.
Qed.

Lemma native_sound slide pt base e w t v : arena slide pt base -> pre e w t ->
 native_call slide pt base e w t v -> post e w t v.
Proof.
 intros Arena P [rs [vs [fl [m [out [[PV BV Ret] [WF [Run ->]]]]]]]].
 destruct(child_correct slide pt base e rs vs fl m Arena WF Ret (transport_pre _ _ _ _ _ PV BV P))
 as [o [R [Spec U]]];destruct (U _ _ Run) as [_ ->];eapply transport_post;eassumption.
Qed.

Definition witness_mem slide base e t :=
 overlay (overlay (fun _=>0) (base-8) 1 (fun _=>slide+continuation e)) base 440 t.
Lemma native_exists slide pt base e w t :
 arena slide pt base -> pre e w t -> words 160 w -> words 440 t -> word64(slide+continuation e) ->
 exists v,native_call slide pt base e w t v /\ post e w t v /\ words 160 v.
Proof.
 intros Arena P W T IP;pose proof (ladder_placement _ _ _ Arena) as Place.
 destruct Place as [_ _ PA BA SF PF BF PS BS BP Code].
 set (m:=overlay (witness_mem slide base e t) pt 160 w).
 assert (B:byte_memory m) by (repeat apply overlay_bytes;unfold witness_mem;repeat apply overlay_bytes;unfold byte_memory;lia).
 assert (PV:agrees 160 (buffer_words m pt) w).
 { intros i I;apply read_word_exact;[apply W,I|intros;apply overlay_byte;assumption]. }
 assert (BV:agrees 440 (buffer_words m base) t).
 { intros i I;apply read_word_exact;[apply T,I|intros;unfold m;rewrite overlay_out by (unfold disjoint in BP;lia);apply overlay_byte;assumption]. }
 assert (Ret:read_word m (base-8)=slide+continuation e).
 { apply read_word_exact;[exact IP|]. intros k K;unfold m,witness_mem.
   rewrite overlay_out by (unfold disjoint,fits64 in *;lia). rewrite overlay_out by lia.
   replace (base-8+k) with ((base-8)+8*Z.of_nat 0+k) by ring;apply (overlay_byte (fun _=>0) (base-8) 1 (fun _=>slide+continuation e) 0 k);lia. }
 assert (WF:well_formed (CPU (child_regs pt base e (fun _=>0)) (fun _ _=>0) None m)).
 { split;[|split;[intros;change (0<=0<2^64);lia|exact B]].
   unfold child_regs;cbn [regs];destruct e as [| | |f a row|f];try contradiction;
   repeat apply put_words;unfold bits,CachedAddABI.flag_word,word64,fits64 in *;
   try (intros;lia);try (destruct f;lia);try (destruct a;lia).
   destruct P as [_ [_ Len]];destruct a;cbn [footprint] in Len;lia. }
 destruct(child_correct slide pt base e _ _ _ _ Arena WF Ret (transport_pre _ _ _ _ _ PV BV P))
   as [out [Run [Spec U]]].
 exists (buffer_words (mem out) pt);split.
 - exists (fun _=>0),(fun _ _=>0),None,m,out;split;[constructor;assumption|auto].
 - pose proof(transport_post _ _ _ _ _ _ PV BV P Spec) as Post;split;[exact Post|].
   assert (Strict:strict (buffer_words (mem out) pt)).
   { destruct e;try contradiction.
     - intros c j C J;apply (proj1(Post P j c J C)).
     - destruct P as [S [C _]];intros c j K J;apply (proj1(proj2 Post (conj (strict_split _ S) C) j c J K)).
     - apply Post. }
   intros i I;set (row:=(i/8)%nat);set (j:=(i mod 8)%nat).
   assert (J:(j<8)%nat) by (apply Nat.mod_upper_bound;lia).
   assert (R:(row<20)%nat) by (apply Nat.div_lt_upper_bound;lia).
   pose proof(strict_split _ Strict row j R J) as H;unfold cell in H.
   replace (row*8+j)%nat with i in H by (unfold row,j;pose proof(Nat.div_mod i 8 ltac:(lia));lia).
   unfold word64;lia.
Qed.
