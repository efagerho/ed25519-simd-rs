From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.ByteMemory.
From Curve25519 Require Import Radix51 group.Affine.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Import Program Operands Execution Native Composition.
Import ListNotations. Local Open Scope Z_scope.

Lemma strict_words w : strict w -> words 160 w.
Proof.
 intros S i I;pose proof(Nat.div_mod i 8 ltac:(lia)) as D;
 pose proof(Nat.mod_upper_bound i 8 ltac:(lia)) as J.
 pose proof(strict_split _ S (i/8)%nat (i mod 8)%nat ltac:(change (i/8<20)%nat;apply Nat.div_lt_upper_bound;lia) J) as H.
 unfold cell in H;replace (i/8*8+i mod 8)%nat with i in H by lia;unfold word64;lia.
Qed.
Lemma seed_words t r : cache_bounds false (slice t 0) -> words 160 (seed_buffer t r).
Proof.
 intros B i I;set (j:=(i mod 8)%nat);set (row:=(i/8)%nat);set (c:=(row/5)%nat);set (k:=(row mod 5)%nat).
 assert (J:(j<8)%nat) by (apply Nat.mod_upper_bound;lia).
 assert (K:(k<5)%nat) by (apply Nat.mod_upper_bound;lia).
 pose proof(Nat.div_mod i 8 ltac:(lia));pose proof(Nat.div_mod row 5 ltac:(lia)).
 assert (R:(5*c+k=row)%nat) by (unfold c,k;lia).
 assert (U:(row<20)%nat) by (unfold row;apply Nat.div_lt_upper_bound;lia).
 assert (C:(c<=3)%nat) by (unfold c;lia).
 change (word64(Seed.out (Seed.execute (fun a=>cell t a j) (r j)) row)).
 rewrite <-R;destruct (Nat.eq_dec c 3) as [->|N].
 - rewrite Seed.zero_t by lia;unfold word64;lia.
 - rewrite Seed.routed by lia.
   assert (Bounds:Seed.bounded (fun a=>cell t a j)) by (intros a Bound;apply B;assumption).
   pose proof(proj1(Seed.seed_bound _ c Bounds) k K) as V.
   unfold loose_bound,split,word64 in *;destruct Nat.eqb in V;lia.
Qed.
Definition post_strict e w t v : pre e w t -> post e w t v -> strict v.
Proof.
 destruct e;try contradiction.
 - intros B D c j C J;apply (proj1(D B j c J C)).
 - intros [B [C _]] [_ D] i j I J;apply (proj1(D (conj (split_cached_point _ (strict_split _ B)) C) j i J I)).
 - intros _ [B _];exact B.
Qed.

Section Paths.
Variables (slide pt base pc pad:Z) (s:cpu) (B:point) (A:nat->point).
Hypotheses (Arena:arena slide pt base) (IPs:forall e,direct e -> word64(slide+continuation e))
 (Inputs:valid_inputs pc pad s) (Tables:valid_tables s B A).
Local Notation act := (native_action slide pt base pc pad s).
Fixpoint safe ops (b:buffers) : Prop := match ops with
 | nil=>True | e::rest=>(exists m,act e b m) /\
 forall m,act e b m -> action pc pad s e b m /\ safe rest m end.
Lemma safe_exec ops b : safe ops b ->
 (exists z,native_runs slide pt base pc pad s ops b z) /\
 forall z,native_runs slide pt base pc pad s ops b z -> executes pc pad s ops b z.
Proof.
 revert b;induction ops as [|e rest IH];intros b H;[split;[exists b;reflexivity|auto]|].
 destruct H as [[m M] All];split.
 - destruct(IH m (proj2(All m M))) as [[z Run] _];exists z,m;auto.
 - intros z [a [E Run]];exists a;destruct(All a E) as [AE S];split;[exact AE|apply (proj2(IH a S));exact Run].
Qed.
Lemma stage_next n rest w t : (safe rest (w,staged pc pad s n)) ->
 safe (Stage n::rest) (w,t).
Proof. intro K;split;[eexists;reflexivity|intros m ->;split;[constructor|exact K]]. Qed.
Lemma seed_next rest w t : (forall r,safe rest (seed_buffer t r,t)) ->
 safe (SeedXYZ::rest) (w,t).
Proof. intro K;split;[exists (seed_buffer t (fun _=>Seed.Lane 0 (fun _=>0) (fun _=>0)),t);
   eexists;reflexivity|intros m [r ->];split;[constructor|apply K]]. Qed.
Lemma native_next e rest w t : direct e -> words 160 w -> words 440 t -> pre e w t ->
 (forall v,strict v -> safe rest (v,t)) -> safe (e::rest) (w,t).
Proof.
 intros D W T P K;destruct(native_exists _ _ _ _ _ _ Arena P W T (IPs e D)) as [v [Call _]].
 assert (N: forall z, act e (w,t) z <-> snd z=t /\ native_call slide pt base e w t (fst z)).
 { destruct e;contradiction || reflexivity. }
 split;[exists(v,t);apply N;auto|].
 intros [u b] H;apply N in H;cbn [fst snd] in H;destruct H as [-> H].
 pose proof(native_sound _ _ _ _ _ _ _ Arena P H) as Post.
 split;[destruct e;try contradiction;constructor;exact Post|apply K;eapply post_strict;eassumption].
Qed.
Lemma staged_words n : (n<32)%nat -> words 440 (staged pc pad s n).
Proof.
 intro N;destruct Inputs as [W P];specialize(P n N).
 pose proof(SA.stage_correct _ SO.assembled_stage_round_correct _ _ P (entry_wf _ _ _ _ W P)) as H.
 unfold staged;cbv zeta in H;destruct(S.run pc (entry_for pad s n)) as [ip out].
 destruct H as [_ [_ [_ [_ [_ [_ [_ [M _]]]]]]]];intros i I;apply read_word_bound,M.
Qed.
Local Notation operand := (operand_correct pc pad s B A).
Lemma tail_safe n full w t : (n<=31)%nat -> strict w -> safe (tail n full) (w,t).
Proof.
 revert w t;induction n as [|n IH];intros w t N W;[exact I|].
 rewrite tail_cons;apply stage_next,native_next;[exact I|now apply strict_words|apply staged_words;lia| |].
 - split;[apply strict_loose,W|];split;[apply(operand n S.Odd Inputs Tables ltac:(lia))|];
   split;[apply(operand n S.Base Inputs Tables ltac:(lia))|apply(operand n S.Even Inputs Tables ltac:(lia))].
 - intros;apply IH;auto;lia.
Qed.
Theorem schedule_safe full w t : safe (schedule full) (w,t).
Proof.
 apply stage_next,seed_next;intro r.
 pose proof(operand 31%nat S.Odd Inputs Tables ltac:(lia)) as [OB OR].
 pose proof(operand 31%nat S.Base Inputs Tables ltac:(lia)) as [BB BR].
 pose proof(operand 31%nat S.Even Inputs Tables ltac:(lia)) as [EB ER].
 pose proof (staged_words 31 ltac:(lia)) as T.
 apply native_next;[exact I|now apply seed_words|exact T|apply (proj1(seeded _ r _ OB OR))|].
 intros v D;apply native_next;[exact I|now apply strict_words|exact T|split;[exact D|split;[exact BB|cbn;lia]]|].
 intros u F;apply native_next;[exact I|now apply strict_words|exact T|split;[exact F|split;[exact EB|cbn;lia]]|].
 intros;apply tail_safe;auto;lia.
Qed.
End Paths.
