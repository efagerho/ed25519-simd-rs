From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarWords memory.ByteMemory memory.MemoryGeometry memory.FlatMemory.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Import Limbs.
From Ed25519Simd.Decode Require Power Kernels.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode DecoderSave KeySquare
 SetupTail PairedSetup DecoderPower NativeScale SetupValues.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderProduct NativeWords.
Local Open Scope Z_scope.
Local Opaque DecoderProduct.kernel.

Definition half t (signature:bool):=if signature then signature_r (setup_points t) else public_key (setup_points t).
Definition point_bytes e signature:=span (point e signature) 1280.
Definition inputs e t := forall sig,
 fields sig e (after_square (half t sig)) (in_decoder (half t sig)) /\
 preserved (point_bytes e sig) (mem(machine(in_decoder(half t sig)))) (mem(machine(exponent_entry t))).

Theorem from_decoder pol bias e p bank t :
 placement e -> loaded pol bias (mem e) (writable e) -> (bias+DecoderFrame.origin) mod 64=0 ->
 BatchDecode.entry pol bias e p -> well_formed(machine p) -> DecoderPower.observe bias p bank=Some t -> inputs e t.
Proof.
 intros P Image Al E W.
 destruct(BatchDecode.from_decoder pol bias e p P Image E) as [first [A0 KeySetup]].
 destruct(SetupTail.from_setup false pol bias e first bank P Image Al KeySetup) as [key [A1 [KeySq KeyDone]]].
 pose proof(segment_wf _ _ _ _ _ W A0) as W1.
 destruct(setup_fields false _ _ _ P Image _ _ _ Al KeySetup W1 A1) as [Key _].
 destruct(switch _ _ _ _ P Image KeyDone) as [second [A2 [SigSetup KeepKey]]].
 pose proof(segment_wf _ _ _ _ _ (NativeWords.input_words_after _ _ _ _ W1 A1) A2) as W2.
 destruct(SetupTail.from_setup true pol bias e second (masks key) P Image Al SigSetup) as [sig [A3 [SigSq SigDone]]].
 destruct(setup_fields true _ _ _ P Image _ _ _ Al SigSetup W2 A3) as [Sig Rest].
 destruct(DecoderPower.from_setup _ _ _ _ P Image SigDone) as [entry [A4 [_ Call]]].
 unfold DecoderPower.observe,observe_pair,SetupTail.observe;rewrite A0;cbn [bind];rewrite A1;cbn [bind];
 rewrite A2;cbn [bind];rewrite A3;cbn [bind option_map signature_r];rewrite A4;intro Eq;injection Eq as <-.
 assert (Scratch:forall which x,point_bytes e which x ->
   ~span (link_slot pol e) 8 x /\ ~(link_slot pol e-24<=x<link_slot pol e)).
 { intros which x X;pose proof(depth pol e);destruct(scratch_stack _ P);
   unfold point_bytes,span,point,point_offset,disjoint in *;destruct which;lia. }
 intros [|];split;[exact Sig| |exact Key|].
 - intros x X;apply Call,(proj1(Scratch _ _ X)).
 - intros x X;change (mem(machine entry) x=mem(machine(in_decoder key)) x);destruct(Scratch _ _ X) as [Slot Below];rewrite (Call x Slot),(Rest x),(KeepKey x Slot);[reflexivity|].
   split;[exact Below|unfold point_bytes,span,point,point_offset in *;lia].
Qed.

Definition argument e s sig:=buffer_words (mem s) (point e sig+960).
Definition uv y:=let yy:=y*y in let u:=121666*(yy-1) in u*(yy-u).
Lemma limb_word s ptr i j : cell (buffer_words (mem s) ptr) i j=row s ptr j i.
Proof. unfold cell,buffer_words,row;f_equal;lia. Qed.

Theorem certified pol bias e t : DecoderPower.post pol bias e t -> inputs e t ->
 forall sig j,(j<8)%nat ->
 let buf:=argument e (machine(exponent_entry t)) sig in
 (forall i,(i<5)%nat -> 0<=cell buf i j<split) /\
 represents (field_at buf 0 j) (uv (original_encoding sig e j mod 2^255)).
Proof.
 intros [Pair _] Input sig j J buf.
 assert (Square:squared sig pol bias e (after_square (half t sig))).
 { destruct sig;[exact (proj1(proj2 Pair))|exact (proj1(proj1 Pair))]. }
 destruct Square as [_ [_ [_ [_ Values]]]];destruct(Values j J) as [Bounds [YY Pos]].
 set (v:=vectors(machine(after_square(half t sig))) j) in *.
 assert (B:bounded v) by (intros i I;specialize(Bounds i I);change (0<=v i<=radix+2^16) in Bounds;lia).
 destruct(scaled_bounds _ B Pos) as [U V].
 destruct(Power.apply_ok _ Kernels.Multiply _ _ (proj1 DecoderProduct.multiplication)
    (bounded_split _ U) (bounded_split _ V)) as [UV [Rep _]].
 destruct(Input sig) as [Fields Keep].
 assert (Same:forall i,(i<5)%nat -> cell buf i j=product v i).
 { intros i I;unfold buf,argument;rewrite limb_word.
   rewrite (keep_row _ _ (point e sig+960) _ Keep ltac:(intros x X;unfold point_bytes,span;lia) j i J I).
   exact (proj2(proj2(Fields j i J I))). }
 split.
 - intros i I. rewrite (Same i I). specialize(UV i I).
   change (0<=product v i<=radix+2^16) in UV.
   assert (Width:radix+2^16<Radix51.split) by reflexivity.
   split;[exact (proj1 UV)|exact (Z.le_lt_trans (product v i) (radix+2^16) Radix51.split (proj2 UV) Width)].

 - unfold field_at;change (represents (limbs(fun i=>cell buf i j)) (uv (original_encoding sig e j mod 2^255))).
   erewrite limbs_ext by exact Same;eapply ctrans;[exact Rep|].
   destruct(scaled_values v) as [Ueq Veq];set (y:=original_encoding sig e j mod 2^255) in *.
   assert (Num:represents (pack(u_digits v)) (121666*(y*y-1))).
   { eapply ctrans;[exact Ueq|apply ctimes;[apply crefl|apply cminus;[exact YY|apply crefl]]]. }
   apply ctimes;[exact Num|eapply ctrans;[exact Veq|apply cminus;assumption]].
Qed.
