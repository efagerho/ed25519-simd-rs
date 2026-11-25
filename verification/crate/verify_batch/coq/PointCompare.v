From Coq Require Import List ZArith Lia Bool.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.QwordBlock execution.MappedFetch memory.ByteMemory memory.FlatMemory.
From Machine Require execution.PredicateBlock execution.MaskedWords execution.MaskTransfer.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Limbs.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterCarry RootMasks ScoreSetup.
Import ListNotations. Local Open Scope Z_scope.

Inductive site:=Key (phase:bool) | Signature (y:bool).
Definition origin s:=match s with Key _=>FilterLoad.site | Signature _=>ScoreSetup.callee Dalek end.
Definition text s:=match s with Key _=>FilterLoad.text | Signature _=>ScoreSetup.code Dalek end.
Definition start s:=match s with Key phase=>FilterCarry.offset phase+5 | Signature y=>if y then 351 else 511 end.
Lemma child s:In (origin s,text s) (children Dalek).
Proof. destruct s;[exact StrictFilterCall.in_filter|exact (ScoreSetup.image Dalek)]. Qed.
Definition low_literal phase:=DecoderFrame.origin+0xb88-origin phase.
Definition ops phase:=[RootMasks.mask1;RootMasks.low 1 (low_literal phase)].
Definition fragment phase:=firstn 16 (skipn (Z.to_nat(start phase+18)) (text phase)).
Lemma image phase: InstructionRoute.linked (text phase) (route (start phase) RootMasks.conjunction) /\
 MaskedWords.assemble (start phase+18) (ops phase)=Some(fragment phase) /\ length(fragment phase)=16%nat.
Proof. destruct phase as [[|]|[|]];repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute phase bias p bank:=let o:=bias+origin phase in bind (segment o (text phase) 3 p) (fun q=>PredicateBlock.execute o (ops phase) q bank).
Record result phase bias e p q k:Prop:=Result {
 pc:ip q=bias+origin phase+(start phase+34); writes:accounted e (writable e) q; words:well_formed(machine q);
 registers:regs(machine q)=regs(machine p); memory_after:mem(machine q)=mem(machine p); history:log q=log p;
 high_regs:forall j r,r<>10%nat -> r<>11%nat -> vectors(machine q) j r=vectors(machine p) j r;
 equal_zero:forall j,k 1%nat j=((j<?8)%nat && Limbs.high_test (vectors(machine p) j) 0)%bool
}.

Theorem checked phase bias e p bank : loaded Dalek bias (mem e) (writable e) -> ip p=bias+origin phase+start phase ->
 accounted e (writable e) p -> well_formed(machine p) -> (forall j,vectors(machine p) j 29%nat=radix-1) ->
 exists q k,execute phase bias p bank=Some(q,k) /\ result phase bias e p q k.
Proof.
 intros I PC Acc W C;destruct(image phase) as [And [Enc Len]];set (o:=bias+origin phase) in *;set (s:=machine p) in *.
 set (off:=start phase) in *;assert (Off:0<=off /\ off+34<Z.of_nat(length(text phase))) by (destruct phase as [[|]|[|]];vm_compute;split;discriminate || reflexivity).
 destruct(QwordBlock.execute o _ _ _ s (LinkedRun.carry p) And) as [v [Run [G [M [F Vec]]]]].
 replace (QwordBlock.after off RootMasks.conjunction) with (off+18) in Run by (change (off+18=off+6+6+6);ring).
 destruct(mapped_now _ _ _ I _ _ _ Acc (child phase)) as [Map Sep].
 destruct(at_segment _ _ p o (text phase) 3 off _ _ Acc PC Map Sep Run (Forall_nil _)) as [First Paid].
 set (mid:=LinkedRun.finish o p (State(Running(off+18)) v (LinkedRun.carry p),[])) in *.
 assert (View:mapped (mem(machine mid)) (ip mid) (fragment phase)).
 { change (mapped (mem v) (o+(off+18)) (fragment phase));rewrite M;replace (off+18) with (Z.of_nat(Z.to_nat(off+18))) at 1 by lia.
   apply MaskTransfer.subimage with (text:=text phase);[exact Map|rewrite Len;lia|now rewrite Len]. }
 set (k:=RootMasks.cmp o v (RootMasks.gate o v bank) 1 (low_literal phase)).
 pose proof(PredicateBlock.mapped_block o (off+18) (ops phase) mid bank _ k eq_refl Enc View eq_refl) as Pred.
 assert (Stop:word(ip mid+Z.of_nat(length(fragment phase)))=o+(off+34)).
 { change (word(o+(off+18)+Z.of_nat(length(fragment phase)))=o+(off+34));rewrite Len;replace (o+(off+18)+Z.of_nat 16) with (o+(off+34)) by ring.
   apply word_fits;destruct(proj1(symbols _ _ _ _ I _ _ (child phase))) as [L H];change (0<=o) in L;fold o in L,H;unfold word64;lia. }
 assert (Other:forall j r,r<>10%nat -> r<>11%nat -> vectors v j r=vectors s j r).
 { intros j r A B;rewrite Vec;cbn [RootMasks.conjunction map lane lane_step bits];unfold put;rewrite !(proj2(Nat.eqb_neq 10 r) ltac:(lia)),(proj2(Nat.eqb_neq 11 r) ltac:(lia));reflexivity. }
 do 2 eexists;split;[unfold execute;fold o;rewrite First;exact Pred|constructor];[exact Stop|exact Paid|exact (segment_wf _ _ _ _ _ W First)|exact G|exact M|apply app_nil_r|exact Other|].
 assert (Lit:read_word (mem v) (word(o+low_literal phase))=radix-19).
 { rewrite M;replace (o+low_literal phase) with (bias+DecoderFrame.origin+0xb88) by (unfold o,low_literal;ring).
   destruct(mapped_now _ _ _ I _ _ _ Acc (BatchDecode.decode_in Dalek)) as [D _].
   apply NativeScale.read_literal with (bs:=DecoderFrame.code);[exact D|apply (proj1(symbols _ _ _ _ I _ _ (BatchDecode.decode_in Dalek)))|
      lia|change (0xb88+8<=2984);lia|vm_compute;reflexivity]. }
 intro j;unfold k,RootMasks.cmp,RootMasks.low;rewrite PredicateBlock.compare;cbn [MaskedWords.holds PredicateBlock.operand Nat.eqb orb].
 unfold RootMasks.gate,RootMasks.mask1;rewrite PredicateBlock.compare;cbn [MaskedWords.holds PredicateBlock.operand Nat.eqb orb].
 rewrite Lit,(Other j 29%nat ltac:(discriminate) ltac:(discriminate)),C,(Other j 0%nat ltac:(discriminate) ltac:(discriminate)).
 assert (V:vectors v j 10%nat=RootMasks.high (vectors s j)) by (rewrite Vec;reflexivity).
 rewrite V;unfold RootMasks.high,Limbs.high_test;rewrite Z.add_0_r;destruct(j<?8)%nat;cbn;now rewrite ?andb_true_r.
Qed.
