From Coq Require Import List ZArith Lia Bool.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.QwordBlock execution.MappedFetch memory.ByteMemory memory.FlatMemory.
From Machine Require execution.PredicateBlock execution.MaskedWords execution.MaskTransfer.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Limbs.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterCarry RootMasks.
Import ListNotations. Local Open Scope Z_scope.

Definition start phase:=FilterCarry.offset phase+5.
Definition low_literal:=DecoderFrame.origin+0xb88-FilterLoad.site.
Definition ops:=[RootMasks.mask1;RootMasks.low 1 low_literal].
Definition fragment phase:=firstn 16 (skipn (Z.to_nat(start phase+18)) FilterLoad.text).
Lemma image phase: InstructionRoute.linked FilterLoad.text (route (start phase) RootMasks.conjunction) /\
 MaskedWords.assemble (start phase+18) ops=Some(fragment phase) /\ length(fragment phase)=16%nat.
Proof. destruct phase;repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias p bank:=let o:=bias+FilterLoad.site in bind (segment o FilterLoad.text 3 p) (fun q=>PredicateBlock.execute o ops q bank).
Record result phase bias e p q k:Prop:=Result {
 pc:ip q=bias+FilterLoad.site+(start phase+34); writes:accounted e (writable e) q; words:well_formed(machine q);
 registers:regs(machine q)=regs(machine p); memory_after:mem(machine q)=mem(machine p); history:log q=log p;
 high_regs:forall j r,r<>10%nat -> r<>11%nat -> vectors(machine q) j r=vectors(machine p) j r;
 equal_zero:forall j,k 1%nat j=((j<?8)%nat && Limbs.high_test (vectors(machine p) j) 0)%bool
}.

Theorem checked phase bias e p bank : loaded Dalek bias (mem e) (writable e) -> ip p=bias+FilterLoad.site+start phase ->
 accounted e (writable e) p -> well_formed(machine p) -> (forall j,vectors(machine p) j 29%nat=radix-1) ->
 exists q k,execute bias p bank=Some(q,k) /\ result phase bias e p q k.
Proof.
 intros I PC Acc W C;destruct(image phase) as [And [Enc Len]];set (o:=bias+FilterLoad.site) in *;set (s:=machine p) in *.
 set (off:=start phase) in *;assert (Off:off=265 \/ off=483) by (destruct phase;[right|left];reflexivity).
 destruct(QwordBlock.execute o _ _ _ s (LinkedRun.carry p) And) as [v [Run [G [M [F Vec]]]]].
 replace (QwordBlock.after off RootMasks.conjunction) with (off+18) in Run by (destruct Off as [O|O];rewrite O;reflexivity).
 destruct(mapped_now _ _ _ I _ _ _ Acc StrictFilterCall.in_filter) as [Map Sep].
 destruct(at_segment _ _ p o FilterLoad.text 3 off _ _ Acc PC Map Sep Run (Forall_nil _)) as [First Paid].
 set (mid:=LinkedRun.finish o p (State(Running(off+18)) v (LinkedRun.carry p),[])) in *.
 assert (View:mapped (mem(machine mid)) (ip mid) (fragment phase)).
 { change (mapped (mem v) (o+(off+18)) (fragment phase));rewrite M;replace (off+18) with (Z.of_nat(Z.to_nat(off+18))) at 1 by lia.
   apply MaskTransfer.subimage with (text:=FilterLoad.text);[exact Map|rewrite Len;change (length FilterLoad.text) with 551%nat;lia|now rewrite Len]. }
 set (k:=RootMasks.cmp o v (RootMasks.gate o v bank) 1 low_literal).
 pose proof(PredicateBlock.mapped_block o (off+18) ops mid bank _ k eq_refl Enc View eq_refl) as Pred.
 assert (Stop:word(ip mid+Z.of_nat(length(fragment phase)))=o+(off+34)).
 { change (word(o+(off+18)+Z.of_nat(length(fragment phase)))=o+(off+34));rewrite Len;replace (o+(off+18)+Z.of_nat 16) with (o+(off+34)) by ring.
   apply word_fits;destruct(proj1(symbols _ _ _ _ I _ _ StrictFilterCall.in_filter)) as [L H];change (0<=o) in L;change (o+551<=2^64) in H;unfold word64;lia. }
 assert (Other:forall j r,r<>10%nat -> r<>11%nat -> vectors v j r=vectors s j r).
 { intros j r A B;rewrite Vec;cbn [RootMasks.conjunction map lane lane_step bits];unfold put;rewrite !(proj2(Nat.eqb_neq 10 r) ltac:(lia)),(proj2(Nat.eqb_neq 11 r) ltac:(lia));reflexivity. }
 do 2 eexists;split;[unfold execute;fold o;rewrite First;exact Pred|constructor];[exact Stop|exact Paid|exact (segment_wf _ _ _ _ _ W First)|exact G|exact M|apply app_nil_r|exact Other|].
 assert (Lit:read_word (mem v) (word(o+low_literal))=radix-19).
 { rewrite M;replace (o+low_literal) with (bias+DecoderFrame.origin+0xb88) by (unfold o,low_literal;ring).
   destruct(mapped_now _ _ _ I _ _ _ Acc (BatchDecode.decode_in Dalek)) as [D _].
   apply NativeScale.read_literal with (bs:=DecoderFrame.code);[exact D|apply (proj1(symbols _ _ _ _ I _ _ (BatchDecode.decode_in Dalek)))|
      lia|change (0xb88+8<=2984);lia|vm_compute;reflexivity]. }
 intro j;unfold k,RootMasks.cmp,RootMasks.low;rewrite PredicateBlock.compare;cbn [MaskedWords.holds PredicateBlock.operand Nat.eqb orb].
 unfold RootMasks.gate,RootMasks.mask1;rewrite PredicateBlock.compare;cbn [MaskedWords.holds PredicateBlock.operand Nat.eqb orb].
 rewrite Lit,(Other j 29%nat ltac:(discriminate) ltac:(discriminate)),C,(Other j 0%nat ltac:(discriminate) ltac:(discriminate)).
 assert (V:vectors v j 10%nat=RootMasks.high (vectors s j)) by (rewrite Vec;reflexivity).
 rewrite V;unfold RootMasks.high,Limbs.high_test;rewrite Z.add_0_r;destruct(j<?8)%nat;cbn;now rewrite ?andb_true_r.
Qed.
