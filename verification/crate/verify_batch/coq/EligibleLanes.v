From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.PrepareChunk Require CommonBytes Dispatch.
From Curve25519 Require Scalar.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode.
From Ed25519 Require Import Optimized.
From Ed25519Simd.VerifyBatch Require DecoderReturn DecoderEpilogue DecoderSpills KeyReturn PairReturn RootDecision ScalarInputs.
Import ListNotations. Local Open Scope Z_scope.

Definition code:list line := [(142,4%nat,ExtendByte 15 0);(146,3%nat,Shr32 0 8);(149,4%nat,StoreByte 0 (Address 13 None 72));
 (153,3%nat,And32 14 15);(156,3%nat,And32 14 0);(159,2%nat,Branch Equal (258-161))].
Lemma linked_code : linked CommonBytes.symbol_bytes code.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition eligible s a r:=Z.land (Z.land s a) r.
Lemma masked_byte a b : 0<=b<256 -> 0<=Z.land a b<256.
Proof. intro B;rewrite <-(Z.mod_small b (2^8) B),<-Z.land_ones,Z.land_assoc,Z.land_ones by lia;apply Z.mod_pos_bound;lia. Qed.
Definition next mask:=if mask=?0 then 258 else 161.
Definition store_at o ptr rv:=Store (word(o+149)) (ptr+72) 1 (fun _=>rv).

Lemma branch o s c scalar key sig ptr : regs s 0%nat=256*sig+key -> regs s 14%nat=scalar ->
 regs s 13%nat=ptr -> word64(ptr+72) -> 0<=key<256 -> 0<=sig<256 ->
 let mask:=eligible scalar key sig in let w:=store_at o ptr sig in
 exists v,run 6 (ScalarBytes.fetch o CommonBytes.symbol_bytes) (State (Running 142) s c)=
 Some(State (Running (next mask)) v (Some false),[w]) /\ regs v 14%nat=mask /\
 regs v 15%nat=key /\ regs v 0%nat=sig /\ mem v=commit (mem s) w /\
 forall r,r<>0%nat -> r<>14%nat -> r<>15%nat -> regs v r=regs s r.
Proof.
 intros E S P Fit K R mask w.
 assert (Low:(256*sig+key) mod 256=key) by (replace (256*sig+key) with (key+sig*256) by ring;rewrite Z.mod_add by lia;now apply Z.mod_small).
 assert (High:Z.shiftr ((256*sig+key) mod 2^32) 8 mod 2^32=sig).
 { rewrite (Z.mod_small (256*sig+key) (2^32)),Z.shiftr_div_pow2 by lia;change (2^8) with 256.
   replace (256*sig) with (sig*256) by ring;rewrite Z.div_add_l,Z.div_small,Z.add_0_r,Z.mod_small by lia;reflexivity. }
 pose proof(masked_byte scalar key K) as A;pose proof(masked_byte (Z.land scalar key) sig R) as B.
 set (out:=with_zf (set (set (with_words (set (set s 15 key) 0 sig) (regs(set (set s 15 key) 0 sig))
   (commit (mem s) w)) 14 (Z.land scalar key)) 14 mask) (mask=?0)).
 exists out;split.
 - apply (checked _ _ _ linked_code);cbn [code follow step loc cpu_state cf option_map effective eval_condition
    set set_regs with_zf with_words regs flag mem put Nat.eqb app].
   change (8 mod 32) with 8;change (8=?0) with false.
   cbn [follow step loc cpu_state cf option_map effective eval_condition set set_regs with_zf with_words regs flag mem put Nat.eqb app].
   rewrite E,S,P,Low,High,!Z.add_0_r,(word_fits _ Fit),(Z.mod_small sig 256 R).
   rewrite (Z.mod_small (Z.land scalar key) (2^32)),(Z.mod_small (Z.land (Z.land scalar key) sig) (2^32)) by lia.
   fold (eligible scalar key sig);fold mask;unfold next;destruct(mask=?0);reflexivity.
 - unfold out;cbn [with_zf set set_regs with_words regs mem put Nat.eqb].
   repeat split;intros n N A' B';unfold put;rewrite (proj2(Nat.eqb_neq 14 n) ltac:(lia)),(proj2(Nat.eqb_neq 0 n) ltac:(lia)),(proj2(Nat.eqb_neq 15 n) ltac:(lia));reflexivity.
Qed.

Definition execute bias:=segment (bias+PrepareNative.common) CommonBytes.symbol_bytes 6.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition candidate e j:=ScalarInputs.original_scalar e (BatchWindow.row e j)<Scalar.L /\
 RootDecision.decodes false e j /\ RootDecision.decodes true e j.
Record post pol bias e p q:Prop:=Post {
 destination:ip q=bias+PrepareNative.common+next (regs(machine q) 14%nat);
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 mask_byte:0<=regs(machine q) 14%nat<256;
 bit:forall j,(j<8)%nat -> (Z.testbit (regs(machine q) 14%nat) (Z.of_nat j)=true <-> candidate e j);
 live_branch:(regs(machine q) 14%nat<>0 <-> exists j,(j<8)%nat /\ candidate e j);
 stored:log q=log p++[store_at (bias+PrepareNative.common) (Rows.frame e+768) (regs(machine q) 0%nat)];
 memory_after:mem(machine q)=commit (mem(machine p)) (store_at (bias+PrepareNative.common) (Rows.frame e+768) (regs(machine q) 0%nat));
 kept_rbp:regs(machine q) 5%nat=regs(machine p) 5%nat;
 sig_bits:forall j,(j<8)%nat -> (Z.testbit (mem(machine q)(Rows.frame e+840)) (Z.of_nat j)=true <-> RootDecision.decodes true e j);
 key_bits:forall j,(j<8)%nat -> (Z.testbit (regs(machine q) 15%nat) (Z.of_nat j)=true <-> RootDecision.decodes false e j);
 scratch_base:regs(machine q) 3%nat=scratch e;
 identity_address:regs(machine q) 12%nat=regs e 8%nat;
 prepared_address:regs(machine q) 13%nat=Rows.frame e+768;
 stack:regs(machine q) 4%nat=common_top pol e-104
}.

Theorem from_return pol bias e scalar d t : placement e -> loaded pol bias (mem e) (writable e) ->
 ScalarInputs.recoded e (machine scalar) -> caller_values e scalar d -> DecoderReturn.post pol bias e d t ->
 exists q,execute bias (DecoderReturn.returned t)=Some q /\ post pol bias e (DecoderReturn.returned t) q.
Proof.
 intros P Image [Sc Digits] [Ptr [SM [Scratch Fallback]]] D.
 set (p:=DecoderReturn.returned t);set (k:=DecoderReturn.points t);set (o:=bias+PrepareNative.common).
 set (s:=regs(machine scalar) 0%nat) in *.
 set (av:=regs(machine(PairReturn.returned k)) 13%nat);set (rv:=regs(machine(PairReturn.returned k)) 0%nat).
 pose proof(DecoderReturn.decoded _ _ _ _ _ D) as K;fold k in K.
 pose proof(proj1(PairReturn.signature_mask _ _ _ _ K)) as R;fold rv in R.
 assert (A:0<=av<256) by (unfold av;rewrite (PairReturn.key_mask _ _ _ _ K);exact (KeyReturn.valid_byte _ _ _ _ (PairReturn.key_result _ _ _ _ K))).
 assert (G:forall r,In r DecoderSpills.registers -> regs(machine p) r=regs(machine d) r) by exact (DecoderReturn.restores _ _ _ _ _ D).
 assert (Fit:word64(Rows.frame e+768+72)) by
   (destruct(stack_ok _ P) as [[L H] _];unfold Rows.frame,sp,word64 in *;lia).
 destruct(branch o (machine p) (LinkedRun.carry p) s av rv (Rows.frame e+768)
   (DecoderReturn.mask_word _ _ _ _ _ D)
   ltac:(rewrite G by (cbn;tauto);rewrite SM;apply Z.mod_small;lia)
   ltac:(rewrite G by (cbn;tauto);exact Ptr) Fit A R) as [v [Run [M [Key [Sig [Mem Regs]]]]]].
 set (w:=store_at o (Rows.frame e+768) rv) in *.
 assert (Safe:confined (writable e) [w]) by
   (constructor;[intros x X;left;change (Rows.frame e+768+72<=x<Rows.frame e+768+72+1) in X;unfold span,Rows.frame,sp in *;lia|constructor]).
 pose proof(DecoderReturn.writes _ _ _ _ _ D) as Acc;fold p in Acc.
 destruct(mapped_now _ _ _ Image _ _ _ Acc (in_common pol)) as [Map Sep].
 destruct(at_segment _ _ p o CommonBytes.symbol_bytes 6 142 _ _ Acc (DecoderReturn.resumes _ _ _ _ _ D) Map Sep Run Safe) as [End Paid].
 set (q:=LinkedRun.finish o p (State (Running(next(eligible s av rv))) v (Some false),[w])) in *.
 assert (KeyBit:forall j,(j<8)%nat -> (Z.testbit av (Z.of_nat j)=true <-> RootDecision.decodes false e j))
   by exact (PairReturn.key_accepts _ _ _ _ K).
 pose proof(SignatureDecision.bits _ _ _ _ P K) as SigBit;fold rv in SigBit.
 assert (Bits:forall j,(j<8)%nat -> (Z.testbit (eligible s av rv) (Z.of_nat j)=true <-> candidate e j)).
 { intros j J;unfold eligible,candidate;rewrite !Z.land_spec,!andb_true_iff,(KeyBit j J),(SigBit j J),(proj1(Digits j J));tauto. }
 pose proof(masked_byte (Z.land s av) rv R) as B;fold (eligible s av rv) in B.
 exists q;split;[exact End|]. constructor;change (machine q) with v.
 - rewrite M;reflexivity.
 - exact Paid.
 - exact (segment_wf _ _ _ p q (DecoderReturn.words _ _ _ _ _ D) End).
 - now rewrite M.
 - now rewrite M.
 - rewrite M,(Dispatch.flag_nonzero _ B);split;intros [j [J H]];exists j;split;try exact J;apply (Bits j J);exact H.
 - rewrite Sig;reflexivity.
 - now rewrite Sig.
 - apply Regs;discriminate.
 - assert (V:mem v (Rows.frame e+840)=rv).
   { rewrite Mem;unfold w,store_at,commit;cbn [address size payload].
     replace (Rows.frame e+840) with (Rows.frame e+768+72+0) by ring;apply write_at;lia. }
   now rewrite V.
 - now rewrite Key.
 - rewrite Regs by discriminate;rewrite G by (cbn;tauto);exact Scratch.
 - rewrite Regs by discriminate;rewrite G by (cbn;tauto);exact Fallback.
 - rewrite Regs by discriminate;rewrite G by (cbn;tauto);exact Ptr.
 - rewrite Regs by discriminate;exact (DecoderReturn.frame_top _ _ _ _ _ D).
Qed.

Record trace:=Trace { decoded:DecoderReturn.trace; stopped:cursor }.
Definition observe pol bias e d bank:=bind (DecoderReturn.observe pol bias e d bank)
 (fun t=>option_map (Trace t) (execute bias (DecoderReturn.returned t))).
Definition checked_trace pol bias e d t:=
 DecoderReturn.post pol bias e d (decoded t) /\ post pol bias e (DecoderReturn.returned(decoded t)) (stopped t).

Theorem from_decoder pol bias e scalar d bank : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e d -> well_formed(machine d) ->
 ScalarInputs.recoded e (machine scalar) -> caller_values e scalar d ->
 exists t,observe pol bias e d bank=Some t /\ checked_trace pol bias e d t.
Proof.
 intros P I Al E W S C;destruct(DecoderReturn.from_decoder _ _ _ _ bank P I Al E W) as [r [A D]].
 destruct(from_return _ _ _ _ _ _ P I S C D) as [q [B Q]];exists(Trace r q);split;
   [unfold observe;rewrite A;cbn [bind];now rewrite B|exact (conj D Q)].
Qed.

Lemma accepted_candidate pol e j : signature_accepts pol (read_input (mem e) (regs e 7%nat) (BatchWindow.row e j)) ->
 candidate e j.
Proof.
 intro H;destruct(Optimized.accepted_eligible _ _ H) as [S [[r [RY _]] [a [[AY _] _]]]].
 split;[exact S|split];unfold RootDecision.decodes,BatchDecode.original_encoding;[exists (Affine.x a);rewrite <-AY;apply Affine.on_edwards|
  exists (Affine.x r);rewrite <-RY;apply Affine.on_edwards].
Qed.

Corollary zero_rejects pol bias e p q : post pol bias e p q -> regs(machine q) 14%nat=0 ->
 forall j,(j<8)%nat -> (j<BatchWindow.remaining e)%nat -> ~signature_accepts pol (read_input (mem e) (regs e 7%nat) (BatchWindow.first+j)).
Proof.
 intros T Zero j J Live Valid;rewrite <-(BatchWindow.own_row e j Live) in Valid.
 pose proof(proj2(bit _ _ _ _ _ T j J) (accepted_candidate pol e j Valid)) as Bit.
 now rewrite Zero,Z.bits_0 in Bit.
Qed.
End Iteration.

Definition masks t:=FinishTrace.masks (PairReturn.signature (DecoderReturn.points(decoded t))).
