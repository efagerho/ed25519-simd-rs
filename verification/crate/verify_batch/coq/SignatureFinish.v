From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.InstructionRoute execution.MappedFetch memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderKernel DecoderProduct DecoderPower DecoderFinish RootTest RootCandidate
 Selection SignedRoot ReturnedPoint KeyReturn.
Import ListNotations. Local Open Scope Z_scope.

Definition route:list line:=[(190,4%nat,Compare32 12 2);(194,2%nat,Branch Unequal 32);
 (196,3%nat,Copy32 13 0);(199,7%nat,LeaG 7 (Address 3 None 1280));(206,8%nat,LeaG 6 (Address 4 None 320));
 (214,3%nat,Copy32 9 14);(217,5%nat,CallRelative (901-222))].
Lemma code:linked text route. Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition enter bias:=segment (base bias) text 7.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked pol bias e t : placement e -> loaded pol bias (mem e) (writable e) -> KeyReturn.post pol bias e t ->
 let p:=KeyReturn.returned t in exists q,enter bias p=Some q /\ DecoderFinish.entry true pol bias e q /\
 regs(machine q) 13%nat=regs(machine p) 0%nat /\ preserved (fun x=>~span (link_slot pol e) 8 x) (mem(machine p)) (mem(machine q)).
Proof.
 intros P I K p;pose proof(KeyReturn.native_return _ _ _ _ K) as Out;pose proof(KeyReturn.signed_result _ _ _ _ K) as S.
 pose proof(RootCandidate.selection _ _ _ _ (SignedRoot.raw _ _ _ _ S)) as D;pose proof(Selection.test_result _ _ _ _ D) as T.
 destruct(RootTest.finish_arguments _ _ _ _ T) as [_ [_ [_ [_ [_ [_ [_ [[BX [BP Count]] _]]]]]]]].
 set (s:=machine p) in *;set (st:=link_slot pol e) in *;set (o:=base bias) in *.
 assert (G:forall r,r<>0%nat -> r<>4%nat -> r<>8%nat -> r<>10%nat -> regs s r=regs(machine(SignedRoot.begin(KeyReturn.signed t))) r).
 { intros r Z F B N;rewrite (ReturnedPoint.preserved_regs _ _ _ _ _ _ Out) by assumption;apply (SignedRoot.register _ _ _ _ S);assumption. }
 assert (GB:regs s 3%nat=scratch e+1024) by (rewrite G by discriminate;exact BX).
 assert (GBp:regs s 5%nat=common_top pol e-120) by (rewrite G by discriminate;exact BP).
 assert (N:regs s 12%nat=2) by (rewrite G by discriminate;exact Count).
 assert (Signs:forall j,(j<8)%nat -> Z.testbit (regs s 14%nat) (Z.of_nat j)=Z.testbit (original_encoding true e j) 255)
  by (intros j J;rewrite G by discriminate;exact (RootTest.signature_signs _ _ _ _ T j J)).
 pose proof(ReturnedPoint.stack _ _ _ _ _ _ Out) as SP;change (regs s 4%nat=st+8) in SP.
 destruct(scratch_ok _ P) as [[L H] Al];destruct(Return.stack_ok _ P) as [[Lo Hi] _];pose proof(depth pol e) as Depth;fold st in Depth.
 assert (DI:word(regs s 3%nat+0+1280)=point e true) by (rewrite GB;unfold point,point_offset;rewrite word_fits by (unfold word64;lia);ring).
 assert (SI:word(regs s 4%nat+0+320)=st+8+320) by (rewrite SP;rewrite word_fits by (unfold word64;lia);ring).
 assert (Push:word(regs s 4%nat-8)=st) by (rewrite SP;replace (st+8-8) with st by ring;apply word_fits;unfold word64;lia).
 assert (Dest:word(o+901)=o+901) by (apply word_fits;exact (DecoderProduct.address_fits _ _ _ I DecoderKernel.Carry 901 ltac:(change (0<=901<2984);lia))).
 set (args:=set (set (set (set (with_zf s true) 13 (regs s 0%nat mod 2^32)) 7 (point e true)) 6 (st+8+320)) 9 (regs s 14%nat mod 2^32)).
 set (child:=push args (o+222));set (w:=qword (word(o+217)) st (o+222)).
 assert (R:run 7 (ScalarBytes.fetch o text) (State (Running 190) s (LinkedRun.carry p))=
  Some(State (Running 901) child (Some false),[w])).
 { apply (InstructionRoute.checked _ _ _ code);unfold route;simpl follow;
   cbn [step cpu_state cf loc eval_condition option_map app effective set set_regs with_zf regs put Nat.eqb];
   rewrite N;change (2 mod 2^32) with 2;cbn [Z.eqb negb];rewrite DI,SI,Push,Dest.
   replace (o+901-o) with 901 by ring;reflexivity. }
 assert (Safe:confined (writable e) [w]) by (constructor;[intros x X;change (st<=x<st+8) in X;left;unfold span;lia|constructor]).
 pose proof(ReturnedPoint.writes _ _ _ _ _ _ Out) as Acc;fold p in Acc.
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ p o text 7 190 _ _ Acc (ReturnedPoint.resume _ _ _ _ _ _ Out) Map Sep R Safe) as [Next Paid].
 assert (WM:well_formed child) by exact (segment_wf o text 7 p _ (ReturnedPoint.words _ _ _ _ _ _ Out) Next).
 assert (Mem:mem child=store_word (mem s) st (o+222)) by (unfold child,args;cbn [push push_words with_words set set_regs regs with_zf mem put Nat.eqb];now rewrite Push).
 assert (Reg:regs child=put (put (put (put (put (regs s) 13 (regs s 0%nat mod 2^32)) 7 (point e true)) 6 (st+8+320)) 9 (regs s 14%nat mod 2^32)) 4 st) by
  (unfold child,args;cbn [push push_words with_words set set_regs regs with_zf mem put Nat.eqb];now rewrite Push).
 eexists;split;[exact Next|split].
 - unfold DecoderFinish.entry;cbn [LinkedRun.finish machine ip absolute loc cpu_state];fold st o.
   split;[reflexivity|split;[exact Paid|split;[exact WM|]]].
   rewrite Reg;cbn [put Nat.eqb DecoderFinish.power_offset DecoderFinish.return_offset];split;[reflexivity|split;[reflexivity|split;[reflexivity|split]]].
   + rewrite Mem;apply read_word_exact;[exact (DecoderProduct.address_fits _ _ _ I DecoderKernel.Carry 222 ltac:(change (0<=222<2984);lia))|].
     intros k B;unfold store_word;rewrite write_at by lia;reflexivity.
   + split;[unfold DecoderPower.decoder_registers;rewrite Reg;exact (conj GB (conj GBp N))|split].
     * intros j J;rewrite Z.mod_pow2_bits_low by lia;apply Signs,J.
     * exact (ReturnedPoint.high _ _ _ _ _ _ Out).
 - split.
   + change (regs child 13%nat=regs s 0%nat);rewrite Reg;cbn [put Nat.eqb];apply Z.mod_small;pose proof(KeyReturn.valid_byte _ _ _ _ K) as B;change (0<=regs s 0%nat<256) in B;lia.
   + intros x X;change (mem child x=mem s x);rewrite Mem;apply write_outside,X.
Qed.
End Iteration.
