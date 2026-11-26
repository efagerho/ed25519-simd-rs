From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordBounds execution.WordSemantics execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare DecoderPower DecoderResume.
From Ed25519Simd.Decode Require DecoderKernel.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderProduct.
Import ListNotations. Local Open Scope Z_scope.

Definition power_offset (sig:bool):=if sig then 320 else 0.
Definition return_offset (sig:bool):=if sig then 222 else 190.
Definition first_call:list line := [(166,2%nat,Jump 8);(176,3%nat,CopyG 7 3);(179,3%nat,CopyG 6 4);
 (182,3%nat,Copy32 9 13);(185,5%nat,CallRelative (901-190))].
Lemma first_bytes : linked text first_call.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition enter bias:=segment (base bias) text 9.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition entry (sig:bool) pol bias e p:=
 let st:=link_slot pol e in let s:=machine p in
 ip p=base bias+901 /\ accounted e (writable e) p /\ well_formed s /\
 regs s 4%nat=st /\ regs s 7%nat=point e sig /\ regs s 6%nat=st+8+power_offset sig /\
 read_word (mem s) st=base bias+return_offset sig /\ decoder_registers pol e s /\
 (forall j,(j<8)%nat -> Z.testbit (regs s 9%nat) (Z.of_nat j)=Z.testbit (original_encoding sig e j) 255) /\
 forall i j,(i<4)%nat -> vectors s j (28+i)%nat=DecoderFrame.constant i.

Theorem from_power pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 DecoderResume.ready pol bias e p -> exists q,enter bias p=Some q /\ entry false pol bias e q /\
 preserved (fun x=>~span (link_slot pol e) 8 x) (mem(machine p)) (mem(machine q)) /\
 forall j,(j<8)%nat -> Z.testbit (regs(machine q) 14%nat) (Z.of_nat j)=Z.testbit (original_encoding true e j) 255.
Proof.
 intros P Image [PC [Acc [W [SP [[BX [BP Count]] [Key Sig]]]]]].
 set (s:=machine p) in *;set (o:=base bias) in *;set (st:=link_slot pol e) in *.
 destruct(DecoderFrame.load_constants true o s (LinkedRun.carry p)) as [v [Run [Regs [Memory Values]]]].
 pose proof(depth pol e) as Deep;fold st in Deep;destruct(Return.stack_ok _ P) as [[Lo Hi] _].
 assert (Push:word(regs v 4%nat-8)=st) by (rewrite Regs,SP;replace (st+8-8) with st by ring;apply word_fits;unfold word64;lia).
 assert (Fits:word64(o+190)) by exact (DecoderProduct.address_fits pol bias e Image DecoderKernel.Carry 190 ltac:(vm_compute;split;discriminate || reflexivity)).
 set (args:=set (set (set v 7 (regs v 3%nat)) 6 (regs v 4%nat)) 9 (regs v 13%nat mod 2^32)).
 set (child:=push args (o+190));set (w:=qword (word(o+185)) st (o+190)).
 assert (Jump:run 5 (ScalarBytes.fetch o text) (State (Running 166) v (LinkedRun.carry p))=
   Some(State (Running 901) child (LinkedRun.carry p),[w])).
 { apply (checked _ _ _ first_bytes);cbn [first_call follow step loc cpu_state cf option_map app];
   cbn [set set_regs regs put Nat.eqb];rewrite Push.
   replace (o+(185+Z.of_nat 5+(901-190))) with (o+901) by ring.
   rewrite (word_fits (o+901)) by exact (DecoderProduct.address_fits pol bias e Image DecoderKernel.Carry 901 ltac:(vm_compute;split;discriminate || reflexivity)).
   replace (o+901-o) with 901 by ring;reflexivity. }
 assert (Safe:confined (writable e) [w]) by
   (constructor;[intros x X;change (st<=x<st+8) in X;left;unfold span;lia|constructor]).
 destruct(mapped_now _ _ _ Image _ _ _ Acc (decode_in pol)) as [Map Sep].
 pose proof(run_append _ 4 _ _ _ Run 5 _ _ Jump) as All.
 destruct(at_segment _ _ _ o text 9 126 _ _ Acc PC Map Sep All Safe) as [Next Paid].
 assert (WF:well_formed child) by exact (segment_wf _ _ _ _ _ W Next).
 assert (M:mem child=store_word (mem s) st (o+190)).
 { unfold child,args;cbn [push push_words with_words set set_regs regs mem put Nat.eqb];now rewrite Push,Memory. }
 assert (G:regs child=put (put (put (put (regs s) 7 (regs s 3%nat)) 6 (regs s 4%nat)) 9 (regs s 13%nat mod 2^32)) 4 st).
 { unfold child,args;cbn [push push_words with_words set set_regs regs mem put Nat.eqb];now rewrite Push,Regs. }
 destruct(mapped_now _ _ _ Image _ _ _ Acc (helper_in pol)) as [Helper _].
 pose proof(proj1(symbols _ _ _ _ Image _ _ (helper_in pol))) as LiteralRange.
 eexists;split;[exact Next|split].
 2:{ split.
     2:{ intros j J;change (Z.testbit (regs child 14%nat) (Z.of_nat j)=Z.testbit (original_encoding true e j) 255);rewrite G;apply Sig,J. }
     intros x X;change (mem child x=mem s x);rewrite M;apply write_outside,X. }
 unfold entry;cbn [LinkedRun.finish ip machine absolute cpu_state loc];fold o st.
 split;[reflexivity|split;[exact Paid|split;[exact WF|]]].
 rewrite G;cbn [put Nat.eqb power_offset return_offset].
 split;[reflexivity|split;[exact BX|split;[lia|split]]].
 - rewrite M;apply read_word_exact;[exact Fits|intros k K;unfold store_word;rewrite write_at by lia;reflexivity].
 - split;[unfold decoder_registers;rewrite G;exact (conj BX (conj BP Count))|split].
   + intros j J;rewrite Z.mod_pow2_bits_low by lia;apply Key,J.
   + intros i j I;change (vectors v j (28+i)%nat=DecoderFrame.constant i);rewrite Values by exact I.
     apply DecoderFrame.mapped_value;[exact I|exact Helper|].
     destruct(DecoderFrame.offsets i I) as [L H];destruct LiteralRange;
       unfold word64,DecoderFrame.at_literal,DecoderFrame.field_offset,DecoderFrame.helper in *;lia.
Qed.
End Iteration.
