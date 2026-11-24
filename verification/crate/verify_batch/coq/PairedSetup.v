From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory
 memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare SetupTail.
From Ed25519Simd.VerifyBatch Require DecoderProduct DecoderKernel DecoderFrame PrepareCopies.
Import ListNotations. Local Open Scope Z_scope.

Definition selector:list line := [(73,3%nat,Copy32 13 0);(76,4%nat,Compare32 12 2);
 (80,2%nat,Branch Unequal (168-82));(82,7%nat,LeaG 7 (Address 3 None 1280));
 (89,7%nat,Add64 6 256);(96,5%nat,CallRelative (244-101))].
Lemma selector_bytes : linked text selector.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition next_input bias:=segment (base bias) text 6.

Lemma switch pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 finished false pol bias e p -> exists q,next_input bias p=Some q /\ setup true pol bias e q /\
 preserved (fun x=>~span (link_slot pol e) 8 x) (mem(machine p)) (mem(machine q)).
Proof.
 intros P Image [PC [A [SP [DI [Raw [Env C]]]]]].
 destruct Env as [BX BP SI N Back Data Signs].
 set (o:=base bias) in *;set (slot:=link_slot pol e) in *;set (s:=machine p) in *.
 destruct(scratch_ok _ P) as [[L H] _];destruct(Return.stack_ok _ P) as [[SL SH] _].
 pose proof(depth pol e) as Depth;fold slot in Depth.
 pose proof(caller_above pol e) as [Above [Below Deep]];fold slot in Above.
 change (regs s 6%nat=scratch e+0) in SI;rewrite Z.add_0_r in SI.
 assert (NewPoint:word(regs s 3%nat+0+1280)=point e true).
 { rewrite BX;unfold point,point_offset;rewrite word_fits by (unfold word64;lia);ring. }
 assert (Arg:word(word(regs s 6%nat)+word 256)=source e true).
 { rewrite SI,(word_fits (scratch e) ltac:(unfold word64;lia));change (word(scratch e+256)=scratch e+256);apply word_fits;unfold word64;lia. }
 assert (Push:word(regs s 4%nat-8)=slot) by (rewrite SP;replace (slot+8-8) with slot by ring;apply word_fits;unfold word64;lia).
 assert (Target:word(o+244)=o+244) by (apply word_fits;exact (DecoderProduct.address_fits pol bias e Image DecoderKernel.Carry 244 ltac:(vm_compute;split;discriminate || reflexivity))).
 set (signed:=set s 13 (regs s 0%nat mod 2^32)).
 set (pointed:=set (with_zf signed true) 7 (point e true)).
 set (ready:=with_zf (set pointed 6 (source e true)) (source e true=?0)).
 set (child:=push ready (o+101)).
 set (w:=qword (word(o+96)) slot (o+101)).
 assert (R:run 6 (ScalarBytes.fetch o text) (State (Running 73) s (carry p))=
   Some(State (Running 244) child (Some (2^64<=?word(regs s 6%nat)+word 256)),[w])).
 { apply (checked _ _ _ selector_bytes);unfold selector;simpl follow;
   cbn [step cpu_state cf loc eval_condition option_map app effective set set_regs with_zf regs put Nat.eqb];
   rewrite N;change (2 mod 2^32) with 2;
   cbn [Z.eqb negb];rewrite NewPoint,Arg,Push,Target;
   replace (o+244-o) with 244 by ring;reflexivity. }
 assert (Safe:confined (writable e) [w]) by
   (constructor;[intros x X;change (slot<=x<slot+8) in X;left;unfold span;lia|constructor]).
 destruct(mapped_now _ _ _ Image _ _ _ A (decode_in pol)) as [Map Away].
 destruct(at_segment _ _ _ o text _ 73 _ _ A PC Map Away R Safe) as [Next Paid].
 assert (Memory:mem child=store_word (mem s) slot (o+101)).
 { unfold child,ready,pointed,signed;cbn [push push_words set set_regs with_zf with_words mem regs put Nat.eqb];now rewrite Push. }
 assert (Regs:regs child=put (put (put (put (regs s) 13 (regs s 0%nat mod 2^32)) 7 (point e true)) 6 (source e true)) 4 slot).
 { unfold child,ready,pointed,signed;cbn [push push_words set set_regs with_zf with_words mem regs put Nat.eqb];now rewrite Push. }
 assert (Ret:read_word (mem child) slot=word(o+101)).
 { assert (Fits:word64(o+101)) by exact (DecoderProduct.address_fits pol bias e Image DecoderKernel.Carry 101 ltac:(vm_compute;split;discriminate || reflexivity)).
   rewrite Memory,word_fits by exact Fits;apply read_word_exact;[exact Fits|intros k K;unfold store_word;rewrite write_at by lia;reflexivity]. }
 assert (Keep:preserved (caller_bytes pol e) (mem s) (mem child)).
 { intros x X;rewrite Memory;apply write_outside;unfold caller_bytes in X;destruct(scratch_stack _ P);unfold disjoint in *;lia. }
 eexists;split;[exact Next|split].
 2:{ intros x X;change (mem child x=mem s x);rewrite Memory;apply write_outside,X. }
 unfold setup;cbn [LinkedRun.finish machine ip loc cpu_state absolute];fold slot o.
 split;[reflexivity|split;[exact Paid|]]. rewrite Regs;cbn [put Nat.eqb].
 split;[reflexivity|split;[lia|split;[exact BX|split;[reflexivity|split;[reflexivity|split;[exact N|split;[exact Ret|]]]]]]].
 split;[rewrite <-Back;apply preserved_read with (outside:=caller_bytes pol e);[exact Keep|intros k K;right;lia]|].
 split;[intros j sig k J K;rewrite Keep;[apply Data;assumption|left;unfold PrepareCopies.dest;destruct sig;lia]|].
 split;[exact C|intros _ j J;unfold key_signs;rewrite Regs;cbn [put Nat.eqb];rewrite Z.mod_pow2_bits_low by lia;exact (proj2(proj2(Raw j J)))].
Qed.

Record chunks:=Chunks { public_key:checkpoints; signature_r:checkpoints }.
Definition observe_pair bias p bank:=bind (observe bias p bank) (fun a=>
 bind (next_input bias (in_decoder a)) (fun next=>option_map (Chunks a) (input_setup bias next (masks a)))).
Definition paired pol bias e r:=post false pol bias e (public_key r) /\ post true pol bias e (signature_r r).

Theorem from_decoder pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> entry pol bias e p -> exists r,observe_pair bias p bank=Some r /\ paired pol bias e r.
Proof.
 intros P I Al Entry;destruct(SetupTail.from_decoder _ _ _ _ bank P I Al Entry) as [a [A Done]].
 destruct(switch _ _ _ _ P I (proj2 Done)) as [next [N [Start _]]].
 destruct(SetupTail.from_setup true _ _ _ _ (masks a) P I Al Start) as [b [B Result]].
 exists (Chunks a b);split;[unfold observe_pair;rewrite A;cbn [bind];rewrite N;cbn [bind];now rewrite B|exact (conj Done Result)].
Qed.
