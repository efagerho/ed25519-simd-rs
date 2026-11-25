From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.LinkedRun execution.ScalarBytes execution.MappedFetch execution.InstructionRoute
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.Pow2 Require Pow2ABI Pow2Memory ObjectBytes.
From Ed25519Simd.Decode Require DecoderBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare SetupTail PairedSetup.
From Ed25519Simd.VerifyBatch Require DecoderProduct DecoderKernel DecoderFrame ScalarInputs.
Import ListNotations. Local Open Scope Z_scope.

Definition power bias:=bias+DecoderBytes.pow_pc.
Definition return_pc bias:=base bias+126.
Definition regions pol e (r:nat):=match r with
 | 1%nat=>scratch e+1984 | 2%nat=>scratch e+3264
 | 3%nat=>link_slot pol e+8 | 4%nat=>link_slot pol e-1928 | _=>0 end.
Definition locations pol bias e:=Placement (regions pol e) (power bias) (return_pc bias).
Definition size:=Z.of_nat(length Pow2.ObjectBytes.symbol_bytes).
Lemma power_in pol : In (DecoderBytes.pow_pc,Pow2.ObjectBytes.symbol_bytes) (children pol).
Proof. apply in_or_app;left;do 6 right;left;reflexivity. Qed.
Lemma separate_symbols : DecoderBytes.pow_pc+size<=DecoderFrame.origin+126 \/ DecoderFrame.origin+126<DecoderBytes.pow_pc.
Proof. first [left;vm_compute;discriminate || reflexivity|right;vm_compute;reflexivity]. Qed.
Lemma slot_alignment pol e : link_slot pol e mod 16=8.
Proof.
 unfold link_slot,DecoderFrame.top;set (x:=common_top pol e-112-40).
 replace (x-x mod 64-640-8) with (8+(4*(x/64)-41)*16) by (pose proof(Z.div_mod x 64 ltac:(lia));lia).
 rewrite Z.mod_add by lia;reflexivity.
Qed.

Lemma placement_ok pol bias e : Return.placement e -> LoadedImage.loaded pol bias (mem e) (writable e) ->
 Pow2Memory.valid_placement (locations pol bias e) size.
Proof.
 intros P I;set (st:=link_slot pol e).
 pose proof(depth pol e) as D;fold st in D.
 destruct(stack_ok _ P) as [[SL SH] _];destruct(scratch_ok _ P) as [[L H] _];pose proof(scratch_stack _ P) as Apart.
 unfold Pow2Memory.valid_placement,Pow2Memory.entry_rsp,locations,regions,Pow2ABI.stack,Pow2ABI.output,Pow2ABI.input_a,Pow2ABI.input_b;
  cbn [FlatMemory.origin caller_pc code_base];fold st;
  replace (st-1928+1928) with st by ring;
  pose proof(proj1(symbols _ _ _ _ I _ _ (power_in pol))) as Fit;change (fits64 (power bias) size) in Fit;destruct Fit as [CodeLo CodeHi];
  assert (Back:word64(return_pc bias)) by exact (DecoderProduct.address_fits pol bias e I DecoderKernel.Carry 126 ltac:(vm_compute;split;discriminate || reflexivity));
  assert (Outside:~(power bias<=return_pc bias<power bias+size)) by (unfold power,return_pc,base;pose proof separate_symbols;lia).
 assert (Distinct:forall a n,0<n -> sp e-16384<=a -> a+n<=sp e ->
      disjoint a n (power bias) size).
 { intros a n Len A Z;apply ScalarInputs.apart;[exact Len|vm_compute;reflexivity|intros x X Over];
   apply (immutable _ _ _ _ I x);[left;exists DecoderBytes.pow_pc,Pow2.ObjectBytes.symbol_bytes;split;[apply power_in|exact X]|left;unfold span;lia]. }
 repeat split;try apply slot_alignment;try exact Outside;try apply Distinct;
  unfold fits64,word64,disjoint in *;try lia.
Qed.

Definition bridge:list line := [(101,3%nat,Copy32 14 0);(104,7%nat,LeaG 2 (Address 3 None 2240));
 (111,7%nat,LeaG 6 (Address 3 None 960));(118,3%nat,CopyG 7 4);
 (121,5%nat,CallRelative (DecoderBytes.pow_pc-(DecoderBytes.address+126)))].
Lemma bridge_bytes : linked text bridge.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition enter bias:=segment (base bias) text 5.
Definition decoder_registers pol e s:=
 regs s 3%nat=scratch e+1024 /\ regs s 5%nat=common_top pol e-120 /\ regs s 12%nat=2.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition entry pol bias e p:=let st:=link_slot pol e in
 ip p=power bias /\ accounted e (writable e) p /\
 regs(machine p) 4%nat=st /\ regs(machine p) 7%nat=st+8 /\
 regs(machine p) 6%nat=scratch e+1984 /\ regs(machine p) 2%nat=scratch e+3264 /\
 read_word (mem(machine p)) st=return_pc bias /\
 key_signs e (machine p) /\ (forall j,(j<8)%nat ->
 Z.testbit (regs(machine p) 14%nat) (Z.of_nat j)=Z.testbit (original_encoding true e j) 255) /\
 decoder_registers pol e (machine p).

Theorem from_setup pol bias e p : Return.placement e -> loaded pol bias (mem e) (writable e) ->
 finished true pol bias e p -> exists q,enter bias p=Some q /\ entry pol bias e q /\
 preserved (fun x=>~span (link_slot pol e) 8 x) (mem(machine p)) (mem(machine q)).
Proof.
 intros P I [At [Acc [SP [DI [Raw [Env C]]]]]];destruct Env as [BX BP SI N Back Data Key].
 set (s:=machine p) in *;set (st:=link_slot pol e) in *;set (o:=base bias) in *.
 destruct(scratch_ok _ P) as [[L H] _];destruct(stack_ok _ P) as [[SL SH] _].
 pose proof(depth pol e) as Depth;fold st in Depth.
 assert (A:word(regs s 3%nat+0+960)=scratch e+1984) by (rewrite BX,word_fits by (unfold word64;lia);ring).
 assert (B:word(regs s 3%nat+0+2240)=scratch e+3264) by (rewrite BX,word_fits by (unfold word64;lia);ring).
 assert (Top:word(regs s 4%nat-8)=st) by (rewrite SP;replace (st+8-8) with st by ring;apply word_fits;unfold word64;lia).
 pose proof(mapped_word _ _ _ I _ _ (power_in pol) ltac:(vm_compute;reflexivity)) as Good.
 assert (Target:word(o+(126+(DecoderBytes.pow_pc-(DecoderBytes.address+126))))=power bias)
   by (replace (o+(126+(DecoderBytes.pow_pc-(DecoderBytes.address+126)))) with (power bias) by (unfold o,base,DecoderFrame.origin,power;ring);
       apply word_fits,Good).
 set (args:=set (set (set (set s 14 (regs s 0%nat mod 2^32)) 2 (scratch e+3264)) 6 (scratch e+1984)) 7 (st+8)).
 set (child:=push args (return_pc bias));set (w:=qword (word(o+121)) st (return_pc bias)).
 assert (R:run 5 (ScalarBytes.fetch o text) (State (Running 101) s (carry p))=
   Some(State (Running(power bias-o)) child (carry p),[w])).
 { apply (checked _ _ _ bridge_bytes);unfold bridge;simpl follow;
   cbn [step cpu_state cf loc app effective set set_regs regs put Nat.eqb];rewrite A,B,Top,SP;match goal with |- context[word (o+?delta)-o]=>change (word(o+delta)=power bias) in Target;rewrite Target end;reflexivity. }
 assert (Safe:confined (writable e) [w]) by
   (constructor;[intros x X;change (st<=x<st+8) in X;left;unfold span;lia|constructor]).
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text _ 101 _ _ Acc At Map Sep R Safe) as [Next Paid].
 assert (Link:read_word (mem child) st=return_pc bias).
 { change (read_word (store_word (mem s) (word(regs s 4%nat-8)) (return_pc bias)) st=return_pc bias).
   rewrite Top;apply read_word_exact;[exact (DecoderProduct.address_fits pol bias e I DecoderKernel.Carry 126 ltac:(vm_compute;split;discriminate || reflexivity))|
    intros k K;unfold store_word;rewrite write_at by lia;reflexivity]. }
 eexists;split;[exact Next|split].
 2:{ intros x X;change (store_word (mem s) (word(regs s 4%nat-8)) (return_pc bias) x=mem s x).
     rewrite Top;apply write_outside,X. }
 unfold entry;cbn [LinkedRun.finish machine ip absolute loc cpu_state];fold st o.
 split;[ring|split;[exact Paid|]].
 assert (G:regs child=put (regs args) 4 st) by
   (unfold child,args;cbn [push push_words set set_regs with_words regs put Nat.eqb];now rewrite Top).
 split;[rewrite G;reflexivity|split;[rewrite G;reflexivity|split;[rewrite G;reflexivity|split;[rewrite G;reflexivity|split;[exact Link|]]]]].
 split.
 - intros j J;unfold key_signs in Key;rewrite G;exact (Key eq_refl j J).
 - split.
   2:{ unfold decoder_registers;change (regs child 3%nat=scratch e+1024 /\ regs child 5%nat=common_top pol e-120 /\ regs child 12%nat=2);
       rewrite G;exact (conj BX (conj BP N)). }
   intros j J;rewrite G;change (Z.testbit (regs s 0%nat mod 2^32) (Z.of_nat j)=Z.testbit (original_encoding true e j) 255);
   rewrite Z.mod_pow2_bits_low by lia;exact (proj2(proj2(Raw j J))).
Qed.

Record trace:=Trace { setup_points:chunks; exponent_entry:cursor }.
Definition observe bias p bank:=bind (observe_pair bias p bank) (fun r=>
 option_map (Trace r) (enter bias (in_decoder (signature_r r)))).
Definition post pol bias e r:=paired pol bias e (setup_points r) /\ entry pol bias e (exponent_entry r) /\
 Pow2Memory.valid_placement (locations pol bias e) size.
Theorem from_decoder pol bias e p bank : Return.placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> exists r,observe bias p bank=Some r /\ post pol bias e r.
Proof.
 intros P I Al Start;destruct(PairedSetup.from_decoder _ _ _ _ bank P I Al Start) as [r [Setup Points]].
 destruct(from_setup _ _ _ _ P I (proj2(proj2 Points))) as [q [Call [Args _]]].
 exists (Trace r q);split;[unfold observe;rewrite Setup;cbn [bind];now rewrite Call|
 exact (conj Points (conj Args (placement_ok _ _ _ P I)))].
Qed.
End Iteration.
