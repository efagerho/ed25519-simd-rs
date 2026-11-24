From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.QwordBlock
 memory.ByteMemory memory.MemoryGeometry.
From Machine Require execution.MaskedResult execution.MaskTransfer.
From Ed25519Simd.Decode Require Scale.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame MaskSegment.
Import ListNotations. Local Open Scope Z_scope.
Module MR:=MaskedResult.

Definition parity:=map Arithmetic [
 (20%nat,Add 0 28);(20%nat,Shr 20 51);(20%nat,Add 20 1);(20%nat,Shr 20 51);
 (20%nat,Add 20 2);(20%nat,Shr 20 51);(20%nat,Add 20 3);(20%nat,Shr 20 51);
 (20%nat,Add 20 4);(20%nat,Shr 20 51);(20%nat,Xor 0 20)].
Definition compare:=[MR.TestBroadcast 3 20 0xb80;MR.FromGpr 4 9;MR.Exclusive 3 3 4].
Definition execute bias p bank:=bind (segment (base bias) text 11 p) (fun mid=>MR.execute (base bias) compare mid bank).
Definition need_sign s j:=xorb (Scale.parity_after (vectors s j)) (Z.testbit (regs s 9%nat) (Z.of_nat j)).
Lemma images:linked text (route 1163 parity) /\
 MR.assemble 1234 compare=Some(MaskSegment.bytes 1234 19) /\ length(MaskSegment.bytes 1234 19)=19%nat.
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma add_comm a b : Arithmetic.vpaddq a b=Arithmetic.vpaddq b a.
Proof. unfold Arithmetic.vpaddq;now rewrite Z.add_comm. Qed.
Lemma parity_bit load h : h 28%nat=19 ->
 negb(Z.land (lane load h parity 20%nat) 1=?0)=Scale.parity_after h.
Proof.
 intro H;cbn [parity map lane lane_step bits put Nat.eqb];unfold Scale.parity_after;rewrite H.
 rewrite (add_comm _ (h 1%nat)),(add_comm _ (h 2%nat)),(add_comm _ (h 3%nat)),(add_comm _ (h 4%nat));reflexivity.
Qed.
Definition sign_bit (s:cpu) j:=Z.testbit (regs s 9%nat) (Z.of_nat j).
Theorem checked pol bias e p bank : loaded pol bias (mem e) (writable e) -> ip p=base bias+1163 ->
 accounted e (writable e) p -> well_formed(machine p) -> (forall j,vectors(machine p) j 28%nat=19) ->
 exists q out,execute bias p bank=Some(q,out) /\ ip q=base bias+1253 /\ accounted e (writable e) q /\
 well_formed(machine q) /\ regs(machine q)=regs(machine p) /\ mem(machine q)=mem(machine p) /\ log q=log p /\
 (forall j i,i<>20%nat -> vectors(machine q) j i=vectors(machine p) j i) /\
 forall j,(j<8)%nat -> out 3%nat j=need_sign (machine p) j.
Proof.
 intros I PC Acc W C;set (o:=base bias) in *;set (s:=machine p) in *.
 destruct(QwordBlock.execute o _ _ _ s (LinkedRun.carry p) (proj1 images)) as [v [Run [G [M [_ Vec]]]]].
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text 11 1163 _ _ Acc PC Map Sep Run (Forall_nil _)) as [Start Paid].
 set (mid:=LinkedRun.finish o p (State (Running 1234) v (LinkedRun.carry p),[])) in *.
 assert (MW:well_formed(machine mid)) by exact (segment_wf _ _ _ _ _ W Start).
 set (test:=fun j=>negb(Z.land (vectors v j 20%nat) (read_word (mem v) (word(o+0xb80)))=?0)).
 set (kt:=MR.set_mask bank 3 8 test);set (ks:=MR.set_mask kt 4 16 (sign_bit v)).
 set (kk:=MR.set_mask ks 3 16 (fun j=>xorb (ks 3%nat j) (ks 4%nat j))).
 assert (Eval:MR.evaluate o v bank compare=Some(v,kk)) by reflexivity.
 destruct(MaskSegment.checked pol bias e 1234 19 compare mid bank v kk I ltac:(lia) ltac:(change (1253<2984);lia)
   (proj2(proj2 images)) (proj1(proj2 images)) eq_refl Paid MW Eval) as [q [Pick [V [End [Safe [WF [_ [_ Log]]]]]]]].
 assert (Lit:read_word (mem v) (word(o+0xb80))=1).
 { rewrite M;apply (read_literal bias DecoderFrame.origin text 0xb80 1 (mem s) Map
   (proj1(symbols _ _ _ _ I _ _ (decode_in pol))) ltac:(lia) ltac:(change (2952<=2984);lia) ltac:(vm_compute;reflexivity)). }
 exists q,kk;split;[unfold execute;fold o;rewrite Start;exact Pick|split;[exact End|split;[exact Safe|split;[exact WF|]]]].
 split;[rewrite V;exact G|split;[rewrite V;exact M|split]].
 - rewrite Log;apply app_nil_r.
 - split.
   + intros j i N;rewrite V,Vec;cbn [parity map lane lane_step bits];unfold put;now rewrite (proj2(Nat.eqb_neq 20 i) ltac:(lia)).
   + intros j J;unfold kk,ks,kt,MR.set_mask,put;cbn [Nat.eqb];rewrite (proj2(Nat.ltb_lt j 16) ltac:(lia)),(proj2(Nat.ltb_lt j 8) J).
     cbn [andb];unfold test,sign_bit,need_sign;rewrite Lit,G;rewrite (Vec j);now rewrite parity_bit by apply C.
Qed.
