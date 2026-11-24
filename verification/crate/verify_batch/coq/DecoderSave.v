From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute execution.AlignedRows
 memory.ByteMemory memory.WriteTrace memory.MemoryGeometry.
From Curve25519 Require Import Radix51.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode.
From Ed25519Simd.VerifyBatch Require DecoderFrame.
Local Open Scope Z_scope.

Definition address e := scratch e+1344.
Definition preserve bias := segment (bias+DecoderFrame.origin) DecoderFrame.code 5.
Definition digits e s j i := read_word (mem s) (address e+64*Z.of_nat i+8*Z.of_nat j).
Definition saved bias e p := ip p=bias+DecoderFrame.origin+497 /\ accounted e (writable e) p /\
 0<=regs(machine p) 0%nat<256 /\ forall j,(j<8)%nat ->
 split_field (digits e (machine p) j) /\ limbs (digits e (machine p) j)=original_key e j mod 2^255 /\
 Z.testbit (regs(machine p) 0%nat) (Z.of_nat j)=Z.testbit (original_key e j) 255.
Lemma bytes : linked DecoderFrame.code (AlignedRows.route true 462 0 7 320 5).
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Theorem from_limbs pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 regs(machine p) 7%nat=scratch e+1024 -> unpacked bias e p ->
 exists q,preserve bias p=Some q /\ saved bias e q /\ regs(machine q)=regs(machine p) /\
 vectors(machine q)=vectors(machine p) /\ forall j i,(j<8)%nat -> (i<5)%nat ->
 digits e (machine q) j i=vectors(machine p) j i.
Proof.
 intros Place Image DI [PC [Acc [Mask Data]]];set (o:=bias+DecoderFrame.origin) in *.
 destruct(scratch_ok _ Place) as [[Lo Hi] Al].
 destruct(mapped_now _ _ _ Image _ _ _ Acc (decode_in pol)) as [Map Apart].
 assert (Base:regs(machine p) 7%nat+320=address e) by (unfold address;lia).
 assert (Aligned:address e mod 64=0) by (unfold address;replace 1344 with (21*64) by reflexivity;now rewrite Z.mod_add by lia).
 destruct (stores o _ 5 462 0 7 320 (address e) (machine p) (carry p) bytes Base Aligned
    ltac:(unfold fits64,address;lia)
    ltac:(intros i j I J;pose proof (proj1(Data j J) i I) as B;change (0<=vectors(machine p) j i<=2^52-1) in B;change (0<=vectors(machine p) j i<2^64);lia))
    as [s [ws [Run [Regs [Vec [_ [Safe Rows]]]]]]].
 assert (W:confined (writable e) ws).
 { apply Forall_impl with (P:=permits (range (address e) 5));[|exact Safe].
   intros w R x X;specialize(R x X);right;left;unfold span,range,address in *;lia. }
 destruct (at_segment _ _ _ o DecoderFrame.code _ 462 _ _ Acc PC Map Apart Run W) as [Next Paid].
 eexists;split;[exact Next|split].
 - split;[reflexivity|split;[exact Paid|]]. cbn [LinkedRun.finish machine cpu_state].
   rewrite Regs;split;[exact Mask|]. intros j J;destruct(Data j J) as [Bound [Y Sign]].
   assert (D:forall i,(i<5)%nat -> digits e s j i=vectors(machine p) j i) by (intros i I;apply Rows;assumption).
   split;[intros i I;rewrite D by exact I;apply Bound,I|split;[rewrite <-Y;apply limbs_ext,D|exact Sign]].
 - split;[exact Regs|split;[exact Vec|]]. intros j i J I;apply Rows;assumption.
Qed.

Definition key_setup bias decoder incoming :=
 bind (inner bias decoder) (fun s=>bind (transpose bias s) (fun words=>
 bind (unpack bias words incoming) (fun '(y,k)=>option_map (fun p=>(p,k)) (preserve bias y)))).
Definition frame pol e s := let sp:=common_top pol e-112 in
 regs s 7%nat=scratch e+1024 /\ regs s 4%nat=DecoderFrame.top sp-8 /\
 forall i j,(i<4)%nat -> vectors s j (28+i)%nat=DecoderFrame.constant i.

Theorem from_decoder pol bias e p incoming : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> entry pol bias e p ->
 exists q updated,key_setup bias p incoming=Some(q,updated) /\ saved bias e q /\
 frame pol e (machine q) /\ forall j i,(j<8)%nat -> (i<5)%nat -> digits e (machine q) j i=vectors(machine q) j i.
Proof.
 intros P M Al Entry;destruct(BatchDecode.from_decoder _ _ _ _ P M Entry) as [s [Inner Setup]].
 destruct(BatchDecode.from_setup _ _ _ _ P M Al Setup) as [v [Next [Words [_ [_ G]]]]].
 destruct(BatchDecode.from_words _ _ _ _ incoming P M Words) as [y [k [Unpack [Value [_ [_ [Other Constants]]]]]]].
 destruct Setup as [_ [_ [SP [_ [_ [DI _]]]]]].
 assert (Dest:regs(machine y) 7%nat=scratch e+1024) by (rewrite Other,G by discriminate;exact DI).
 destruct(from_limbs _ _ _ _ P M Dest Value) as [q [Save [Saved [Regs [Vec Data]]]]].
 exists q,k;split;[unfold key_setup;rewrite Inner;cbn [bind];rewrite Next;cbn [bind];rewrite Unpack;cbn [bind];now rewrite Save|].
 split;[exact Saved|split].
 - unfold frame;rewrite Regs;split;[exact Dest|split;[rewrite Other,G by discriminate;exact SP|intros i j I;rewrite Vec;apply Constants,I]].
 - intros j i J I;rewrite Vec;exact (Data j i J I).
Qed.
