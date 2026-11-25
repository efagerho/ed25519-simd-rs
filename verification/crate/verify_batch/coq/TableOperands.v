From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds
 execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.MappedFetch
 execution.InstructionRoute execution.AlignedRows execution.RipBroadcasts memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.Decode Require HelperBytes.
From Ed25519Simd.KeyTable Require Fields.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableEntry TableFrame TableKernels DecoderFrame NativeScale.
Import ListNotations. Local Open Scope Z_scope.

Definition constants:=HelperBytes.address+0xde0-TableEntry.origin.
Definition factor:=0x8c0.
Lemma sites:linked TableFrame.text (RipBroadcasts.route 4 124 28 constants) /\
 linked TableFrame.text (AlignedRows.route false 164 0 12 960 5) /\
 linked TableFrame.text (RipBroadcasts.route 5 204 5 factor).
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma literal i : (i<5)%nat ->
 read_word (fun x=>nth (Z.to_nat x) TableFrame.text 0) (factor+8*Z.of_nat i)=Fields.two_d i.
Proof. intros N;destruct i as [|[|[|[|[|i]]]]];[vm_compute;reflexivity..|lia]. Qed.

Definition setup bias:=segment (TableFrame.base bias) TableFrame.text 14.
Definition inputs pt s j i:=read_word (mem s) (pt+960+64*Z.of_nat i+8*Z.of_nat j).
Record ready e p q:Prop:=Ready {
 regs_after:regs(machine q)=regs(machine p);
 memory_after:mem(machine q)=mem(machine p);
 flags_after:flag(machine q)=flag(machine p);
 coordinates:forall j i,(i<5)%nat -> vectors(machine q) j i=inputs (TableEntry.point e) (machine p) j i;
 coefficient:forall j i,(i<5)%nat -> vectors(machine q) j (5+i)%nat=Fields.two_d i;
 field_constants:forall j i,(i<4)%nat -> vectors(machine q) j (28+i)%nat=DecoderFrame.constant i
}.

Theorem checked pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=TableFrame.base bias+124 -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 12%nat=TableEntry.point e ->
 exists q,setup bias p=Some q /\ ip q=TableFrame.base bias+TableKernels.site Fields.TwoDT /\
 accounted e (writable e) q /\ well_formed(machine q) /\ ready e p q.
Proof.
 intros P I PC Acc W R12;set (s:=machine p) in *;set (o:=TableFrame.base bias) in *;set (pt:=TableEntry.point e) in *.
 destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 destruct(RipBroadcasts.load o _ _ _ _ _ s (LinkedRun.carry p) (proj1 sites)) as [a [A [GA [MA [FA [C _]]]]]].
 destruct(scratch_ok _ P) as [[L H] Align].
 assert (Aligned:(pt+960) mod 64=0).
 { replace (pt+960) with (scratch e+31*64) by (unfold pt,TableEntry.point;ring);now rewrite Z.mod_add by lia. }
 destruct(AlignedRows.loads o _ 5 164 0 12 960 (pt+960) a (LinkedRun.carry p) (proj1(proj2 sites))
  ltac:(now rewrite GA,R12) Aligned ltac:(unfold fits64,pt,TableEntry.point;change (Z.of_nat 5) with 5;lia))
  as [b [B [GB [MB [FB [Rows Held]]]]]].
 destruct(RipBroadcasts.load o _ _ _ _ _ b (LinkedRun.carry p) (proj2(proj2 sites))) as [t [T [GT [MT [FT [Factor Keep]]]]]].
 change (124+10*Z.of_nat 4) with 164 in A.
 change (AlignedRows.after false 164 0 12 960 5) with 204 in B.
 pose proof(run_append _ _ _ _ _ (run_append _ _ _ _ _ A _ _ _ B) _ _ _ T) as Run.
 destruct(at_segment _ _ p o TableFrame.text 14 124 _ _ Acc PC Map Sep Run (Forall_nil _)) as [Step Paid].
 eexists;split;[exact Step|split;[reflexivity|split;[exact Paid|split;[exact (segment_wf _ _ _ _ _ W Step)|constructor]]]].
 - exact (eq_trans GT (eq_trans GB GA)).
 - exact (eq_trans MT (eq_trans MB MA)).
 - exact (eq_trans FT (eq_trans FB FA)).
 - intros j i N;change (vectors t j i=inputs pt s j i);rewrite Keep by lia;exact (eq_trans (Rows j i N) (f_equal (fun m=>read_word m (pt+960+64*Z.of_nat i+8*Z.of_nat j)) MA)).
 - intros j i N;change (vectors t j (5+i)%nat=Fields.two_d i);rewrite Factor,MB,MA by exact N.
   replace (o+factor+8*Z.of_nat i) with (bias+TableEntry.origin+(factor+8*Z.of_nat i)) by (unfold o,TableFrame.base;ring).
   eapply NativeScale.read_literal;[exact Map|exact (proj1(symbols _ _ _ _ I _ _ (TableEntry.image pol)))|
     unfold factor;lia|change (factor+8*Z.of_nat i+8<=2280);unfold factor;lia|apply literal,N].
 - intros j i N;change (vectors t j (28+i)%nat=DecoderFrame.constant i);rewrite Keep,Held,C by lia.
   destruct(mapped_now _ _ _ I _ _ _ Acc (BatchDecode.helper_in pol)) as [Helper _].
   replace (o+constants+8*Z.of_nat i) with (bias+HelperBytes.address+DecoderFrame.field_offset i) by
      (unfold o,TableFrame.base,constants,DecoderFrame.field_offset;ring).
   eapply NativeScale.read_literal;[exact Helper|exact (proj1(symbols _ _ _ _ I _ _ (BatchDecode.helper_in pol)))|
    apply DecoderFrame.offsets,N|apply DecoderFrame.offsets,N|apply DecoderFrame.literal_value,N].
Qed.
