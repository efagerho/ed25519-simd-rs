From Coq Require Import List ZArith Znumtheory Bool Lia.
From Machine Require Import isa.Instructions isa.QwordRegister execution.ScalarBytes execution.LinkedCalls
 execution.WordBounds execution.WordSemantics execution.InstructionRoute execution.LinkedRun execution.MappedFetch
 memory.MemoryGeometry memory.ByteMemory memory.WriteTrace.
From Machine Require execution.MaskTransfer execution.QwordBlock.
From Ed25519Simd.Decode Require Unpack Limbs.
From Ed25519Simd.VerifyBatch Require DecoderWords DecoderFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition take_signs p ks :=
 match MaskTransfer.tick (MaskTransfer.Signs 2 6) p ks with
 | Some (q,updated)=>MaskTransfer.tick (MaskTransfer.ToEax 2) q updated
 | None=>None end.
Lemma signs o p ks : ip p=o+355 -> fits64 o (Z.of_nat(length DecoderFrame.code)) ->
 mapped (mem(machine p)) o DecoderFrame.code ->
 exists q updated,take_signs p ks=Some(q,updated) /\ ip q=o+365 /\ log q=log p /\
 mem(machine q)=mem(machine p) /\ vectors(machine q)=vectors(machine p) /\
 (forall r,r<>0%nat -> regs(machine q) r=regs(machine p) r) /\
 (forall j,updated 2%nat j=MaskTransfer.sign_bits (machine p) 6%nat j) /\
 0<=regs(machine q) 0%nat<256 /\ forall j,(j<8)%nat ->
 Z.testbit (regs(machine q) 0%nat) (Z.of_nat j)=Z.testbit (vectors(machine p) j 6%nat) 63.
Proof.
 intros PC [Lo Hi] Map;change (Z.of_nat(length DecoderFrame.code)) with 2984 in Hi.
 set (m:=mem(machine p)) in *;set (a:=MaskTransfer.Signs 2 6);set (b:=MaskTransfer.ToEax 2).
 assert (A:mapped m (ip p) (MaskTransfer.encoding a)).
 { rewrite PC;exact (MaskTransfer.subimage _ _ _ 355 (MaskTransfer.encoding a) Map ltac:(change (361<=2984)%nat;lia) ltac:(vm_compute;reflexivity)). }
 unfold take_signs;fold a b;rewrite (MaskTransfer.fetched a p ks eq_refl A);cbn [a MaskTransfer.effect];fold a.
 set (q:=Cursor _ _ _ _).
 assert (Middle:ip q=o+361).
 { unfold q;cbn [ip];rewrite PC;change (word(o+355+6)=o+361);rewrite word_fits by (unfold word64;lia);ring. }
 assert (B:mapped (mem(machine q)) (ip q) (MaskTransfer.encoding b)).
 { rewrite Middle;exact (MaskTransfer.subimage _ _ _ 361 (MaskTransfer.encoding b) Map ltac:(change (365<=2984)%nat;lia) ltac:(vm_compute;reflexivity)). }
 rewrite (MaskTransfer.fetched b q _ eq_refl B);do 2 eexists;split;[reflexivity|].
 cbn [b MaskTransfer.effect ip log regs set set_regs machine with_words put Nat.eqb];unfold q;
 cbn [cpu_state ip machine log regs vectors mem set set_regs put Nat.eqb];rewrite PC.
 split;[change (word(word(o+355+6)+4)=o+365);rewrite (word_fits (o+355+6)),word_fits by (unfold word64;lia);ring|].
 split;[reflexivity|split;[reflexivity|split;[reflexivity|]]]. split.
 - intros r R;unfold put;now rewrite (proj2(Nat.eqb_neq 0 r) ltac:(lia)).
 - split;[intros;reflexivity|exact (MaskTransfer.sign_word _ _)].
Qed.

Import QwordBlock.
Definition ops : list operation :=
 [Arithmetic(1%nat,Shr 0 51);Arithmetic(5%nat,Shl 4 13);BitOr 1 1 5;
  Arithmetic(4%nat,Shr 4 38);Arithmetic(5%nat,Shl 2 26);BitOr 4 4 5;
  Arithmetic(3%nat,Shr 2 25);Arithmetic(5%nat,Shl 6 39);BitOr 3 3 5;
  Arithmetic(2%nat,And 4 29);Arithmetic(4%nat,Shr 6 12);
  Arithmetic(0%nat,And 0 29);Arithmetic(1%nat,And 1 29);Arithmetic(3%nat,And 3 29);Arithmetic(4%nat,And 4 29)].
Lemma bound : linked DecoderFrame.code (route 365 ops).
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Lemma word_mask x : Unpack.masked (word x)=Unpack.masked x.
Proof. unfold Unpack.masked,word;rewrite !Z.land_ones by lia.
 symmetry;apply Zmod_div_mod;[lia|lia|exists 8192;reflexivity].
Qed.
Lemma limbs o s c flat (source:nat->Z) :
 (forall j,(j<8)%nat -> vectors s j 29%nat=Z.ones 51) ->
 (forall j w,(j<8)%nat -> (w<4)%nat -> vectors s j (DecoderWords.result_reg w)=Unpack.qword flat (source j) w 0%nat) ->
 exists v,run 15 (ScalarBytes.fetch o DecoderFrame.code) (State (Running 365) s c)=Some(State (Running 462) v c,[]) /\
 regs v=regs s /\ mem v=mem s /\ forall j i,(j<8)%nat -> (i<5)%nat ->
 vectors v j i=Unpack.unpack flat (source j) 0%nat i.
Proof.
 intros Mask Words;destruct (execute o _ _ _ s c bound) as [v [Run [Regs [Mem [_ Values]]]]].
 exists v;split;[exact Run|split;[exact Regs|split;[exact Mem|]]].
 intros j i J I;pose proof(Words j 0%nat J ltac:(lia)) as A;pose proof(Words j 1%nat J ltac:(lia)) as B;
 pose proof(Words j 2%nat J ltac:(lia)) as C;pose proof(Words j 3%nat J ltac:(lia)) as D.
 change (DecoderWords.result_reg 0) with 0%nat in A;change (DecoderWords.result_reg 1) with 4%nat in B;
 change (DecoderWords.result_reg 2) with 2%nat in C;change (DecoderWords.result_reg 3) with 6%nat in D.
 rewrite Values;destruct i as [|[|[|[|[|i]]]]];try lia.
 all: cbv beta iota zeta delta [ops lane lane_step bits put Nat.eqb Logic.vpandq Unpack.unpack Limbs.five];
   rewrite ?A,?B,?C,?D,(Mask j J);
   unfold Unpack.splice;first [apply word_mask|reflexivity].
Qed.
