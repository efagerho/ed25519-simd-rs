From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.LinkedCalls execution.LinkedRun
 execution.WordBounds execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute
 execution.AlignedRows execution.VectorProcedure memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.Decode Require Import Limbs Scale.
From Ed25519Simd.Decode Require Power Decode Kernels.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode DecoderSave KeySquare SetupTail NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderProduct DecoderKernel DecoderFrame NativeWords.
Import ListNotations. Local Open Scope Z_scope.

Definition carry_code:list Instructions.instruction:=
 flat_map (fun i=>[((10+i)%nat,Shr i 51);(i,And i 29)]) (seq 0 5)++
 [(0%nat,Madd false 14 28)]++map (fun i=>(i,Add i (9+i))) (seq 1 4).
Lemma carry_lane r d :
 (forall i,(i<5)%nat -> r i=d i) -> r 28%nat=19 -> r 29%nat=radix-1 ->
 forall i,(i<5)%nat -> Instructions.run no_read (DecoderKernel.body DecoderKernel.Carry) r i=reduced d i.
Proof.
 assert (Code:DecoderKernel.body DecoderKernel.Carry=carry_code) by (vm_compute;reflexivity).
 intros R K M i I;rewrite Code;destruct i as [|[|[|[|[|i]]]]];try lia;
 cbv beta iota zeta delta [carry_code seq flat_map map app Instructions.run fold_left
   put Nat.eqb bits reduced Nat.add];rewrite ?K,?M,!R by lia;reflexivity.
Qed.

Section Setup.
Variables (signature:bool) (pol:policy) (bias:Z) (e:cpu).
Hypothesis P:placement e.
Hypothesis Image:loaded pol bias (mem e) (writable e).
Local Notation a:=(point e signature).
Local Notation o:=(base bias).
Local Notation state:=(stage signature pol bias e).

Lemma spill off delta p q :
 linked text (AlignedRows.route true off 0 7 delta 5) -> 0<=delta<=960 -> delta mod 64=0 ->
 state off p -> well_formed(machine p) -> step_at bias 5 p=Some q ->
 AlignedRows.saved (machine p) (machine q) (a+delta) 0 5 /\
 preserved (fun x=>~(a+delta<=x<a+delta+320)) (mem(machine p)) (mem(machine q)).
Proof.
 intros Route D Dal S W Next;destruct(scratch_ok _ P) as [[L H] Al].
 assert (A:a mod 64=0) by (apply point_aligned,Al).
 destruct(AlignedRows.stores o _ 5 off 0 7 delta (a+delta) (machine p) (LinkedRun.carry p) Route
   ltac:(rewrite (dest _ _ _ _ _ _ S);reflexivity) ltac:(rewrite Z.add_mod,A,Dal by lia;reflexivity)
   ltac:(unfold fits64,point,point_offset;destruct signature;change (Z.of_nat 5) with 5;lia)
   ltac:(intros i j I J;apply W,J)) as [t [ws [R [_ [_ [_ [Safe Rows]]]]]]].
 assert (Bound:confined (writable e) ws).
 { apply Forall_impl with (P:=permits (range (a+delta) 5));[|exact Safe].
   intros w V x X;specialize(V x X);right;left;unfold span,range,point,point_offset in *;destruct signature;change (Z.of_nat 5) with 5 in V;lia. }
 pose proof(SetupTail.paid _ _ _ _ _ _ S) as Acc;destruct(mapped_now _ _ _ Image _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text 5 off _ _ Acc (position _ _ _ _ _ _ S) Map Sep R Bound) as [At _].
 unfold step_at in Next;rewrite At in Next;injection Next as <-;split;[exact Rows|].
 pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)) as Mem;change (mem t=WriteTrace.replay (mem(machine p)) ws) in Mem.
 intros x X;change (mem t x=mem(machine p) x);rewrite Mem;apply (WriteTrace.frame _ _ Safe),X.
Qed.

Lemma keep_row s t ptr protect :
 preserved protect (mem s) (mem t) -> (forall x,ptr<=x<ptr+320 -> protect x) ->
 forall j i,(j<8)%nat -> (i<5)%nat -> row t ptr j i=row s ptr j i.
Proof. intros M Ext j i J I;apply preserved_read with (outside:=protect);[exact M|].
 intros k K;change (0<=k<8) in K;apply Ext;lia. Qed.

Definition product h:=Power.apply_kernel DecoderProduct.kernel Kernels.Multiply (u_digits h) (v_digits h).
Definition fields (p q:cursor):=forall j i,(j<8)%nat -> (i<5)%nat ->
 let h:=vectors(machine p) j in
 row (machine q) a j i=u_digits h i /\
 row (machine q) (a+640) j i=v_digits h i /\
 row (machine q) (a+960) j i=product h i.

Lemma off_stack delta n x : 0<=delta<=960 -> 0<=n<=24 ->
 a+delta<=x<a+delta+320 -> ~(link_slot pol e-n<=x<link_slot pol e).
Proof.
 intros;pose proof(depth pol e);destruct(scratch_stack _ P);
 unfold disjoint,point,point_offset in *;destruct signature;lia.
Qed.

Theorem returned_fields p q : squared signature pol bias e p -> well_formed(machine p) ->
 finish_setup bias p=Some q -> fields p q /\ preserved (setup_untouched signature pol e) (mem(machine p)) (mem(machine q)).
Proof.
 intros S W End;destruct(trace_tail _ _ _ _ P Image _ S) as [final [Tail [_ Path]]].
 rewrite End in Tail;injection Tail as <-.
 destruct Path as [aa b c d f g h Scale A B F G Carry CE Save Load LM LR Ptr Arg PM PR Mul ME Store RM].
 destruct(at_scale signature pol bias e p P Image S W) as [scaled [To [Data ScaleMem]]].
 rewrite Scale in To;injection To as <-.
 pose proof(segment_wf _ _ _ _ _ W Scale) as WA.
 assert (WB:well_formed(machine b)).
 { eapply (NativeWords.call _ _ _ _ _ (NativeWords.block _ _ _));eassumption. }
 pose proof(segment_wf _ _ _ _ _ WB Save) as WC;pose proof(segment_wf _ _ _ _ _ WC Load) as WD.
 pose proof(segment_wf _ _ _ _ _ WD Ptr) as WF;pose proof((proj1(NativeWords.kernels bias)) _ _ WF Mul) as WG.
 destruct(spill 784 640 b c ltac:(repeat constructor;vm_compute;discriminate || reflexivity) ltac:(lia) eq_refl B WB Save) as [VRows KeepU].
 destruct(spill 865 960 g h ltac:(repeat constructor;vm_compute;discriminate || reflexivity) ltac:(lia) eq_refl G WG Store) as [UVRows KeepUV].
 destruct CE as [_ _ _ CMem CRegs];destruct ME as [_ _ _ MMem MRegs].
 pose proof(stack _ _ _ _ _ _ A) as ASP;pose proof(stack _ _ _ _ _ _ F) as FSP.
 rewrite ASP in CMem;rewrite FSP in MMem.
 split.
 2:{ intros x [Stack Outside];change (~(link_slot pol e-24<=x<link_slot pol e)) in Stack;unfold span in Outside;
     rewrite RM,KeepUV,MMem,PM,LM,KeepU,CMem,ScaleMem by lia;reflexivity. }
 assert (InA:forall x,a<=x<a+320 -> ~(link_slot pol e-8<=x<link_slot pol e)).
 { intros x X;apply (off_stack 0 8 x);lia. }
 assert (Later:forall offset,0<=offset<=640 -> forall j i,(j<8)%nat -> (i<5)%nat ->
   row (machine q) (a+offset) j i=row (machine c) (a+offset) j i).
 { intros offset O j i J I;unfold row;rewrite RM.
   apply preserved_read with (outside:=fun x=>a+offset<=x<a+offset+320).
   - intros x X;rewrite (KeepUV x) by lia;rewrite (MMem x) by (apply (off_stack offset 24 x);lia);now rewrite PM,LM.
   - intros k K;change (0<=k<8) in K;lia. }
 assert (Good:forall j,(j<8)%nat -> bounded(vectors(machine p) j) /\ 2<=vectors(machine p) j 0%nat).
 { destruct S as [_ [_ [_ [_ Squared]]]];intros j J;destruct(Squared j J) as [Bounds [_ Pos]].
   split;[|exact Pos];intros k K;specialize(Bounds k K);change (0<=vectors(machine p) j k<=radix+2^16) in Bounds;lia. }
 assert (U:forall j i,(j<8)%nat -> (i<5)%nat -> row (machine c) a j i=u_digits (vectors(machine p) j) i).
 { intros j i J I;transitivity (row (machine aa) a j i).
   - apply keep_row with (protect:=fun x=>a<=x<a+320);[|auto|exact J|exact I].
     intros x X;rewrite (KeepU x) by lia;apply CMem,InA,X.
   - rewrite (proj1(Data j i J I));exact (proj1(scale_native _ (proj1(Good j J)) (proj2(Good j J)) i I)). }
 assert (V:forall j i,(j<8)%nat -> (i<5)%nat -> row (machine c) (a+640) j i=v_digits (vectors(machine p) j) i).
 { intros j i J I;unfold row;rewrite (VRows i j I J).
   change (vectors(machine b) j i=v_digits (vectors(machine p) j) i);rewrite (CRegs j);set (v:=vectors(machine p) j).
   rewrite (carry_lane _ (difference v) ltac:(intros k K;exact (proj2(Data j k J K)))
    (constants _ _ _ _ _ _ A 0%nat j ltac:(lia)) (constants _ _ _ _ _ _ A 1%nat j ltac:(lia)) i I).
   exact (proj2(proj2(scale_native v (proj1(Good j J)) (proj2(Good j J)) i I))). }
 assert (Pushed:forall j i,(j<8)%nat -> (i<5)%nat ->
   DecoderProduct.rhs_at (push (machine f) (o+865)) j i=row (machine c) (a+640) j i).
 { intros j i J I;unfold DecoderProduct.rhs_at,row.
   change (read_word (store_word (mem(machine f)) (word(regs(machine f) 4%nat-8)) (o+865))
      (regs(machine f) 8%nat+64*Z.of_nat i+8*Z.of_nat j)=read_word (mem(machine c)) (a+640+64*Z.of_nat i+8*Z.of_nat j)).
   rewrite Arg,FSP,(word_fits (link_slot pol e-8)) by (pose proof(depth pol e);destruct(Return.stack_ok _ P) as [[SL SH] _];unfold word64;lia).
   apply preserved_read with (outside:=fun x=>a+640<=x<a+960).
   - intros x X;unfold store_word;rewrite write_outside by (intro Touch;apply (off_stack 640 8 x ltac:(lia) ltac:(lia) ltac:(lia));lia).
     now rewrite PM,LM.
   - intros k K;change (0<=k<8) in K;lia. }
 intros j i J I;split.
 - replace a with (a+0) at 1 by ring;rewrite Later by lia;rewrite Z.add_0_r;apply U;assumption.
 - split;[rewrite Later by lia;apply V;assumption|].
   unfold row;rewrite RM,(UVRows i j I J);change (vectors(machine g) j i=product (vectors(machine p) j) i).
   rewrite MRegs;unfold product;apply DecoderProduct.lane_product;[| |exact I].
   + intros k K;unfold DecoderProduct.arguments;rewrite (proj2(Nat.leb_gt 5 k) ltac:(lia)),
      (proj2(Nat.leb_le 5 (5+k)%nat) ltac:(lia)),(proj2(Nat.ltb_lt (5+k) 10) ltac:(lia)).
     replace (5+k-5)%nat with k by lia;split;[change (vectors(machine f) j k=u_digits (vectors(machine p) j) k);rewrite PR,LR by exact K;apply U;assumption|].
     rewrite Pushed by assumption;apply V;assumption.
   + intros k K;unfold DecoderProduct.arguments;rewrite (proj2(Nat.ltb_ge (28+k) 10) ltac:(lia)),andb_false_r.
     exact (constants _ _ _ _ _ _ F k j K).
Qed.

Theorem setup_fields p bank r : (bias+DecoderFrame.origin) mod 64=0 -> setup signature pol bias e p ->
 well_formed(machine p) -> input_setup bias p bank=Some r ->
 fields (after_square r) (in_decoder r) /\ preserved (setup_untouched signature pol e) (mem(machine p)) (mem(machine(in_decoder r))).
Proof.
 intros Al S W;destruct(KeySquare.from_setup signature pol bias e p bank P Image Al S) as [sq [k [Run [Value Keep]]]].
 unfold input_setup;rewrite Run;cbn [bind];destruct(finish_setup bias sq) as [q|] eqn:T;[|discriminate].
 intro Eq;injection Eq as <-;destruct(returned_fields sq q Value (NativeWords.setup_square_words _ _ _ _ _ W Run) T) as [Out More].
 split;[exact Out|intros x X;cbn [in_decoder];now rewrite More,Keep by exact X].
Qed.
End Setup.
