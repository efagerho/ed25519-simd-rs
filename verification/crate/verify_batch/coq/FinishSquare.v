From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordBounds execution.WordSemantics execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.AlignedRows execution.VectorProcedure
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.Decode Require Import Kernels Power.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderPower DecoderFinish DecoderProduct DecoderKernel NativeWords.
Import ListNotations. Local Open Scope Z_scope.

Definition load bias:=segment (base bias) text 5.
Definition call bias:=wrapped (base bias) text (base bias) text (DecoderProduct.native bias DecoderKernel.Square).
Definition evaluate bias:=then_run (load bias) (call bias).
Lemma loads_bound : linked text (AlignedRows.route false 901 0 6 0 5).
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Lemma called pol bias e : placement e -> loaded pol bias (mem e) (writable e) ->
 contract e (writable e) (DecoderProduct.area e) (base bias+935) (base bias+940) 8
 (DecoderKernel.body DecoderKernel.Square) (call bias).
Proof.
 intros P I;set (o:=base bias);apply (invoke _ _ _ o text 935 (0x59b-940) o text 0x7b1 0).
 - apply DecoderProduct.stack,P.
 - lia.
 - exact (DecoderProduct.placed pol bias e I DecoderKernel.Square).
 - exact (DecoderProduct.placed pol bias e I DecoderKernel.Square).
 - lia.
 - vm_compute;reflexivity.
 - lia.
 - vm_compute;reflexivity.
 - replace (o+(935+5)+(0x59b-940)) with (o+0x59b) by ring;
     exact (DecoderProduct.address_fits pol bias e I DecoderKernel.Square 0x59b ltac:(vm_compute;split;discriminate || reflexivity)).
 - exact (DecoderProduct.address_fits pol bias e I DecoderKernel.Square 940 ltac:(vm_compute;split;discriminate || reflexivity)).
 - replace (o+(935+5)+(0x59b-940)) with (o+0x59b) by ring;exact (DecoderProduct.calc pol bias e I DecoderKernel.Square).
Qed.

Lemma square_frame : kernel_frame DecoderProduct.kernel Square.
Proof. apply frame_ok;vm_compute;reflexivity. Qed.
Lemma lane r x : (forall i,(i<5)%nat -> r i=x i) ->
 (forall i,(i<4)%nat -> r (28+i)%nat=DecoderFrame.constant i) ->
 forall i,(i<5)%nat -> Instructions.run no_read (DecoderKernel.body DecoderKernel.Square) r i=
 Power.apply_kernel DecoderProduct.kernel Square x x i.
Proof.
 intros X C;refine (proj1(square_frame no_read no_read r (Power.feed x x) _)).
 intros i Live;destruct(Nat.lt_ge_cases i 5) as [Small|Large].
 - do 5 (destruct i as [|i];[apply X;lia|]);lia.
 - unfold live in Live;rewrite (proj2(Nat.ltb_ge _ _) Large) in Live;cbn in Live.
   do 28 (destruct i as [|i];[discriminate|]).
   do 4 (destruct i as [|i];[first [exact (C 0%nat ltac:(lia))|exact (C 1%nat ltac:(lia))|
        exact (C 2%nat ltac:(lia))|exact (C 3%nat ltac:(lia))]|]);discriminate.
Qed.

Definition operand sig pol e s j:=row s (link_slot pol e+8+DecoderFinish.power_offset sig) j.
Definition post sig pol bias e p q:=let slot:=link_slot pol e in
 ip q=base bias+940 /\ accounted e (writable e) q /\ well_formed(machine q) /\
 (forall r,regs(machine q) r=regs(machine p) r) /\
 preserved (fun x=>~(slot-8<=x<slot)) (mem(machine p)) (mem(machine q)) /\
 (forall i j,(i<4)%nat -> vectors(machine q) j (28+i)%nat=DecoderFrame.constant i) /\
 forall j i,(j<8)%nat -> (i<5)%nat -> let x:=operand sig pol e (machine p) j in
 vectors(machine q) j i=Power.apply_kernel DecoderProduct.kernel Square x x i.

Theorem from_entry sig pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 DecoderFinish.entry sig pol bias e p -> exists q,evaluate bias p=Some q /\ post sig pol bias e p q.
Proof.
 intros P I [PC [Acc [W [SP [DI [SI [Link [Env [Signs C]]]]]]]]].
 set (a:=link_slot pol e+8+DecoderFinish.power_offset sig) in *;set (s:=machine p) in *;set (o:=base bias) in *.
 pose proof(depth pol e) as Depth;destruct(Return.stack_ok _ P) as [[L H] _].
 assert (Fit:fits64 a 320) by (unfold a,DecoderFinish.power_offset,fits64;destruct sig;lia).
 assert (Al:a mod 64=0).
 { unfold a,link_slot,DecoderFrame.top;set (x:=common_top pol e-112-40);
   pose proof(Z.div_mod x 64 ltac:(lia)) as E;apply Z.mod_divide;[lia|].
   destruct sig;cbn [DecoderFinish.power_offset];[exists(x/64-5)|exists(x/64-10)];lia. }
 destruct(AlignedRows.loads o _ 5 901 0 6 0 a s (LinkedRun.carry p) loads_bound ltac:(lia) Al Fit)
   as [v [R [G [M [_ [Rows Other]]]]]].
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Away].
 destruct(at_segment _ _ _ o text 5 901 _ _ Acc PC Map Away R (Forall_nil _)) as [Load Paid].
 set (mid:=LinkedRun.finish o p (ScalarBytes.State (ScalarBytes.Running 935) v (LinkedRun.carry p),[])) in *.
 destruct(called pol bias e P I mid eq_refl Paid ltac:(change (sp e-16384+8<=regs v 4%nat<=sp e);rewrite G,SP;lia))
   as [q [Call [At Done Reg Keep Project]]].
 assert (WF:well_formed(machine q)) by
  (eapply (NativeWords.call _ _ _ _ _ (NativeWords.block _ _ _));[|exact Call];eapply segment_wf;[exact W|exact Load]).
 exists q;split;[unfold evaluate,then_run,load;fold o;rewrite Load;exact Call|].
 split;[exact At|split;[exact Done|split;[exact WF|split]]].
 - intro r;rewrite Reg;change (regs v r=regs s r);now rewrite G.
 - split.
   + intros x X;change (mem(machine q) x=mem s x);rewrite <- (f_equal (fun flat=>flat x) M);apply Keep;change (~(regs v 4%nat-8<=x<regs v 4%nat));now rewrite G,SP.
   + assert (High:forall j k,(k<4)%nat -> vectors v j (28+k)%nat=DecoderFrame.constant k)
       by (intros j k K;rewrite Other by lia;apply C,K).
     split.
     * intros k j K;rewrite Project;destruct(square_frame no_read no_read (vectors v j) (vectors v j) ltac:(reflexivity)) as [_ Survive];
       change (Instructions.run no_read (body DecoderProduct.kernel Square) (vectors v j) (28+k)%nat=DecoderFrame.constant k);
       rewrite Survive by lia;apply High,K.
     * intros j i J K;rewrite Project;apply lane;[intros k N;apply Rows,N|apply High|exact K].
Qed.
