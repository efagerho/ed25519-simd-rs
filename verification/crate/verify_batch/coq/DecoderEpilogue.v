From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.StoreInstructions execution.InstructionRoute execution.MappedFetch
 memory.ByteMemory memory.MemoryGeometry memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare.
From Ed25519Simd.Decode Require Chunks.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderSpills.
Import ListNotations. Local Open Scope Z_scope.

Definition pack: list line:=[(222,3%nat,Shl32 0 8);(225,3%nat,Or32 0 13)].
Definition restore: list line:=[(228,4%nat,LeaG 4 (Address 5 None (-32)));(232,2%nat,RestoreG 14);
 (234,2%nat,RestoreG 13);(236,2%nat,RestoreG 12);(238,1%nat,RestoreG 3);(239,1%nat,RestoreG 5);
 (240,3%nat,ZeroUpper);(243,1%nat,Ret)].
Lemma linked_code:linked text pack /\ linked text restore.
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition packed a r:=Z.lor (Z.shiftl r 8) a.
Lemma above_byte v i : 0<=v<256 -> 8<=i -> Z.testbit v i=false.
Proof.
 intros V I;rewrite <-(Z.mod_small v (2^8) V);apply Z.mod_pow2_bits_high;lia.
Qed.
Lemma packed_value a r : 0<=a<256 -> 0<=r<256 -> packed a r=256*r+a.
Proof. intros A _;apply Chunks.combine_masks,A. Qed.
Lemma bits a r i : 0<=a<256 -> 0<=i<8 -> Z.testbit (packed a r) i=Z.testbit a i /\
 Z.testbit (packed a r) (8+i)=Z.testbit r i.
Proof. intros A I;unfold packed;rewrite !Z.lor_spec,!Z.shiftl_spec,Z.testbit_neg_r,(above_byte a (8+i)) by lia;
 replace (8+i-8) with i by ring;now rewrite orb_false_r. Qed.

Lemma masks o s c : 0<=regs s 0%nat<256 -> 0<=regs s 13%nat<256 ->
 exists u,run 2 (ScalarBytes.fetch o text) (State (Running 222) s c)=Some(State (Running 228) u (Some false),[]) /\
 regs u 0%nat=packed (regs s 13%nat) (regs s 0%nat) /\ (forall r,r<>0%nat -> regs u r=regs s r) /\ mem u=mem s.
Proof.
 intros R A;eexists;split;[apply (InstructionRoute.checked _ _ _ (proj1 linked_code));reflexivity|].
 cbn [pack follow step option_map loc cpu_state cf app with_zf set set_regs regs put Nat.eqb mem].
 rewrite (Z.mod_small (regs s 0%nat) (2^32)) by lia.
 change (8 mod 32) with 8;assert (Shift:0<=Z.shiftl (regs s 0%nat) 8<2^32) by (rewrite Z.shiftl_mul_pow2 by lia;lia).
 rewrite (Z.mod_small _ _ Shift);fold (packed (regs s 13%nat) (regs s 0%nat)).
 rewrite Z.mod_small by (rewrite packed_value by lia;lia).
 split;[reflexivity|split;[intros n N;unfold put;rewrite (proj2(Nat.eqb_neq 0 n) ltac:(lia));reflexivity|reflexivity]].
Qed.

Lemma saved_word pol e original s i r : well_formed original -> DecoderSpills.saved pol e original (mem s) ->
 nth_error DecoderSpills.registers i=Some r ->
 read_word (mem s) (DecoderSpills.top pol e-8*(1+Z.of_nat i))=regs original r.
Proof.
 intros W Saved N;assert(I:(i<5)%nat) by (change (i<length DecoderSpills.registers)%nat;apply (proj1(nth_error_Some _ _));congruence).
 rewrite <- (spilled_word _ (mem original) (DecoderSpills.top pol e) _ i r (proj1 W) N).
 apply preserved_read with (outside:=DecoderSpills.area pol e);[exact Saved|intros k K;unfold DecoderSpills.area;change (0<=k<8) in K;lia].
Qed.

Lemma returns pol e o original s c : placement e -> well_formed original ->
 regs s 5%nat=DecoderSpills.top pol e-8 -> DecoderSpills.saved pol e original (mem s) ->
 exists t,run 8 (ScalarBytes.fetch o text) (State (Running 228) s c)=Some(t,[]) /\
 loc t=Returned(word(read_word (mem original) (DecoderSpills.top pol e))) /\ regs(cpu_state t) 4%nat=DecoderSpills.top pol e+8 /\
 mem(cpu_state t)=mem s /\ regs(cpu_state t) 0%nat=regs s 0%nat /\
 forall r,In r DecoderSpills.registers -> regs(cpu_state t) r=regs original r.
Proof.
 intros P W BP Saved;set (sp:=DecoderSpills.top pol e) in *.
 destruct(Return.stack_ok _ P) as [[Lo Hi] _];assert (Bounds:100<=sp<2^64-8) by
   (unfold sp,DecoderSpills.top,common_top,Rows.frame,Return.sp in *;destruct pol;lia).
 assert (Back:read_word (mem s) sp=read_word (mem original) sp).
 { apply preserved_read with (outside:=fun x=>sp<=x<sp+8);[|intros k K;change (0<=k<8) in K;lia].
   intros x X;rewrite (Saved x) by (unfold DecoderSpills.area;fold sp;lia);apply outside_spill;right;lia. }
 eexists;split;[apply (InstructionRoute.checked _ _ _ (proj2 linked_code));reflexivity|].
 cbn [restore follow step loc cf cpu_state effective option_map flag with_zf pop caller_step stack_step
   set set_regs with_words apply_stack regs mem result_regs result_mem target_ip].
 unfold stack_top,advance_rsp,put;cbn [Nat.eqb];rewrite BP.
 repeat match goal with |- context[word ?a]=>first [rewrite (word_fits a ltac:(unfold word64 in *;lia))|fail 1] end.
 replace (sp-8+0+-32+8+8+8+8+8) with sp by ring.
 split;[now rewrite Back|split;[f_equal;ring|split;[reflexivity|split;[reflexivity|]]]].
 intros r Member;cbn [DecoderSpills.registers In] in Member;destruct Member as [<-|[<-|[<-|[<-|[<-|[]]]]]];cbn [Nat.eqb].
 all: repeat match goal with |-context[word ?a]=>rewrite (word_fits a ltac:(unfold word64 in *;lia)) end.
 all: match goal with |-read_word _ ?a=regs _ ?r =>
   let i:=eval vm_compute in (match r with 5%nat=>0%nat|3%nat=>1%nat|12%nat=>2%nat|13%nat=>3%nat|_=>4%nat end) in
   replace a with (DecoderSpills.top pol e-8*(1+Z.of_nat i)) by (fold sp;ring);exact (saved_word _ _ _ _ i r W Saved eq_refl) end.
Qed.
