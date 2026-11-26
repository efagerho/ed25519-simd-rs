From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.VectorProcedure
 execution.ScalarBytes execution.MappedFetch execution.WordBounds memory.MemoryGeometry.
From Ed25519Simd.Decode Require Kernels Program DecoderBytes HelperBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode.
From Ed25519Simd.Decode Require DecoderKernel.

Import ListNotations. Local Open Scope Z_scope.
Module K:=DecoderKernel.
From Ed25519Simd.Decode Require NativeProduct.
Definition section:=NativeProduct.section.
Definition native:=NativeProduct.native.
Definition columns:=NativeProduct.columns.
Definition product:=NativeProduct.product.
Definition area e := Area (sp e-16384) (sp e).
Section Linked.
Variables (pol:policy) (bias:Z) (e:cpu).
Hypothesis P:placement e.
Hypothesis Loaded:loaded pol bias (mem e) (writable e).
Local Notation spec := (contract e (writable e) (area e)).
Local Notation h := (bias+HelperBytes.address).
Local Notation d := (bias+DecoderBytes.address).
Lemma stack : VectorProcedure.stack_ok (area e) (writable e).
Proof.
 destruct(Return.stack_ok _ P) as [[L H] _];unfold VectorProcedure.stack_ok,area;cbn [bottom ceiling].
 split;[exact L|split;[lia|intros x X;left;unfold span,region,area in *;cbn [bottom ceiling] in *;lia]].
Qed.
Lemma placed b : available e (writable e) (bias+section b) (K.image b).
Proof.
 assert (S:forall a t,In (a,t) (children pol) -> available e (writable e) (bias+a) t).
 { intros a t I;split;[exact (proj2(symbols _ _ _ _ Loaded _ _ I))|].
   intros x X;apply (immutable _ _ _ _ Loaded);left;exists a,t;auto. }
 destruct b;apply S;apply helper_in || apply decode_in.
Qed.
Lemma calc b : spec (bias+section b+K.start b) (bias+section b+K.stop b) 0 (K.body b) (native bias b).
Proof. apply block;[apply placed|apply K.bytes|destruct b;vm_compute;reflexivity]. Qed.
Lemma address_fits b off : 0<=off<Z.of_nat(length (K.image b)) -> word64(bias+section b+off).
Proof.
 assert (S:In(section b,K.image b)(children pol)) by (destruct b;apply helper_in || apply decode_in).
 destruct(proj1(symbols _ _ _ _ Loaded _ _ S));unfold word64;lia.
Qed.
Lemma after_seed : spec (h+0xbfc) (h+0xca3) 8 (K.body K.Convolve++K.body K.Fold)
 (then_run (wrapped h HelperBytes.symbol_bytes h HelperBytes.symbol_bytes (native bias K.Convolve)) (native bias K.Fold)).
Proof. apply NativeProduct.after_seed;auto using stack,placed,address_fits. Qed.
Lemma check_product : spec (d+0xa79) (d+0xadd) 16 (Kernels.product Ed25519Simd.Decode.Program.code) (product bias).
Proof. apply NativeProduct.check_product;auto using stack,placed,address_fits. Qed.
End Linked.
From Ed25519Simd.Decode Require Power.
From Curve25519 Require Import Radix51 Field.
From Machine Require Import isa.Instructions.
From Machine Require Import isa.VectorMoves execution.InstructionRoute execution.AlignedRows memory.ByteMemory.
Definition dbase bias:=bias+DecoderBytes.address.
Definition rhs_at s j i:=read_word (mem s) (regs s 8%nat+64*Z.of_nat i+8*Z.of_nat j).
Definition arguments s j i := if ((5<=?i)&&(i<?10))%nat then rhs_at s j (i-5)%nat else vectors s j i.
Definition readable (args:nat->nat->Z) s := regs s 8%nat mod 64=0 /\ fits64 (regs s 8%nat) 320 /\
 forall j i,arguments s j i=args j i.
Definition multiplied args (_ t:cpu) := forall j i,vectors t j i=
 Instructions.run no_read (Kernels.product NativeProduct.kernel) (args j) i.
Definition multiply_body bias:=then_run (segment (dbase bias) DecoderBytes.symbol_bytes 5) (product bias).
Definition multiply_call bias:=wrapped (dbase bias) DecoderBytes.symbol_bytes (dbase bias) DecoderBytes.symbol_bytes
 (multiply_body bias).
Lemma rhs_bytes : linked DecoderBytes.symbol_bytes (AlignedRows.route false 0xa57 5 8 0 5).
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Lemma multiply pol bias e args : placement e -> loaded pol bias (mem e) (writable e) ->
 guarded e (writable e) (area e) (dbase bias+0xa57) (dbase bias+0xadd) 16
 (readable args) (multiplied args) (multiply_body bias).
Proof.
 intros P M p [Al [Fit Args]] PC Acc Space;set (s:=machine p) in *;set (o:=dbase bias) in *.
 destruct(AlignedRows.loads o _ 5 0xa57 5 8 0 (regs s 8%nat) s (carry p) rhs_bytes
   (Z.add_0_r _) Al Fit) as [v [Run [Regs [Mem [_ [Rows Other]]]]]].
 destruct(placed pol bias e M K.Carry) as [Image Sep].
 destruct(at_segment _ _ _ o DecoderBytes.symbol_bytes _ _ _ _ Acc PC (image_after _ _ _ _ _ Acc Image Sep) Sep Run (Forall_nil _)) as [Load A].
 set (mid:=LinkedRun.finish o p (State (Running 0xa79) v (carry p),[])) in *.
 assert (View:forall j i,vectors v j i=args j i).
 { intros j i;rewrite <-Args;unfold arguments;destruct (Nat.leb_spec 5 i), (Nat.ltb_spec i 10);cbn;
   try (rewrite Other by lia;reflexivity).
   replace i with (5+(i-5))%nat at 1 by lia;rewrite Rows by lia;reflexivity. }
 destruct(check_product pol bias e P M mid eq_refl A
    ltac:(change (room (area e) 16 v);unfold room;rewrite Regs;exact Space)) as [q [Product [At Paid G F V]]].
 exists q;split;[unfold multiply_body,then_run;fold o;rewrite Load;exact Product|].
 constructor;[exact At|exact Paid| | |].
 - intros r;rewrite G;exact (f_equal (fun rs=>rs r) Regs).
 - intros x X;rewrite F;[exact (f_equal (fun m=>m x) Mem)|].
   change (~(regs v 4%nat-16<=x<regs v 4%nat));rewrite Regs;exact X.
 - intros j i;rewrite V;apply Instructions.run_ext;[reflexivity|apply View].
Qed.

Theorem call_at pol bias e pc args : placement e -> loaded pol bias (mem e) (writable e) ->
 0<=pc -> pc+5<2984 -> ScalarBytes.decode (skipn (Z.to_nat pc) DecoderBytes.symbol_bytes)=
 Some(5%nat,CallRelative(0xa57-(pc+5))) ->
 guarded e (writable e) (area e) (dbase bias+pc) (dbase bias+(pc+5)) 24
 (fun s=>readable args (push s (dbase bias+(pc+5)))) (multiplied args) (multiply_call bias).
Proof.
 intros P M Pos In Call;set (o:=dbase bias) in *.
 apply (invoke_effect _ _ _ o _ pc (0xa57-(pc+5)) o _ 0xadd 16 (readable args) (multiplied args) (multiplied args)).
 - intros s t V;exact V.
 - apply stack,P.
 - lia.
 - exact (placed pol bias e M K.Carry).
 - exact (placed pol bias e M K.Carry).
 - exact Pos.
 - exact Call.
 - lia.
 - vm_compute;reflexivity.
 - replace (o+(pc+5)+(0xa57-(pc+5))) with (o+0xa57) by ring.
   exact (address_fits pol bias e M K.Carry 0xa57 ltac:(vm_compute;split;discriminate || reflexivity)).
 - apply (address_fits pol bias e M K.Carry);change (0<=pc+5<2984);lia.
 - replace (o+(pc+5)+(0xa57-(pc+5))) with (o+0xa57) by ring;exact (multiply pol bias e args P M).
Qed.
