From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.LinkedRun execution.MappedFetch memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.SignatureScalar Require Object ObjectBytes OrderBytes Audit Program.
From Curve25519 Require Import Scalar.
From ProofArithmetic Require Import Radix.
From Ed25519Simd.VerifyBatch Require Import Policy Digest Rows Return LoadedImage PrepareNative.
Local Open Scope Z_scope.

Definition sig_ptr e j := descriptor (mem e) (regs e 7%nat) j 8.
Definition borrowed e := forall j,(j<Scatter.count e)%nat ->
 let a:=sig_ptr e j in fits64 a 64 /\ (forall x,a<=x<a+64 -> ~writable e x).
Definition original_scalar e j := little_endian (s_bytes (read_input (mem e) (regs e 7%nat) j)).
Definition matrix e s := forall j,(j<8)%nat ->
 read_word (mem s) (Rows.frame e+576+8*Z.of_nat j)=sig_ptr e j.

Definition recoded e s := 0<=regs s 0%nat<256 /\ forall j,(j<8)%nat ->
 let x:=original_scalar e j in let ds:=SignatureScalar.Audit.digits s (scratch e+512) j in
 (Z.testbit (regs s 0%nat) (Z.of_nat j)=true <-> x<L) /\
 (if x <? L then Forall (fun d=> -8<=d<8) ds /\ number 16 ds=x else ds=repeat 0 64).

Lemma apart a n b m : 0<n -> 0<m -> (forall x,b<=x<b+m -> ~(a<=x<a+n)) -> disjoint a n b m.
Proof.
 intros N M Ex;unfold disjoint. destruct (Z_le_dec (a+n) b);[auto|right].
 destruct (Z_le_dec (b+m) a);[auto|]. exfalso;apply (Ex (Z.max a b));lia.
Qed.

Definition code := SignatureScalar.ObjectBytes.symbol_bytes.
Definition size := Z.of_nat (length code).
Lemma scalar_in pol : In (PrepareNative.scalar,code) (children pol).
Proof. apply in_or_app;left;right;left;reflexivity. Qed.
Lemma order_in pol : In (OrderBytes.address,OrderBytes.symbol_bytes) (children pol).
Proof. apply in_or_app;left;do 2 right;left;reflexivity. Qed.

Theorem from_call pol bias e child masks top ip s :
 Return.placement e -> loaded pol bias (mem e) (writable e) -> accounted e (writable e) child ->
 well_formed (machine child) -> sp e-1200<=top<=sp e-1000 ->
 regs(machine child) 7%nat=scratch e+512 -> regs(machine child) 6%nat=top-104 ->
 regs(machine child) 4%nat=top-112 -> borrowed e -> (8<=Scatter.count e)%nat ->
 (forall j,(j<8)%nat -> SignatureScalar.Audit.ptr (machine child) j=word(32+sig_ptr e j)) ->
 SignatureScalar.Program.run PrepareNative.scalar size OrderBytes.address bias (machine child) masks=(ip,s) ->
 recoded e s.
Proof.
 intros Place Image Prev Words Top Dst Src SP Borrow Full Ptr Run.
 assert (Pointers: forall j,(j<8)%nat -> SignatureScalar.Audit.ptr (machine child) j=sig_ptr e j+32).
 { intros j J;rewrite Ptr by exact J;destruct (Borrow j ltac:(lia)) as [[Lo Hi] _].
   rewrite word_fits by (unfold word64;lia);ring. }
 assert (Source:forall a n, 0<n -> fits64 a n ->
   (forall x,a<=x<a+n -> ~writable e x) -> SignatureScalar.Audit.source (machine child) a n).
 { intros a n N Fit Away;split;[exact Fit|]. rewrite Dst;apply apart;[lia|exact N|].
   intros x X In;apply (Away x X);right;left;unfold span;lia. }
 assert (Code: forall a bytes, In (a,bytes) (children pol) -> 0<Z.of_nat(length bytes) ->
   SignatureScalar.Audit.source (machine child) (bias+a) (Z.of_nat(length bytes))).
 { intros a bytes I N;apply Source;[exact N|exact (proj1(symbols _ _ _ _ Image _ _ I))|].
   intros x X;apply (immutable _ _ _ _ Image);left;exists a,bytes;auto. }
 destruct (stack_ok _ Place) as [[Lo Hi] _].
 assert (P:SignatureScalar.Audit.placement (machine child) (bias+PrepareNative.scalar) size (bias+OrderBytes.address)).
 { constructor.
   - rewrite Dst;destruct(scratch_ok _ Place) as [[SL SH] _];unfold fits64;lia.
   - exact (Code _ _ (scalar_in _) ltac:(vm_compute;reflexivity)).
   - exact (Code _ _ (order_in _) ltac:(vm_compute;reflexivity)).
   - rewrite Src;split;[unfold fits64;lia|rewrite Dst;destruct(scratch_stack _ Place);unfold disjoint;lia].
   - intros j J;rewrite Pointers by exact J;destruct (Borrow j ltac:(lia)) as [[A U] K].
     apply Source;[lia|unfold fits64;lia|intros x X;apply K;lia].
   - rewrite SP;split;[unfold fits64;lia|rewrite Dst;destruct(scratch_stack _ Place);unfold disjoint;lia].
   - rewrite SP;lia. }
 assert (Literal: MappedFetch.mapped (mem(machine child)) (bias+OrderBytes.address) OrderBytes.symbol_bytes).
 { eapply image_after;[exact Prev|exact (proj2(symbols _ _ _ _ Image _ _ (order_in _)))|].
   intros x X;apply (immutable _ _ _ _ Image);left;eexists _,_;split;[apply order_in|exact X]. }
 pose proof (SignatureScalar.Audit.returns_correct _ _ _ _ SignatureScalar.Object.assembled_signature_scalar_correct
     bias (machine child) masks P Words Literal) as [_ H]. fold code in H;fold size PrepareNative.scalar in H.
 rewrite Run in H;destruct H as [_ [_ [_ [_ [_ [Mask Result]]]]]]. split;[exact Mask|].
 intros j J;specialize(Result j J);cbv zeta in Result|-*;rewrite Dst in Result.
 assert (Original:SignatureScalar.Audit.scalar (machine child) j=original_scalar e j).
 { unfold SignatureScalar.Audit.scalar;rewrite Pointers by exact J;unfold original_scalar,read_input;cbn [s_bytes].
   rewrite read_octets by exact (proj2 (proj2 (initial_cpu _ Place)));fold (sig_ptr e j).
   apply preserved_read with (outside:=fun x=>~writable e x).
   - destruct Prev as [W M];intros x X;rewrite M;apply (WriteTrace.frame _ _ W),X.
   - intros k K;change (0<=k<32) in K;destruct (Borrow j ltac:(lia)) as [_ Away];apply Away;lia. }
 now rewrite Original in Result.
Qed.

Lemma zero_rejects pol e s : recoded e s -> regs s 0%nat mod 2^32=0 ->
 forall j,(j<8)%nat -> ~signature_accepts pol (read_input (mem e) (regs e 7%nat) j).
Proof.
 intros [Mask Bits] Zero j J [Valid _]. rewrite Z.mod_small in Zero by lia.
 change (original_scalar e j<L) in Valid;apply (proj2 (proj1 (Bits j J))) in Valid.
 rewrite Zero,Z.bits_0 in Valid;discriminate.
Qed.
