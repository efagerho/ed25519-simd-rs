From Coq Require Import List ZArith Lia Bool.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory.
From Curve25519.group Require Import PrimeField Affine Decompression.
From Ed25519Simd.VerifyBatch Require Import Policy Loop.
From Ed25519Simd.VerifyBatch Require HashEntry StrictReturn.
Local Open Scope Z_scope.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition chunk pol e bias:=make_chunk e pol bias BatchWindow.first (BatchWindow.remaining e) zero_loc.
Lemma index e j : (0<BatchWindow.remaining e)%nat -> (j<8)%nat ->
 Rows.row_no BatchWindow.first (Nat.min (BatchWindow.remaining e) 8) j=BatchWindow.row e j.
Proof.
 intros N J;unfold Rows.row_no,BatchWindow.row,ChunkRows.lane;apply f_equal.
 set(n:=BatchWindow.remaining e) in *;destruct (Nat.lt_ge_cases n 8) as [Short|Full].
 - rewrite Nat.min_l by lia;do 8 (destruct n as [|n];[do 8 (destruct j as [|j];[try reflexivity;lia|]);lia|]);lia.
 - rewrite Nat.min_r by lia;change (j=Nat.min j (n-1));symmetry;apply Nat.min_l;lia.
Qed.
Definition row e j:=read_input (mem e) (regs e 7%nat) (BatchWindow.row e j).
Definition eligible pol e j:=Lane.eligible_input pol (row e j).
Definition active pol e:=exists j,(j<8)%nat /\ eligible pol e j.
Definition flags pol e s:=forall j,(j<8)%nat -> (HashLengths.enabled e s j=true <-> eligible pol e j).

Lemma original_row pol e bias j : (0<BatchWindow.remaining e)%nat -> (j<8)%nat ->
 Prepare.input_at (chunk pol e bias) j=row e j.
Proof. intros N J;unfold Prepare.input_at,Rows.original_row,chunk,make_chunk;cbn [Prepare.entry Prepare.first Prepare.live];now rewrite index. Qed.
Lemma candidate e j : EligibleLanes.candidate e j <-> eligible Zip215 e j.
Proof.
 unfold EligibleLanes.candidate,eligible,Lane.eligible_input;rewrite !RootDecision.signed_encoding.
 unfold BatchDecode.original_encoding,ScalarInputs.original_scalar,row;cbn [Lane.strict].
 split;[intros [S [[a A] R]];split;[exact S|split;[exact R|exists a;split;[exact A|discriminate]]]|].
 intros [S [R [a [A _]]]];split;[exact S|split;[now exists a|exact R]].
Qed.
Lemma candidate_of pol e j : eligible pol e j -> EligibleLanes.candidate e j.
Proof.
 rewrite candidate;destruct pol;[trivial|intros [S [R [A [DA Strong]]]];split;[exact S|split;[exact R|exists A;split;[exact DA|discriminate]]]].
Qed.
Lemma zip_flags bias origin e q : PreparedReturn.result Zip215 bias origin e q -> flags Zip215 e (machine q).
Proof. intros Q j J;unfold HashLengths.enabled;rewrite negb_true_iff,Z.eqb_neq,<-candidate;
 destruct(PreparedReturn.flags _ _ _ _ _ Q j J) as [Bit On];intuition lia. Qed.
Lemma strict_flags origin e p q : StrictReturn.result origin e p q -> flags Dalek e (machine q).
Proof.
 intros Q j J;unfold HashLengths.enabled;rewrite negb_true_iff,Z.eqb_neq;destruct(StrictReturn.filtered _ _ _ _ Q j J) as [Bit On].
 change (mem(machine q)(FilterFlags.flag_ptr e+Z.of_nat j)<>0 <-> FilterMeaning.eligible e j);
 rewrite <-(StrictReturn.strong_lane _ _ _ _ Q j J);intuition lia.
Qed.

Lemma lengths pol bias pc e p q : (0<BatchWindow.remaining e)%nat -> Prepare.placement (chunk pol e bias) ->
 active pol e -> flags pol e (machine p) -> HashEntry.entry bias pc e p q ->
 forall j,(j<8)%nat -> Sha512Challenge.Output.message_length (machine q) j=Hash.masked_length (chunk pol e bias) j.
Proof.
 intros N Place [j0 [J0 Yes]] Prep Q;set (c:=chunk pol e bias) in *.
 assert (Ready:Prepare.ready c=true).
 { apply (proj2(proj1(Prepare.prepared _ Place)));exists j0;split;[exact J0|].
   apply (proj2(Prepare.eligibility _ _ Place J0));unfold c;rewrite original_row by assumption;exact Yes. }
 intros j J;rewrite (HashEntry.lengths _ _ _ _ _ Q j J).
 assert (EQ:HashLengths.enabled e (machine p) j=Prepare.enabled c j).
 { apply eq_true_iff_eq;rewrite (Prep j J),(Prepare.enabled_ok _ _ Place Ready J).
   unfold c;rewrite original_row by assumption;reflexivity. }
 unfold HashLengths.length,Hash.masked_length;rewrite EQ;destruct(Prepare.enabled c j);[|reflexivity].
 unfold Hash.src,Rows.source,c,chunk,make_chunk;cbn [Prepare.entry Prepare.first Prepare.live];now rewrite index.
Qed.

Theorem placement pol bias pc e p q : (0<BatchWindow.remaining e)%nat -> Loop.spatial (chunk pol e bias) ->
 active pol e -> flags pol e (machine p) -> HashEntry.entry bias pc e p q ->
 Sha512Challenge.Frame.placement (machine q) (bias+HashEntry.callee)
   (Z.of_nat(length Sha512Challenge.ObjectBytes.symbol_bytes)) (bias+Sha512Challenge.LiteralBytes.address).
Proof.
 intros N [Place [Geo [[Frame _] _]]] Live Done Q;set (c:=chunk pol e bias) in *.
 pose proof(lengths _ _ _ _ _ _ N Place Live Done Q) as Sz;fold c in Sz.
 destruct(HashEntry.args _ _ _ _ _ Q) as [SP [DI [SI [DX [CX R8]]]]].
 assert (S:Sha512Challenge.Frame.sp (machine q)=Sha512Challenge.Frame.sp (Hash.hash_entry c)) by exact SP.
 assert (D:Sha512Challenge.Frame.dst (machine q)=Sha512Challenge.Frame.dst (Hash.hash_entry c)) by exact DI.
 assert (F:Sha512Challenge.Frame.frame (machine q)=Sha512Challenge.Frame.frame (Hash.hash_entry c)) by (unfold Sha512Challenge.Frame.frame;now rewrite S).
 assert (Source:forall a n,Sha512Challenge.Frame.source (Hash.hash_entry c) a n -> Sha512Challenge.Frame.source (machine q) a n)
    by (intros a n;unfold Sha512Challenge.Frame.source;now rewrite D,F,S).
 destruct Frame as [Stack Out Code Tables Slices];constructor.
 - now rewrite S,F.
 - now rewrite D,S,F.
 - destruct Code as [A [B C]];split;[apply Source,A|split;[apply Source,B|exact C]].
 - destruct Tables as [A [B [C E]]];rewrite SI,DX,CX,R8;split;[apply Source,A|split;[apply Source,B|split;apply Source;assumption]].
 - intros j J;specialize(Slices j J);rewrite (Sz j J),<-(Hash.hash_message_length c j Place J).
   rewrite (HashEntry.messages _ _ _ _ _ Q j J).
   replace (descriptor (mem e) (regs e 7%nat) (BatchWindow.row e j) 16) with (Hash.src c j 16)
    by (unfold Hash.src,Rows.source,c,chunk,make_chunk;cbn [Prepare.entry Prepare.first Prepare.live];now rewrite index).
   rewrite <-(Hash.hash_message_pointer c j Place Geo J);split;[exact (proj1 Slices)|apply Source,(proj2 Slices)].
Qed.
End Iteration.
