From Coq Require Import List ZArith Lia Bool.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory.
From Curve25519.group Require Import PrimeField Affine Decompression.
From Ed25519Simd.VerifyBatch Require Import Policy Loop.
From Ed25519Simd.VerifyBatch Require HashEntry.
Local Open Scope Z_scope.

Definition chunk e bias:=make_chunk e Zip215 bias 0 (Scatter.count e) zero_loc.
Lemma index e j : (0<Scatter.count e)%nat -> (j<8)%nat ->
 Rows.row_no 0 (Nat.min (Scatter.count e) 8) j=TailCopy.row_index e j.
Proof.
 intros N J;unfold Rows.row_no,TailCopy.row_index;rewrite Nat.add_0_l.
 destruct (Nat.lt_ge_cases (Scatter.count e) 8) as [Short|Full].
 - rewrite Nat.min_l by lia;remember (Scatter.count e) as n;clear Heqn.
   do 8 (destruct n as [|n];[do 8 (destruct j as [|j];[try reflexivity;lia|]);lia|]);lia.
 - rewrite Nat.min_r by lia;change (j=Nat.min j (Scatter.count e-1));symmetry;apply Nat.min_l;lia.
Qed.
Lemma signed_encoding sig e j : RootDecision.decodes sig e j <->
 exists a,Policy.decodes (BatchDecode.original_encoding sig e j) a.
Proof.
 set (w:=BatchDecode.original_encoding sig e j). set (v:=residue (w mod 2^255)).
 change ((exists x,on_curve x v) <-> exists a,y a=v /\ has_sign (Z.testbit w 255) (x a)).
 split.
 - intros [u U];pose proof(decode_correct v (Z.testbit w 255)) as D.
   destruct(decode v (Z.testbit w 255)) as [z|];[destruct D as [C S];exists (Point z v C);auto|contradiction (D u U)].
 - intros [a [Y S]];exists (x a);rewrite <-Y;apply on_edwards.
Qed.
Lemma eligible e bias j : (0<Scatter.count e)%nat -> (j<8)%nat ->
 EligibleLanes.candidate e j <-> Lane.eligible_input Zip215 (Prepare.input_at (chunk e bias) j).
Proof.
 intros N J;unfold EligibleLanes.candidate,Lane.eligible_input;rewrite !signed_encoding.
 unfold Prepare.input_at,Rows.original_row,chunk,make_chunk;cbn [Prepare.entry Prepare.first Prepare.live].
 rewrite index by assumption;unfold BatchDecode.original_encoding,ScalarInputs.original_scalar;cbn [Lane.strict].
 split;[intros [S [[a A] R]];split;[exact S|split;[exact R|exists a;split;[exact A|discriminate]]]|].
 intros [S [R [a [A _]]]];split;[exact S|split;[now exists a|exact R]].
Qed.

Lemma lengths bias pc e p q : (0<Scatter.count e)%nat -> Prepare.placement (chunk e bias) ->
 (exists j,(j<8)%nat /\ EligibleLanes.candidate e j) ->
 PreparedReturn.result Zip215 bias (bias+pc) e p -> HashEntry.entry bias pc e p q ->
 forall j,(j<8)%nat -> Sha512Challenge.Output.message_length (machine q) j=Hash.masked_length (chunk e bias) j.
Proof.
 intros N Place [j0 [J0 Yes]] Prep Q;set (c:=chunk e bias) in *.
 assert (Ready:Prepare.ready c=true).
 { apply (proj2(proj1(Prepare.prepared _ Place)));exists j0;split;[exact J0|].
   apply (proj2(Prepare.eligibility _ _ Place J0)),(proj1(eligible _ _ _ N J0)),Yes. }
 intros j J;rewrite (HashEntry.lengths _ _ _ _ _ Q j J).
 assert (EQ:HashLengths.enabled e (machine p) j=Prepare.enabled c j).
 { apply eq_true_iff_eq;unfold HashLengths.enabled;rewrite negb_true_iff,Z.eqb_neq.
   destruct(PreparedReturn.flags _ _ _ _ _ Prep j J) as [Bit On].
   pose proof (Prepare.enabled_ok _ _ Place Ready J) as Enabled.
   change (Prepare.enabled c j=true <-> Lane.eligible_input Zip215 (Prepare.input_at (chunk e bias) j)) in Enabled.
   rewrite Enabled,<-(eligible e bias j N J);intuition lia. }
 unfold HashLengths.length,Hash.masked_length;rewrite EQ;destruct(Prepare.enabled c j);[|reflexivity].
 unfold Hash.src,Rows.source,c,chunk,make_chunk;cbn [Prepare.entry Prepare.first Prepare.live];now rewrite index.
Qed.

Theorem placement bias pc e p q : (0<Scatter.count e)%nat -> Loop.spatial (chunk e bias) ->
 (exists j,(j<8)%nat /\ EligibleLanes.candidate e j) ->
 PreparedReturn.result Zip215 bias (bias+pc) e p -> HashEntry.entry bias pc e p q ->
 Sha512Challenge.Frame.placement (machine q) (bias+HashEntry.callee)
   (Z.of_nat(length Sha512Challenge.ObjectBytes.symbol_bytes)) (bias+Sha512Challenge.LiteralBytes.address).
Proof.
 intros N [Place [Geo [[Frame _] _]]] Live Done Q;set (c:=chunk e bias) in *.
 pose proof(lengths _ _ _ _ _ N Place Live Done Q) as Sz;fold c in Sz.
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
   replace (descriptor (mem e) (regs e 7%nat) (TailCopy.row_index e j) 16) with (Hash.src c j 16)
    by (unfold Hash.src,Rows.source,c,chunk,make_chunk;cbn [Prepare.entry Prepare.first Prepare.live];now rewrite index).
   rewrite <-(Hash.hash_message_pointer c j Place Geo J);split;[exact (proj1 Slices)|apply Source,(proj2 Slices)].
Qed.
