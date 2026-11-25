From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch abi.SysV
 memory.MemoryGeometry memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.Sha512Challenge Require Execution Output Frame Audit Object ObjectBytes LiteralBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require HashLayout CallWrites Digest.
Import ListNotations. Local Open Scope Z_scope.

Definition code:=Sha512Challenge.ObjectBytes.symbol_bytes.
Definition literal:=Sha512Challenge.LiteralBytes.address.
Definition execute bias q:=Sha512Challenge.Execution.run HashEntry.callee
 (snapshot (mem(machine q)) (ip q) (length code)) bias literal (machine q).
Definition history bias q:=log q++CallWrites.hash_events_at bias (machine q).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition row:=HashLayout.row.
Definition field e j:=descriptor (mem e) (regs e 7%nat) (BatchWindow.row e j).
Definition messages_immutable e:=forall j k,(j<8)%nat -> 0<=k<field e j 24 -> ~writable e (field e j 16+k).

Lemma challenge_bytes bias pc e p q : placement e -> messages_immutable e -> PreparedInputs.encodings e (machine p) ->
 HashEntry.entry bias pc e p q -> forall j,(j<8)%nat ->
 Sha512Challenge.Output.challenge_input (machine q) j=
 r_bytes(row e j)++key_bytes(row e j)++(if HashLengths.enabled e (machine p) j then message(row e j) else []).
Proof.
 intros P Borrow Enc Q j J;destruct(HashEntry.args _ _ _ _ _ Q) as [_ [_ [SI [DX _]]]].
 assert (Data:PreparedInputs.encodings e (machine q)).
 { eapply PreparedInputs.keep_encodings;[|exact Enc];intros x X;apply (HashEntry.other_bytes _ _ _ _ _ Q).
   pose proof(scratch_stack _ P);unfold PreparedInputs.prefix,disjoint,span,Rows.frame,sp in *;lia. }
 assert (Bytes:forall (sig:bool),octets (mem(machine q)) ((if sig then scratch e+256 else scratch e)+32*Z.of_nat j) 32=
    octets (mem e) (ScalarInputs.encoding_ptr e j sig) 32).
 { intros sig;apply Hash.octets_ext;intros k K;specialize(Data j sig k J K);unfold PrepareCopies.dest in Data;destruct sig.
   - replace (scratch e+256+32*Z.of_nat j+k) with (scratch e+32*Z.of_nat j+256+k) by ring;exact Data.
   - rewrite Z.add_0_r in Data;exact Data. }
 unfold Sha512Challenge.Output.challenge_input;rewrite SI,DX,(HashEntry.messages _ _ _ _ _ Q j J),(HashEntry.lengths _ _ _ _ _ Q j J).
 change (octets (mem(machine q)) (scratch e+256+32*Z.of_nat j) 32++octets (mem(machine q)) (scratch e+32*Z.of_nat j) 32++
    octets (mem(machine q)) (field e j 16) (Z.to_nat(HashLengths.length e (machine p) j))=
    r_bytes(row e j)++key_bytes(row e j)++(if HashLengths.enabled e (machine p) j then message(row e j) else [])).
 rewrite (Bytes true),(Bytes false);f_equal;f_equal;unfold HashLengths.length;destruct(HashLengths.enabled e (machine p) j);[|reflexivity].
 apply Hash.octets_ext;intros k K.
 pose proof(read_word_bound (mem e) (regs e 7%nat+40*Z.of_nat(BatchWindow.row e j)+24) (proj2(proj2(initial_cpu _ P)))) as Word.
 change (WordBounds.word64 (field e j 24)) in Word;change (0<=k<Z.of_nat(Z.to_nat(field e j 24))) in K;
 unfold WordBounds.word64 in Word;rewrite Z2Nat.id in K by lia.
 destruct(HashEntry.writes _ _ _ _ _ Q) as [W M];rewrite M;apply (WriteTrace.frame _ _ W),(Borrow j k J K).
Qed.

Record returned pol bias origin e q r:Prop:=Returned {
 back:Sha512Challenge.Execution.return_ip r=origin+458;
 stack:Sha512Challenge.Execution.return_sp r=Rows.frame e;
 saved:forall g,In g sysv_saved -> Sha512Challenge.Execution.saved_register r g=Some(regs(machine q) g);
 writes:confined (writable e) (history bias q);
 bytes:byte_memory (Sha512Challenge.Execution.after r);
 frame:preserved (fun x=>x<sp e-16384 \/ Rows.frame e+512<=x) (mem(machine q)) (Sha512Challenge.Execution.after r);
 replayed:forall x,Sha512Challenge.Execution.after r x=replay (mem e) (history bias q) x;
 digest:forall j,(j<8)%nat -> HashLayout.eligible pol e j ->
   Scalar.ScalarSpec.lane_input (buffer_words (Sha512Challenge.Execution.after r) (Rows.frame e)) j=
   little_endian (SHA512.Spec.sha512 (r_bytes(row e j)++key_bytes(row e j)++message(row e j)))
}.

Theorem checked pol bias pc e p q : placement e -> loaded pol bias (mem e) (writable e) ->
 (0<BatchWindow.remaining e)%nat -> Loop.spatial (HashLayout.chunk pol e bias) -> messages_immutable e ->
 HashLayout.active pol e -> HashLayout.flags pol e (machine p) -> PreparedInputs.encodings e (machine p) ->
 HashEntry.entry bias pc e p q -> exists r,execute bias q=Some r /\ returned pol bias (bias+pc) e q r.
Proof.
 intros P I N Space Borrow Live Flags Enc Q;set (s:=machine q).
 pose proof(HashLayout.placement _ _ _ _ _ _ N Space Live Flags Q) as Layout.
 pose proof(HashEntry.writes _ _ _ _ _ Q) as Prefix;pose proof(HashEntry.words _ _ _ _ _ Q) as W.
 destruct(mapped_now _ _ _ I _ _ _ Prefix (HashEntry.in_image pol)) as [Text _].
 assert (L:In (literal,Sha512Challenge.LiteralBytes.symbol_bytes) (children pol)) by (apply in_or_app;left;do 4 right;left;reflexivity).
 destruct(mapped_now _ _ _ I _ _ _ Prefix L) as [Data _].
 destruct(Sha512Challenge.Audit.returns_correct _ _ _ _ Sha512Challenge.Object.assembled_sha512_challenge_correct bias s Layout W Data)
 as [r [Run [PC [SP [G [B [Frame Digests]]]]]]].
 destruct(Sha512Challenge.Audit.write_footprint _ _ _ _ Sha512Challenge.Object.assembled_sha512_challenge_correct bias s Layout) as [Safe Replay].
 destruct(HashEntry.args _ _ _ _ _ Q) as [Top [Dst _]].
 assert (StackWrites:confined (writable e) (CallWrites.hash_events_at bias s)).
 { eapply Forall_impl;[|exact Safe];intros w H x X;specialize(H x X);left.
   unfold Sha512Challenge.Frame.writable,Sha512Challenge.Frame.frame,Sha512Challenge.Frame.sp,Sha512Challenge.Frame.dst,s in H.
   rewrite Top,Dst in H;pose proof(Z.mod_pos_bound (Rows.frame e-8-8) 64 ltac:(lia));unfold Rows.frame,span,sp in *;lia. }
 exists r;split;[unfold execute;rewrite (HashEntry.target _ _ _ _ _ Q),snapshot_mapped by exact Text;exact Run|constructor].
 - rewrite PC;unfold Sha512Challenge.Frame.sp,s;rewrite Top;apply (HashEntry.back _ _ _ _ _ Q).
 - rewrite SP;unfold Sha512Challenge.Frame.sp,s;rewrite Top;ring.
 - exact G.
 - apply Forall_app;split;[exact (proj1 Prefix)|exact StackWrites].
 - exact B.
 - intros x X;apply Frame;unfold Sha512Challenge.Frame.writable,Sha512Challenge.Frame.frame,Sha512Challenge.Frame.sp,Sha512Challenge.Frame.dst,s;
   rewrite Top,Dst;pose proof(Z.mod_pos_bound (Rows.frame e-8-8) 64 ltac:(lia));unfold Rows.frame,sp in *;lia.
 - intro x;unfold history;rewrite replay_app,(Replay r Run x);apply replay_equal,(proj2 Prefix).
 - intros j J On;pose proof(Digest.sha_to_scalar s _ j J Digests) as Scalar.
   pose proof(challenge_bytes _ _ _ _ _ P Borrow Enc Q j J) as Input.
   rewrite (proj2(Flags j J) On) in Input.
   unfold s in Scalar;rewrite Input,Dst in Scalar;exact Scalar.
Qed.
End Iteration.
