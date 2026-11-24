From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.Sha512Challenge Require Output Frame Execution Audit Object ObjectBytes LiteralBytes.
From Ed25519Simd.PrepareChunk Require Staging.
From Ed25519Simd.VerifyBatch Require Import Policy Digest Rows Prepare.
Import ListNotations. Local Open Scope Z_scope.

Definition stack_base c := frame(entry c).
Definition scratch c := Staging.scratch(p c).
Definition src c j := source (entry c) (first c) (live c) j.
Definition masked_length c j := if enabled c j then src c j 24 else 0.
Definition prefixes c := write_bytes (Staging.original(p c)) (scratch c) 512
  (fun d=>Staging.staged (p c) (scratch c+d)).
Definition hash_memory c := Frame.matrix (prefixes c) (stack_base c+704) 1
  (fun _ j=>masked_length c j).
Definition hash_entry c := with_words (entry c) (fun r=>match r with
 | 4%nat=>stack_base c-8 | 7%nat=>stack_base c | 6%nat=>scratch c+256
 | 2%nat=>scratch c | 1%nat=>stack_base c+640 | 8%nat=>stack_base c+704
 | _=>regs(entry c) r end) (hash_memory c).

Definition stack_separate c := disjoint (stack_base c+512) 256 (scratch c) 512.
Definition messages_separate c := forall j,(j<8)%nat ->
 let a:=src c j 16 in let n:=src c j 24 in
 0<n -> disjoint (stack_base c+512) 256 a n /\ disjoint (scratch c) 512 a n.
Definition geometry c := stack_separate c /\ messages_separate c.

Lemma matrix_out m a n v x : ~(a<=x<a+64*n) -> Frame.matrix m a n v x=m x.
Proof. apply write_outside. Qed.
Lemma hash_message_pointer c j : placement c -> geometry c -> (j<8)%nat ->
 read_word (hash_memory c) (stack_base c+640+8*Z.of_nat j)=src c j 16.
Proof.
 intros P [D _] J. transitivity (read_word (Staging.original(p c)) (stack_base c+640+8*Z.of_nat j)).
 - apply Staging.read_block;intros k K;unfold hash_memory,prefixes,stack_separate,disjoint in *.
   rewrite matrix_out,write_outside by lia. reflexivity.
 - replace (stack_base c+640+8*Z.of_nat j) with
    (frame(entry c)+512+64*Z.of_nat 2+8*Z.of_nat j) by (unfold stack_base;ring).
   exact (row_word _ _ _ 2 j (entry_memory _ P) ltac:(lia) J).
Qed.
Lemma hash_message_length c j : placement c -> (j<8)%nat ->
 Output.message_length (hash_entry c) j=masked_length c j.
Proof.
 intros P J. change (read_word (hash_memory c) (stack_base c+704+8*Z.of_nat j)=masked_length c j).
 replace (stack_base c+704+8*Z.of_nat j) with (Frame.cell (stack_base c+704) 0 j) by (unfold Frame.cell;ring).
 unfold hash_memory. apply Frame.matrix_word;[exact J|lia|].
 unfold masked_length;destruct(enabled c j);[apply read_word_bound,entry_memory,P|unfold word64;lia].
Qed.
Lemma octets_ext m n a b k : (forall d,0<=d<Z.of_nat k -> m(a+d)=n(b+d)) ->
 octets m a k=octets n b k.
Proof. intro H;unfold octets;apply map_ext_in;intros i I;apply in_seq in I;rewrite H by lia;reflexivity. Qed.
Lemma hash_prefix c (sig:bool) j : placement c -> geometry c -> (j<8)%nat ->
 octets (hash_memory c) ((if sig then scratch c+256 else scratch c)+32*Z.of_nat j) 32 =
 octets (mem(entry c)) (src c j (if sig then 8 else 0)) 32.
Proof.
 intros P [D _] J. apply octets_ext; intros k K.
 set (a:=(if sig then scratch c+256 else scratch c)+32*Z.of_nat j).
 assert (A:a=Staging.encoded_ptr (p c) sig j) by
 (unfold a,Staging.encoded_ptr,PrepareChunk.Caller.r_bytes,PrepareChunk.Caller.encoding_size,scratch;
  destruct sig;ring).
 assert (R:0<=a-scratch c+k<512) by (unfold a;destruct sig;lia).
 unfold hash_memory,prefixes. rewrite matrix_out by (unfold stack_separate,disjoint in D;lia).
 replace (a+k) with (scratch c+(a-scratch c+k)) by ring.
 rewrite write_at by lia. replace (scratch c+(a-scratch c+k)) with (Staging.encoded_ptr (p c) sig j+k) by lia.
 rewrite Staging.staged_bytes by lia. unfold p. rewrite prepared_ptr by (auto using entry_memory).
 change (staged_rows (entry c) (first c) (live c) (src c j (if sig then 8 else 0)+k)=mem(entry c) (src c j (if sig then 8 else 0)+k)).
 unfold staged_rows. apply matrix_out.
 destruct(row_separation _ P j J);unfold src,disjoint in *;destruct sig;lia.
Qed.
Lemma hash_input c j : placement c -> geometry c -> (j<8)%nat -> enabled c j=true ->
 Output.challenge_input (hash_entry c) j =
 r_bytes(input_at c j)++key_bytes(input_at c j)++message(input_at c j).
Proof.
 intros P G J On. unfold Output.challenge_input;fold (Output.message_length (hash_entry c) j).
 rewrite hash_message_length by auto. unfold masked_length;rewrite On.
 change (octets (hash_memory c) (scratch c+256+32*Z.of_nat j) 32 ++
  octets (hash_memory c) (scratch c+32*Z.of_nat j) 32 ++ octets (hash_memory c)
   (read_word (hash_memory c) (stack_base c+640+8*Z.of_nat j)) (Z.to_nat(src c j 24)) = r_bytes(input_at c j)++key_bytes(input_at c j)++message(input_at c j)).
 rewrite (hash_prefix c true j P G J),(hash_prefix c false j P G J), hash_message_pointer by auto.
 f_equal;f_equal. apply octets_ext;intros k K.
 pose proof(read_word_bound _ _ (entry_memory _ P)
  : word64(src c j 24)). unfold word64 in H. rewrite Z2Nat.id in K by lia.
 change (0<=k<src c j 24) in K. destruct (proj2 G j J ltac:(lia)) as [Stack Scratch].
 change (hash_memory c (src c j 16+k)=mem(entry c)(src c j 16+k)).
 unfold hash_memory,prefixes.
 rewrite matrix_out,write_outside by (unfold disjoint in *;lia).
 change (staged_rows (entry c) (first c) (live c) (src c j 16+k)=mem(entry c) (src c j 16+k)).
 unfold staged_rows;apply matrix_out;unfold disjoint,stack_base in *;lia.
Qed.

Definition abi c := let s:=hash_entry c in
 Ed25519Simd.Sha512Challenge.Frame.placement s (slide c+Ed25519Simd.Sha512Challenge.ObjectBytes.address) (Z.of_nat(length Ed25519Simd.Sha512Challenge.ObjectBytes.symbol_bytes))
   (slide c+LiteralBytes.address) /\ well_formed s /\
 Ed25519Simd.Sha512Challenge.Frame.mapped s (slide c+LiteralBytes.address) LiteralBytes.symbol_bytes.
Definition runs c := Ed25519Simd.Sha512Challenge.Execution.run Ed25519Simd.Sha512Challenge.ObjectBytes.address Ed25519Simd.Sha512Challenge.ObjectBytes.symbol_bytes (slide c) LiteralBytes.address (hash_entry c).
Lemma returns c : abi c -> exists result, runs c=Some result /\ byte_memory (Ed25519Simd.Sha512Challenge.Execution.after result) /\ Output.challenge_digests (hash_entry c) (Ed25519Simd.Sha512Challenge.Execution.after result).
Proof.
 intros [P [W M]]. destruct (Ed25519Simd.Sha512Challenge.Audit.returns_correct _ _ _ _ Ed25519Simd.Sha512Challenge.Object.assembled_sha512_challenge_correct
  (slide c) (hash_entry c) P W M) as [result [Run [_ [_ [_ [Bytes [_ Digests]]]]]]];eauto.
Qed.
