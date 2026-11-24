From Coq Require Import List ZArith Lia Bool.
From Machine Require Import execution.LinkedCalls execution.WordBounds execution.MachineState memory.ByteMemory.
From Curve25519 Require Import Scalar.
From Curve25519.group Require Import Affine.
From Ed25519Simd.PrepareChunk Require Staging Caller Dispatch Composition Audit Object.
From Ed25519Simd.VerifyBatch Require Import Policy Lane Rows.
Local Open Scope Z_scope.

Record chunk := Chunk { entry:cpu; first:nat; live:nat; mode:policy; slide:Z;
  masks:nat->nat->bool; temp:nat->data }.
Definition p c := preparation (entry c) (first c) (live c) (strict (mode c)).
Definition input_at c := original_row (entry c) (first c) (live c).
Definition scalar_out c := Staging.scalar_run PrepareChunk.Audit.common_pc (p c) (entry c) (masks c) (slide c).
Definition filter_state c := Composition.filter_entry (p c) (temp c) (entry c).
Definition dispatch c := Dispatch.dispatch (strict(mode c)) (filter_state c)
  (regs (scalar_out c) 0%nat) (Composition.decoded (p c)).
Definition ready c := snd (dispatch c).
Definition metadata c := Ed25519Simd.PrepareChunk.Audit.metadata (strict(mode c)) (p c) (filter_state c)
  (regs (scalar_out c) 0%nat).
Definition enabled c j := metadata c (Staging.selected (p c)+64+Z.of_nat j) =? 1.

Record placement c : Prop := {
  entry_memory : byte_memory (mem (entry c));
  row_separation : rows_apart (entry c) (first c) (live c);
  prepare_placement : Ed25519Simd.PrepareChunk.Audit.placement (p c);
  scalar_placement : Staging.scalar_inputs PrepareChunk.Audit.common_pc (p c) (entry c) (slide c);
  initial_words : forall t,data_words(temp c t)
}.

Lemma rows_bytes c : byte_memory(mem(entry c)) -> byte_memory(Staging.original (p c)).
Proof.
 intro B. apply write_bytes_well_formed; [exact B|intros;apply word_byte_bound].
Qed.
Lemma prepared c : placement c -> Ed25519Simd.PrepareChunk.Audit.chunk_result (strict(mode c)) (p c) (entry c)
  (masks c) (slide c) (temp c).
Proof.
 intros [B R P A T]. apply (Ed25519Simd.PrepareChunk.Audit.preparation Ed25519Simd.PrepareChunk.Object.assembled_prepare_chunk_correct);
   auto using rows_bytes.
Qed.
Lemma same_input c j : placement c -> (j<8)%nat ->
 Composition.encoding (p c) false j=little_endian(key_bytes(input_at c j)) /\
 Composition.encoding (p c) true j=little_endian(r_bytes(input_at c j)) /\
 Composition.signature_scalar (p c) j=little_endian(s_bytes(input_at c j)).
Proof. intros [B S _ _ _] J;apply prepared_bytes;assumption. Qed.
Lemma eligibility c j : placement c -> (j<8)%nat ->
 (Composition.accepts (strict(mode c)) (p c) j <-> eligible_input (mode c) (input_at c j)).
Proof.
 intros P J;destruct(same_input _ _ P J) as [K [R S]].
 unfold Composition.accepts,eligible_input. rewrite K,R,S. reflexivity.
Qed.
Local Opaque Staging.scalar_run Composition.decoded Composition.filter_entry Dispatch.dispatch.
Lemma prepare_rejected c : placement c -> ready c=false -> forall j,(j<8)%nat ->
 ~ signature_accepts (mode c) (input_at c j).
Proof.
 intros P No j J H. apply accepted_eligible in H. apply (eligibility _ _ P J) in H.
 assert (ready c=true) by (apply (proj1(prepared _ P));exists j;auto). congruence.
Qed.
Lemma enabled_ok c j : placement c -> ready c=true -> (j<8)%nat ->
 (enabled c j=true <-> eligible_input (mode c) (input_at c j)).
Proof.
 intros P Ready J. destruct (proj2(prepared _ P) Ready) as [_ [_ [_ L]]].
 destruct (L j J) as [_ [_ [_ [F _]]]]. unfold enabled;rewrite Z.eqb_eq,F.
 apply eligibility;assumption.
Qed.
Definition s_digits c j := SignatureScalar.Audit.digits (scalar_out c)
 (Staging.scratch(p c)+Caller.digits_offset) j.
Lemma prepared_scalar c j : placement c -> ready c=true -> (j<8)%nat -> enabled c j=true ->
 Radix.number 16 (s_digits c j)=little_endian(s_bytes(input_at c j)).
Proof.
 intros P Ready J On. apply (enabled_ok _ _ P Ready J) in On.
 destruct On as [S _]. destruct(same_input _ _ P J) as [_ [_ Eq]].
 destruct (proj2(prepared _ P) Ready) as [[_ Digits] _]. specialize(Digits j J).
 destruct Digits as [_ D].
 rewrite Eq in D. rewrite (proj2 (Z.ltb_lt _ _) S) in D. exact (proj2 D).
Qed.

(* The finite set of lanes lets us obtain a point for each valid decode
   constructively. Invalid-key lanes select the caller's identity table. *)
Definition key_selection c (keys:nat->point) := forall j,(j<8)%nat ->
 if Composition.returned_bit (p c) false j
 then Policy.decodes (Composition.encoding (p c) false j) (keys j)
 else keys j=identity.
Lemma select_keys c : byte_memory(Staging.original(p c)) -> exists keys,key_selection c keys.
Proof.
 intro B. assert (C:forall j,(j<8)%nat ->exists A,
   if Composition.returned_bit (p c) false j then Policy.decodes (Composition.encoding (p c) false j) A
   else A=identity).
 { intros j J. destruct (Composition.decode_lane (p c) false j B J) as [Ok _].
   destruct (Composition.returned_bit _ _ _) eqn:E;[apply Ok;reflexivity|exists identity;reflexivity]. }
 assert (F:forall n,(n<=8)%nat -> exists keys:nat->point, forall j,(j<n)%nat ->
   if Composition.returned_bit (p c) false j then Policy.decodes (Composition.encoding (p c) false j) (keys j)
   else keys j=identity).
 { induction n as [|n IH];intro N;[exists (fun _=>identity);intros;lia|].
   destruct (IH ltac:(lia)) as [f H]. destruct (C n ltac:(lia)) as [a A].
   exists (fun j=>if Nat.eqb j n then a else f j). intros j J.
   destruct (Nat.eqb_spec j n);[subst;exact A|apply H;lia]. }
 apply F;lia.
Qed.
Lemma enabled_key c keys j : placement c -> ready c=true -> key_selection c keys ->
 (j<8)%nat -> enabled c j=true -> Policy.decodes (little_endian(key_bytes(input_at c j))) (keys j).
Proof.
 intros P Ready Select J On. apply (enabled_ok _ _ P Ready J) in On.
 destruct On as [_ [_ [A [DA _]]]]. destruct(same_input _ _ P J) as [K _].
 rewrite <-K in *. specialize (Select j J).
 destruct(Composition.decode_lane (p c) false j (rows_bytes c (entry_memory _ P)) J) as [Ok _].
 assert (Composition.returned_bit (p c) false j=true) by (apply Ok;now exists A).
 now rewrite H in Select.
Qed.
