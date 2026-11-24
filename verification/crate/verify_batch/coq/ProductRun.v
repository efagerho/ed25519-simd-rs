From Coq Require Import List ZArith Lia Bool.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.FlatMemory memory.ByteMemory.
From Curve25519 Require Import SignedRadix16 Scalar.
From ProofArithmetic Require Import Radix.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.PostHash Require Product.
From Ed25519Simd.VerifyBatch Require Import Policy Lane Digest Rows Prepare Hash Candidate.
Local Open Scope Z_scope.

(* These requirements mention the spatial preconditions of the linked routines.
   The byte and digit ranges in their antecedents are proved at each call. *)
Definition bounded_digits l := forall r j k, (r=1%nat \/ r=8%nat) -> (j<8)%nat -> (k<64)%nat ->
 -8<=digits l r j k<8.
Record geometry c : Prop := {
 reducer_layout : forall flat,byte_memory flat ->
  let s:=reducer c flat in
  D.placement (regs s 4%nat) (regs s 7%nat) (regs s 6%nat)
   (slide c+Radix16.LinkedBytes.wrapper_pc) (D.size Radix16.LinkedBytes.symbol_bytes)
   (slide c+Radix16.LinkedBytes.reducer_pc) (D.size Scalar.ObjectBytes.symbol_bytes) /\ well_formed s;
 ladder_layout : forall flat, byte_memory flat ->
  let l:=ladder_with c flat in
  (forall j,(j<8)%nat -> possible c (SA.key_table l j)) ->
  bounded_digits l ->
  F.placement (slide c) l /\ valid_inputs (slide c+FullLadder.LinkedBytes.stage_pc) (F.pad_of l) l
}.

Lemma view_bytes c mid : Prepare.placement c -> byte_memory(mem mid) -> byte_memory (ladder_flat c mid).
Proof.
 intros P M. assert (S:byte_memory(mem(scalar_out c))).
 { pose proof (scalar_placement _ P) as [Pl [W [Literal _]]].
   destruct (SignatureScalar.Audit.returns_correct _ _ _ _ SignatureScalar.Object.assembled_signature_scalar_correct
     (slide c) (PrepareChunk.Staging.scalar_entry (p c) (entry c)) (masks c) Pl W Literal) as [_ Run].
   unfold scalar_out,PrepareChunk.Staging.scalar_run. destruct(SignatureScalar.Program.run _ _ _ _ _ _) as [ip s].
   exact (proj1(proj2(proj2(proj2(proj2 Run))))). }
 apply write_bytes_well_formed;[|intros;apply M]. apply write_bytes_well_formed;[|intros;apply S].
 change (byte_memory (write_bytes (PrepareChunk.Composition.table_memory (p c) (temp c)) (ptrs c) 64
   (vector_byte (PrepareChunk.Dispatch.selected_ptr (p c) (PrepareChunk.Composition.decoded(p c)))))).
 apply write_bytes_well_formed;[|intros;apply word_byte_bound].
 intro x;unfold PrepareChunk.Composition.table_memory,KeyTable.Audit.table_view,KeyTable.Audit.output_byte.
 destruct (KeyTable.Execution.lookup _ _);[apply word_byte_bound|apply rows_bytes,entry_memory,P].
Qed.

Lemma copied_digit c mid j k : buffers c -> (j<8)%nat -> (k<64)%nat ->
 digits (ladder c mid) 1 j k=signed_byte (mem(scalar_out c)(s_addr c+64*Z.of_nat j+Z.of_nat k)) /\
 digits (ladder c mid) 8 j k=signed_byte (mem mid(k_addr c+64*Z.of_nat j+Z.of_nat k)).
Proof.
 intros G J K. pose proof(digit_buffers _ G) as Sep. unfold digits.
 change (regs(ladder c mid) 1%nat) with (s_addr c). change (regs(ladder c mid) 8%nat) with (k_addr c).
 change (mem(ladder c mid)) with (ladder_flat c mid).
 unfold ladder_flat,copy. split;f_equal.
 - rewrite write_outside by (unfold disjoint in Sep;lia).
   replace (s_addr c+64*Z.of_nat j+Z.of_nat k) with (s_addr c+(64*Z.of_nat j+Z.of_nat k)) by ring.
   rewrite write_at by lia;reflexivity.
 - replace (k_addr c+64*Z.of_nat j+Z.of_nat k) with (k_addr c+(64*Z.of_nat j+Z.of_nat k)) by ring.
   rewrite write_at by lia;reflexivity.
Qed.
Lemma digits_passed c mid j : buffers c -> (j<8)%nat ->
 digit_list (ladder c mid) 1 j=s_digits c j /\
 digit_list (ladder c mid) 8 j=D.signed_digits (mem mid) (k_addr c) j.
Proof.
 intros G J. split;apply map_ext_in;intros k K;apply in_seq in K;apply copied_digit;auto;lia.
Qed.

Local Opaque PrepareChunk.Staging.scalar_run PrepareChunk.Composition.decoded PrepareChunk.Composition.filter_entry PrepareChunk.Dispatch.dispatch.
Lemma scalar_range c j : Prepare.placement c -> ready c=true -> (j<8)%nat ->
 Forall (fun d=> -8<=d<8) (s_digits c j).
Proof.
 intros P On J. destruct (proj2(prepared _ P) On) as [[_ Dg] _].
 destruct (Dg j J) as [_ Dg'].
 change (SignatureScalar.Audit.digits _ _ j) with (s_digits c j) in Dg'.
 destruct (PrepareChunk.Composition.signature_scalar (p c) j <? L);
 [exact (proj1 Dg')|rewrite Dg';apply Forall_forall;intros d I;apply repeat_spec in I;lia].
Qed.

Definition native_product c flat keys out := exists mid,
 Product.observation (full c) (slide c) (reducer c flat) (ladder c mid) mid out generator keys (WordSemantics.word (digest_next c)).

Lemma product_exists c flat keys : Prepare.placement c -> ready c=true ->
 buffers c -> constants(entry c) -> key_selection c keys -> geometry c -> byte_memory flat ->
 exists out,native_product c flat keys out.
Proof.
 intros P On G Tables Keys Space Bytes.
 destruct (reducer_layout _ Space flat Bytes) as [DP W].
 destruct (D.run_correct _ _ _ _ Radix16.Object.assembled_digest_to_radix16_correct
   (slide c) (reducer c flat) DP W) as [mid [Run [_ [_ [_ [_ [M Dg]]]]]]].
 set (l:=ladder c mid).
 assert (B:bounded_digits l).
 { intros r j k Which J K.
   assert (H:Forall (fun d=> -8<=d<8) (digit_list l r j)).
   { destruct Which as [->| ->];destruct(digits_passed c mid j G J) as [S D].
     - unfold l;rewrite S;apply scalar_range;assumption.
     - unfold l;rewrite D;exact (proj1(Dg j J)). }
   apply Forall_forall with (x:=digits l r j k) in H;[exact H|].
   unfold digit_list;apply in_map_iff;exists k;split;[reflexivity|apply in_seq;lia]. }
 destruct (ladder_layout _ Space (ladder_flat c mid) (view_bytes c mid P M)
   ltac:(intros j J;change (possible c (SA.key_table (ladder c mid) j));rewrite (selected_pointer _ _ _ P G J);apply selected_possible,J) B) as [LP V].
 pose proof(supplied_tables c mid keys P On G Tables Keys) as T.
 destruct (F.full_product FullLadder.Object.assembled_full_ladder_correct (slide c) l (full c)
  generator keys LP eq_refl V T) as [[out Exec] _].
 exists out,mid. constructor.
 - constructor;assumption || reflexivity.
 - rewrite <- (reducer_return c flat);exact Run.
 - intros j J;apply (proj2(digits_passed c mid j G J)).
 - exact Exec.
Qed.
