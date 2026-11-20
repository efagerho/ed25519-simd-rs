From Coq Require Import ZArith List Lia.
From Machine Require Import execution.Blocks memory.MemoryTrace memory.FlatMemory execution.WordBounds.
Import ListNotations.
Open Scope Z_scope.

Definition byte_memory (flat : bytes) := forall x, 0 <= flat x < 256.
Fixpoint read_le (n : nat) (flat : bytes) a := match n with
 | O => 0 | S n => flat a + 256 * read_le n flat (a+1) end.
Definition read_word := read_le 8.

Lemma word_byte_zero w : word_byte w 0 = w mod 256.
Proof. unfold word_byte; now rewrite Z.div_1_r. Qed.
Lemma word_byte_next w k : 0 <= k -> word_byte w (k+1) = word_byte (w/256) k.
Proof.
 intro K. unfold word_byte. replace (8*(k+1)) with (8+8*k) by ring.
 rewrite Z.pow_add_r by lia. rewrite Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
 reflexivity.
Qed.
Lemma word_byte_bound w k : 0 <= word_byte w k < 256.
Proof. unfold word_byte; apply Z.mod_pos_bound; lia. Qed.

Lemma read_le_bound n flat a : byte_memory flat -> 0 <= read_le n flat a < 256^Z.of_nat n.
Proof.
 intro B; revert a; induction n; intro a; [cbn; lia|].
 cbn [read_le]. rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia.
 specialize (IHn (a+1)); specialize (B a). lia.
Qed.
Lemma read_word_bound flat a : byte_memory flat -> word64 (read_word flat a).
Proof. intro B; exact (read_le_bound 8 flat a B). Qed.

(* Reconstruction is modulo 2^64 without a bound, and exact for word64.
   Neither direction assumes that a byte array already has a logical view. *)
Lemma read_le_encoded n w flat a :
 (forall k, 0 <= k < Z.of_nat n -> flat (a+k) = word_byte w k) ->
 read_le n flat a = w mod 256^Z.of_nat n.
Proof.
 revert w a; induction n as [|n IH]; intros w a E.
 - cbn [read_le Z.of_nat]; now rewrite Z.mod_1_r.
 - cbn [read_le]. rewrite (IH (w/256)).
   + replace (flat a) with (word_byte w 0) by (rewrite <-E by lia; now rewrite Z.add_0_r).
     rewrite word_byte_zero,Nat2Z.inj_succ,Z.pow_succ_r by lia.
     symmetry; apply Z.rem_mul_r; [lia|apply Z.pow_pos_nonneg; lia].
   + intros k K. replace (a+1+k) with (a+(k+1)) by ring.
     rewrite E by lia. apply word_byte_next; lia.
Qed.
Lemma read_word_encoded w flat a :
 (forall k, 0 <= k < 8 -> flat (a+k) = word_byte w k) ->
 read_word flat a = w mod 2^64.
Proof. exact (read_le_encoded 8 w flat a). Qed.
Lemma read_word_exact w flat a : word64 w ->
 (forall k, 0 <= k < 8 -> flat (a+k) = word_byte w k) -> read_word flat a = w.
Proof. intros W E; rewrite (read_word_encoded _ _ _ E); now apply Z.mod_small. Qed.

Theorem word_bytes_injective x y : word64 x -> word64 y ->
 (forall k, 0 <= k < 8 -> word_byte x k = word_byte y k) -> x = y.
Proof.
 intros X Y E. transitivity (read_word (fun k => word_byte x k) 0).
 - symmetry; apply read_word_exact; [exact X|intros; reflexivity].
 - apply read_word_exact; [exact Y|exact E].
Qed.

Lemma read_le_byte n flat a j : byte_memory flat -> (j < n)%nat ->
 word_byte (read_le n flat a) (Z.of_nat j) = flat (a+Z.of_nat j).
Proof.
 intro B; revert a j; induction n as [|n IH]; intros a [|j] J; try lia; cbn [read_le].
 - rewrite word_byte_zero. replace (256 * read_le n flat (a+1)) with
     (read_le n flat (a+1) * 256) by ring.
   rewrite Z.mod_add by lia. rewrite Z.mod_small by apply B. now rewrite Z.add_0_r.
 - rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat j)) with (Z.of_nat j+1) by lia.
   rewrite word_byte_next by lia.
   replace (256 * read_le n flat (a+1)) with (read_le n flat (a+1) * 256) by ring.
   rewrite Z.div_add by lia. rewrite Z.div_small by apply B. cbn [Z.add].
   rewrite IH by lia. f_equal; lia.
Qed.
Lemma read_word_byte flat a k : byte_memory flat -> 0 <= k < 8 ->
 word_byte (read_word flat a) k = flat (a+k).
Proof.
 intros B K. replace k with (Z.of_nat (Z.to_nat k)) by (rewrite Z2Nat.id; lia).
 apply read_le_byte; auto; lia.
Qed.

Lemma vector_byte_lane v j k : 0 <= k < 8 ->
 vector_byte v (8*Z.of_nat j+k) = word_byte (v j) k.
Proof.
 intro K. unfold vector_byte.
 replace (8*Z.of_nat j+k) with (k+Z.of_nat j*8) by ring.
 rewrite Z.div_add,Z.mod_add by lia. rewrite Z.div_small,Z.mod_small by lia.
 cbn [Z.add]. now rewrite Nat2Z.id.
Qed.

Theorem agrees_read_vector loc tracked d slots flat a j :
 agrees loc tracked d slots flat -> tracked (VectorCell a) ->
 data_words d -> (j < 8)%nat ->
 read_word flat (address_of loc a + 8*Z.of_nat j) = memory d a j.
Proof.
 intros A T [_ W] J. apply read_word_exact; [now apply W|].
 intros k K. replace (address_of loc a+8*Z.of_nat j+k) with
   (cell_address loc (VectorCell a)+(8*Z.of_nat j+k)) by (unfold cell_address; ring).
 apply (A (VectorCell a) (8*Z.of_nat j+k)); auto; [cbn [width]; lia|].
 cbn [cell_byte]; now rewrite vector_byte_lane.
Qed.
Theorem agrees_read_return loc tracked d slots flat a t :
 agrees loc tracked d slots flat -> tracked (ReturnSlot a) -> slots a = Some t ->
 word64 (pc_word loc t) -> read_word flat (address_of loc a) = pc_word loc t.
Proof.
 intros A T S W. apply read_word_exact; [exact W|].
 intros k K. apply (A (ReturnSlot a) k _ T K). cbn [cell_byte]; now rewrite S.
Qed.

Definition data_from_bytes loc regs flat := Data regs
 (fun a j => read_word flat (address_of loc a+8*Z.of_nat j)).
Lemma data_from_bytes_words loc regs flat :
 byte_memory flat -> (forall j r, (j<8)%nat -> word64 (regs j r)) ->
 data_words (data_from_bytes loc regs flat).
Proof. intros B R; split; [exact R|intros; now apply read_word_bound]. Qed.
Lemma data_from_bytes_agrees loc tracked regs slots flat :
 byte_memory flat ->
 (forall a t, tracked (ReturnSlot a) -> slots a = Some t ->
   word64 (pc_word loc t) /\ read_word flat (address_of loc a) = pc_word loc t) ->
 agrees loc tracked (data_from_bytes loc regs flat) slots flat.
Proof.
 intros B S [a|a] k b T K V.
 - cbn [cell_byte vector_byte data_from_bytes memory] in V. inversion V; subst b.
   change (flat (address_of loc a+k) =
     word_byte (read_word flat (address_of loc a+8*Z.of_nat (Z.to_nat (k/8)))) (k mod 8)).
   rewrite Z2Nat.id by (apply Z.div_pos; cbn [width] in K; lia).
   rewrite read_word_byte by (auto; apply Z.mod_pos_bound; lia).
   pose proof (Z.div_mod k 8 ltac:(lia)); f_equal; lia.
 - cbn [cell_byte] in V. destruct (slots a) as [t|] eqn:E; [|discriminate].
   inversion V; subst b. destruct (S _ _ T E) as [_ R].
   rewrite <-R. symmetry; now apply read_word_byte.
Qed.

Lemma write_bytes_well_formed flat a n payload :
 byte_memory flat -> (forall k, 0 <= k < n -> 0 <= payload k < 256) ->
 byte_memory (write_bytes flat a n payload).
Proof.
 intros B P x; unfold write_bytes. destruct (_ && _)%bool eqn:E; [|apply B].
 apply Bool.andb_true_iff in E as [L U]. apply Z.leb_le in L; apply Z.ltb_lt in U.
 apply P; lia.
Qed.
Lemma write_event_well_formed loc e d flat :
 byte_memory flat -> byte_memory (write_event loc e d flat).
Proof.
 intro B; destruct e as [op|a t|a t]; [destruct op| |]; try exact B;
 apply write_bytes_well_formed; auto; intros; apply word_byte_bound.
Qed.
Theorem replay_well_formed p loc es d flat :
 byte_memory flat -> byte_memory (replay p loc es d flat).
Proof.
 revert d flat; induction es; intros d flat B; [exact B|].
 cbn [replay]; apply IHes,write_event_well_formed,B.
Qed.

Theorem write_read_word flat a w : word64 w ->
 read_word (write_bytes flat a 8 (word_byte w)) a = w.
Proof. intro W; apply read_word_exact; auto using write_at. Qed.
Theorem write_read_vector flat a v j : (j<8)%nat -> word64 (v j) ->
 read_word (write_bytes flat a 64 (vector_byte v)) (a+8*Z.of_nat j) = v j.
Proof.
 intros J W; apply read_word_exact; [exact W|]. intros k K.
 replace (a+8*Z.of_nat j+k) with (a+(8*Z.of_nat j+k)) by ring.
 rewrite write_at by lia. now apply vector_byte_lane.
Qed.


(* A buffer's qword index is its vector index followed by its lane index. *)
Definition buffer_words flat base k := read_word flat(base+8*Z.of_nat k).
Lemma vector_word_address loc region k :
 address_of loc(region,64*Z.of_nat(k/8))+8*Z.of_nat(k mod 8)=
 origin loc region+8*Z.of_nat k.
Proof.
 unfold address_of;cbn [fst snd].
 pose proof(Nat.div_mod k 8 ltac:(lia))as D;apply(f_equal Z.of_nat)in D.
 rewrite Nat2Z.inj_add,Nat2Z.inj_mul in D;lia.
Qed.
Lemma decoded_buffer loc vectors flat region k :
 memory(data_from_bytes loc vectors flat)(region,64*Z.of_nat(k/8))(k mod 8)%nat=
 buffer_words flat(origin loc region)k.
Proof. unfold data_from_bytes,buffer_words;cbn [memory];now rewrite vector_word_address. Qed.
