From Coq Require Import List ZArith Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory WordBounds ByteMemory ExecutionProperties.
Require Import Pow2ABI Pow2Memory FieldSpec.
Open Scope Z_scope.

(* This entry predicate takes actual qwords and one byte array. In particular,
   overlapping read-only inputs automatically obtain consistent logical views. *)
Record concrete_entry loc size (regs : nat -> Z) (vectors : nat -> nat -> Z) before : Prop := {
 entry_placement : valid_placement loc size;
 entry_bytes : byte_memory before;
 entry_register_words : forall r, word64 (regs r);
 entry_vector_words : forall j r, (j<8)%nat -> word64 (vectors j r);
 entry_stack_pointer : regs 4%nat = entry_rsp loc;
 entry_output_pointer : regs 7%nat = origin loc output;
 entry_a_pointer : regs 6%nat = origin loc input_a;
 entry_b_pointer : regs 2%nat = origin loc input_b;
 entry_return_word : read_word before (entry_rsp loc) = caller_pc loc
}.

Definition buffer_words flat base k := read_word flat (base+8*Z.of_nat k).
Definition entry_from_bytes loc regs vectors flag before : state :=
 (initial_control (Control Caller (fun r => Int (regs r)) flag (fun _ => None)),
  data_from_bytes loc vectors before).
Definition scalar_value loc v := match v with
 | Int n => Some n | Ptr a => Some (address_of loc a) | Unknown => None end.

Lemma decoded_buffer loc vectors flat region k :
 words_at (memory (data_from_bytes loc vectors flat)) region k =
 buffer_words flat (origin loc region) k.
Proof.
 unfold words_at,data_from_bytes,limb_address,address_of,buffer_words; cbn [memory fst snd].
 pose proof (Nat.div_mod k 8 ltac:(lia)) as D.
 apply (f_equal Z.of_nat) in D. rewrite Nat2Z.inj_add,Nat2Z.inj_mul in D.
 f_equal; lia.
Qed.

Theorem concrete_entry_representable loc size regs vectors flag before :
 concrete_entry loc size regs vectors before ->
 let initial := entry_from_bytes loc regs vectors flag before in
 valid_pow2_entry initial (buffer_words before (origin loc input_a))
                          (buffer_words before (origin loc input_b)) /\
 state_words initial /\
 agrees loc mapped (snd initial) (return_memory (fst initial)) before /\
 (forall r, scalar_value loc (gpr (fst initial) r) = Some (regs r)).
Proof.
 intros [Place Bytes Regs Vec SP Out A B Ret] initial.
 assert (Entry : valid_pow2_entry initial (buffer_words before (origin loc input_a))
                                        (buffer_words before (origin loc input_b))).
 { split; [eexists; reflexivity|]. split; intros; apply decoded_buffer. }
 assert (Words : state_words initial).
 { split.
   - intro r. unfold initial,entry_from_bytes,initial_control; cbn [fst gpr].
     do 8 (destruct r as [|r]; [cbn [scalar_words]; auto|]). apply Regs.
   - now apply data_from_bytes_words. }
 split; [exact Entry|]. split; [exact Words|]. split.
 - apply data_from_bytes_agrees; [exact Bytes|]. intros a t Map S.
   change ((if ptr_eq a caller_slot then Some Caller else None) = Some t) in S.
   destruct (ptr_eq a caller_slot) eqn:E; [|discriminate].
   apply ptr_eq_true in E; subst a. inversion S; subst t.
   split; [|exact Ret]. unfold valid_placement in Place.
   destruct Place as (_ & _ & _ & _ & _ & _ & Bound & _). exact Bound.
 - intro r. unfold initial,entry_from_bytes,initial_control; cbn [fst gpr].
   destruct r as [|[|[|[|[|[|[|[|r]]]]]]]];
     cbv beta iota zeta delta [scalar_value address_of fst snd];
     try rewrite Z.add_0_r; try reflexivity; f_equal; symmetry; assumption.
Qed.

(* The observable read relation is exact, rather than equality of truncated
   serializations. It therefore distinguishes every representable qword. *)
Definition vector_reads loc d flat := forall a j,
 mapped (VectorCell a) -> (j<8)%nat ->
 read_word flat (address_of loc a+8*Z.of_nat j) = memory d a j.

Definition byte_result p loc initial final before after :=
 (forall middle, reaches p abi_layout initial middle -> state_words middle) /\
 byte_memory after /\ vector_reads loc (snd final) after /\
 (forall x, ~ writable_byte loc x -> after x = before x) /\
 exists fuel es,
   record_path fuel p abi_layout (fst initial) = Some (fst final,es) /\
   after = replay p loc es (snd initial) before /\
   (* Every trace prefix has representable data and exact concrete reads. *)
   (forall pre tail, es = pre ++ tail ->
     let d := effects p (data_effects pre) (snd initial) in
     let flat := replay p loc pre (snd initial) before in
     data_words d /\ byte_memory flat /\ vector_reads loc d flat) /\
   (forall pre a t tail, es = pre ++ Pop a t :: tail ->
     read_word (replay p loc pre (snd initial) before) (address_of loc a) =
       pc_word loc t mod 2^64).

Lemma memory_safe_bytes p size loc initial final before :
 valid_placement loc size -> state_words initial -> byte_memory before ->
 agrees loc mapped (snd initial) (return_memory (fst initial)) before ->
 returns p abi_layout initial final -> memory_safe p size initial final ->
 exists after, byte_result p loc initial final before after.
Proof.
 intros Place W Bytes Agree [R End] [fuel [es [Trace [_ [_ Frame]]]]].
 pose proof (execution_preserves_words _ _ _ _ R W) as Final.
 destruct (Frame loc Place) as [_ F].
 destruct (F before Agree) as [A [Outside [Prefixes Pops]]].
 exists (replay p loc es (snd initial) before).
 split; [intros middle Reach; eapply execution_preserves_words; eassumption|].
 split; [now apply replay_well_formed|].
 split; [intros a j M J; eapply agrees_read_vector; eauto; exact (proj2 Final)|].
 split; [exact Outside|]. exists fuel,es. split; [exact Trace|]. split; [reflexivity|]. split.
 - intros pre tail E.
   assert (D : data_words (effects p (data_effects pre) (snd initial))).
   { destruct initial; eapply recorded_prefix_words; eassumption. }
   split; [exact D|]. split; [now apply replay_well_formed|].
   intros a j M J. eapply agrees_read_vector; eauto. exact (proj1 (Prefixes _ _ E)).
 - intros pre a t tail E. apply read_word_encoded. intros k K; exact (Pops _ _ _ _ _ E K).
Qed.

Lemma output_bytes loc regs vectors flag before final after :
 vector_reads loc (snd final) after -> forall k, (k<80)%nat ->
 buffer_words after (origin loc output) k =
 output_words (entry_from_bytes loc regs vectors flag before) final k.
Proof.
 intros Reads k K.
 change (buffer_words after (origin loc output) k =
   memory (snd final) (limb_address output 0 (k/8)) (k mod 8)%nat).
 rewrite <-(Reads (limb_address output 0 (k/8)) (k mod 8)%nat).
 - unfold buffer_words,limb_address,address_of; cbn [fst snd].
   pose proof (Nat.div_mod k 8 ltac:(lia)) as D.
   apply (f_equal Z.of_nat) in D. rewrite Nat2Z.inj_add,Nat2Z.inj_mul in D. f_equal; lia.
 - unfold mapped,vector_ok,access,limb_address,abi_layout,output,stack; cbn [fst snd].
   replace (0+64*Z.of_nat (k/8)) with (Z.of_nat (k/8)*64) by ring.
   rewrite Z.mod_mul,Z.div_mul by lia. cbn [Z.eqb andb].
   assert (C : ((0 <=? Z.of_nat (k/8)) && (Z.of_nat (k/8) <? 10))%bool = true).
   { apply Bool.andb_true_iff; split; [apply Z.leb_le; lia|apply Z.ltb_lt].
     pose proof (Nat.div_mod k 8 ltac:(lia)); lia. }
   rewrite C; reflexivity.
 - apply Nat.mod_upper_bound; lia.
Qed.

(* This is the byte-facing part of the single public certificate. Execution is
   still in the stated machine model; no independent ISA refinement is assumed. *)
Definition concrete_pow2_contract p size :=
 forall loc regs vectors flag before, concrete_entry loc size regs vectors before ->
 let initial := entry_from_bytes loc regs vectors flag before in
 exists final after,
   returns p abi_layout initial final /\ stack_restored initial final /\
   registers_preserved initial final /\ byte_result p loc initial final before after /\
   pow2_spec (buffer_words before (origin loc input_a))
             (buffer_words before (origin loc input_b))
             (buffer_words after (origin loc output)).

Theorem concrete_contract_from_logical p size :
 (forall initial a b, valid_pow2_entry initial a b -> exists final,
   returns p abi_layout initial final /\ stack_restored initial final /\
   registers_preserved initial final /\ memory_safe p size initial final /\
   pow2_spec a b (output_words initial final)) ->
 concrete_pow2_contract p size.
Proof.
 intros Logical loc regs vectors flag before Entry initial.
 destruct (concrete_entry_representable _ _ _ _ flag _ Entry) as [E [W [A _]]].
 destruct (Logical _ _ _ E) as [final [R [SP [Regs [Mem Spec]]]]].
 destruct (memory_safe_bytes _ _ _ _ _ _ (entry_placement _ _ _ _ _ Entry)
             W (entry_bytes _ _ _ _ _ Entry) A R Mem) as [after Result].
 exists final,after. split; [exact R|]. split; [exact SP|]. split; [exact Regs|].
 split; [exact Result|].
 assert (Out : forall k, (k<80)%nat -> buffer_words after (origin loc output) k = output_words initial final k).
 { apply output_bytes. exact (proj1 (proj2 (proj2 Result))). }
 intros Bound side j J. destruct (Spec Bound side j J) as [Bounds Value].
 assert (Cell : forall i, (i<10)%nat ->
   cell (buffer_words after (origin loc output)) i j = cell (output_words initial final) i j).
 { intros i I; unfold cell; apply Out; lia. }
 destruct side; cbn zeta in *; split;
 try (intros i I; rewrite Cell by lia; now apply Bounds);
 unfold field_at,limbs in *; repeat rewrite Cell by lia; exact Value.
Qed.
