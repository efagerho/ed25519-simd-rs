From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory ExecutionProperties.
Require Import Program Pow2ABI Pow2Memory.
Require Execution.
Import ListNotations.
Open Scope Z_scope.

Lemma mapped_vector a : mapped (VectorCell a) ->
 vector_in stack 1920 a \/ vector_in output 640 a \/ vector_in input_a 320 a \/ vector_in input_b 320 a.
Proof.
 destruct a as [r n]. unfold mapped,vector_ok,access,abi_layout,vector_in; cbn [fst snd].
 rewrite andb_true_iff. intros [A P]. apply Z.eqb_eq in A.
 pose proof (Z.div_mod n 64 ltac:(lia)).
 destruct (Nat.eqb r stack) eqn:S.
 - apply Nat.eqb_eq in S; subst. left. destruct ((0 <=? n/64) && (n/64 <? 30)) eqn:B.
   + apply andb_true_iff in B as [L U]. apply Z.leb_le in L; apply Z.ltb_lt in U; intuition lia.
   + destruct (n/64 =? -1), (n/64 =? 30); discriminate.
 - destruct (Nat.eqb r output) eqn:O.
   + apply Nat.eqb_eq in O; subst. right; left. destruct ((0 <=? n/64) && (n/64 <? 10)) eqn:B; [|discriminate].
     apply andb_true_iff in B as [L U]. apply Z.leb_le in L; apply Z.ltb_lt in U; intuition lia.
   + destruct ((Nat.eqb r input_a || Nat.eqb r input_b) && (0 <=? n/64) && (n/64 <? 5)) eqn:B; [|discriminate].
     repeat rewrite andb_true_iff in B. destruct B as [[R L] U]. apply orb_true_iff in R.
     apply Z.leb_le in L; apply Z.ltb_lt in U. destruct R as [R|R]; apply Nat.eqb_eq in R; intuition lia.
Qed.

Lemma same_region_vectors loc r n q a b :
 vector_in r n a -> vector_in r q b ->
 VectorCell a = VectorCell b \/
 disjoint (cell_address loc (VectorCell a)) 64 (cell_address loc (VectorCell b)) 64.
Proof.
 destruct a as [ra x], b as [rb y]. unfold vector_in,cell_address,address_of,disjoint; cbn [fst snd].
 intros [-> [_ [_ A]]] [-> [_ [_ B]]]. destruct (Z.eq_dec x y); [subst;auto|right].
 pose proof (Z.div_mod x 64 ltac:(lia)). pose proof (Z.div_mod y 64 ltac:(lia)). lia.
Qed.

Lemma different_regions loc r n q m a b :
 vector_in r n a -> vector_in q m b -> disjoint (origin loc r) n (origin loc q) m ->
 disjoint (cell_address loc (VectorCell a)) 64 (cell_address loc (VectorCell b)) 64.
Proof. destruct a,b. unfold vector_in,cell_address,address_of,disjoint; cbn [fst snd].
 intros [-> [? [? _]]] [-> [? [? _]]]; lia. Qed.

Lemma placement_separates loc size :
 valid_placement loc size -> separated loc allowed_write mapped.
Proof.
 unfold valid_placement,entry_rsp. intros V w s W S.
 destruct V as [_ [_ [_ [_ [_ [_ [_ [_ [OS [OA [OB [SA [SB _]]]]]]]]]]]]].
 destruct w as [w|w], s as [s|s]; cbn [allowed_write] in W.
 - apply mapped_vector in S. destruct W as [O|A];
   destruct S as [T|[U|[B|C]]]; try (eapply same_region_vectors; eassumption); right;
   eapply different_regions; try eassumption; unfold disjoint in *; lia.
 - destruct S as [->| ->]; destruct W as [A|A]; right; destruct w as [r d];
   unfold vector_in in A; cbn [fst snd] in A; destruct A as [-> [L [U _]]];
   unfold cell_address,address_of,private_slot,caller_slot,disjoint in *; cbn [fst snd width]; lia.
 - subst w. apply mapped_vector in S. destruct S as [A|[A|[A|A]]]; right; destruct s as [r d];
   unfold vector_in in A; cbn [fst snd] in A; destruct A as [-> [L [U _]]];
   unfold cell_address,address_of,private_slot,disjoint in *; cbn [fst snd width]; lia.
 - subst w. destruct S as [->| ->]; [now left|right].
   unfold cell_address,address_of,private_slot,caller_slot,disjoint; cbn [width fst snd]; lia.
Qed.

Lemma permitted_bytes loc es x : writes_only allowed_write es -> writes_at loc es x -> writable_byte loc x.
Proof.
 intros W [e [s [I [E K]]]]. apply Forall_forall with (x:=e) in W; [|exact I].
 rewrite E in W. destruct s as [[r d]|a].
 - destruct W as [A|A]; unfold vector_in in A; cbn [fst snd] in A; destruct A as [-> [L [U _]]];
   unfold inside,cell_address,address_of in K; cbn [width fst snd] in K; unfold writable_byte,entry_rsp; lia.
 - cbn [allowed_write] in W; subst a. unfold inside,cell_address,address_of,private_slot in K; cbn [width fst snd] in K;
   unfold writable_byte,entry_rsp; lia.
Qed.

Definition cell_inb r n (a : pointer) :=
 Nat.eqb (fst a) r && (0 <=? snd a) && (snd a + 64 <=? n) && (snd a mod 64 =? 0).
Lemma cell_inb_spec r n a : cell_inb r n a = true <-> vector_in r n a.
Proof. unfold cell_inb,vector_in; rewrite !andb_true_iff,Nat.eqb_eq,!Z.leb_le,Z.eqb_eq; tauto. Qed.
Definition write_ok e := match destination e with
 | Some (VectorCell a) => cell_inb output 640 a || cell_inb stack 1920 a
 | Some (ReturnSlot a) => ptr_eq a private_slot
 | None => true end.
Lemma write_ok_sound es : forallb write_ok es = true -> writes_only allowed_write es.
Proof.
 rewrite forallb_forall. unfold writes_only. rewrite Forall_forall.
 intros H e I; specialize (H e I). unfold write_ok in H.
 destruct (destination e) as [[a|a]|]; cbn [allowed_write]; [|now apply ptr_eq_true|exact Logic.I].
 rewrite orb_true_iff,!cell_inb_spec in H; exact H.
Qed.

Lemma caller_byte_protected loc size k : valid_placement loc size -> 0 <= k < 8 ->
 ~ writable_byte loc (entry_rsp loc+k).
Proof.
 unfold valid_placement. intros (_ & _ & _ & _ & _ & _ & _ & _ & OS & _) K.
 unfold disjoint in OS; unfold writable_byte; lia.
Qed.

Definition observe_frame (result : control * list event) :=
 let '(c,es) := result in
 (map (Blocks.gpr c) saved_registers, forallb write_ok es && check_stack [(caller_slot,Caller)] es).
Lemma frame_checked incoming :
 option_map observe_frame (record_path 1024 pow2_program abi_layout (initial_control incoming)) =
 Some (map (Blocks.gpr (initial_control incoming)) saved_registers,true).
Proof. vm_compute. reflexivity. Qed.

Lemma map_values {A B} (f g : A -> B) xs :
 map f xs = map g xs -> forall x, In x xs -> f x = g x.
Proof.
 induction xs; cbn; intros H x I; [contradiction|]. injection H as F G.
 destruct I as [<-|I]; auto.
Qed.

Lemma trace_frame size c d last es :
 record_path 1024 pow2_program abi_layout c = Some (last,es) ->
 writes_only allowed_write es -> balanced [(caller_slot,Caller)] es ->
 flat_frame pow2_program size es (c,d) (last,effects pow2_program (data_effects es) d).
Proof.
 intros R W B loc Place. cbn [fst snd]. split; [intros; eapply permitted_bytes; eassumption|].
 intros before M. pose proof (placement_separates _ _ Place) as Sep.
 destruct (record_path_sound _ _ _ _ _ _ R) as [_ [Slots Reads]].
 assert (Prefix: forall pre tail, es=pre++tail ->
   agrees loc mapped (effects pow2_program (data_effects pre) d)
    (fold_left update_slots pre (return_memory c)) (replay pow2_program loc pre d before)).
 { intros pre tail ->. apply Forall_app in W as [W _]. eapply replay_agrees; eassumption. }
 split; [rewrite <-Slots; eapply replay_agrees; eassumption|].
 split; [intros x Outside; apply replay_frame; intro I; apply Outside; eapply permitted_bytes; eassumption|].
 split.
 { intros pre tail E; split; [exact (Prefix _ _ E)|]. intros k K.
   apply replay_frame. intro I. apply (caller_byte_protected _ _ _ Place K).
   rewrite E in W. apply Forall_app in W as [W _]. eapply permitted_bytes; eassumption. }
 intros pre a t tail k E K. specialize (Prefix _ _ E).
 assert (I : In (Pop a t) es) by (rewrite E; apply in_or_app; right; now left).
 assert (Map : mapped (ReturnSlot a)).
 { destruct (balanced_pop_location _ _ _ _ B I) as [[A|F]|[u P]].
   - right; symmetry; exact A.
   - contradiction.
   - left. apply Forall_forall with (x:=Push a u) in W; assumption. }
 rewrite E, reads_app in Reads; destruct Reads as [_ [Read _]].
 apply (Prefix (ReturnSlot a) k _ Map K); unfold cell_byte; now rewrite Read.
Qed.

Lemma output_trace_covered es : data_effects es = Execution.expected_path ->
 forall loc k, 0 <= k < 640 -> writes_at loc es (origin loc output+k).
Proof.
 intros E loc k K. set (i := Z.to_nat (k/64)).
 assert (Q : 0 <= k/64 < 10).
 { split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
 assert (I : (i<10)%nat) by (unfold i; lia).
 assert (Index : Z.of_nat i = k/64) by (unfold i; rewrite Z2Nat.id; lia).
 assert (W : In (Write i (limb_address output 0 i)) (data_effects es)).
 { rewrite E. unfold Execution.expected_path.
   apply in_or_app; right. apply in_or_app; right. apply in_or_app; left.
   unfold Execution.stores. apply in_map_iff. exists i; split; [reflexivity|apply in_seq; lia]. }
 unfold data_effects in W. apply in_flat_map in W as [e [Member W]].
 destruct e as [op|a t|a t]; cbn in W; try contradiction.
 destruct W as [Eq|W]; [subst op|contradiction].
 exists (DataOp (Write i (limb_address output 0 i))), (VectorCell (limb_address output 0 i)).
 split; [exact Member|]. split; [reflexivity|].
 unfold inside,cell_address,address_of,limb_address; cbn [fst snd width].
 pose proof (Z.div_mod k 64 ltac:(lia)). pose proof (Z.mod_pos_bound k 64 ltac:(lia)). lia.
Qed.

Theorem pow2_frame_correct size initial a b final :
 valid_pow2_entry initial a b -> returns pow2_program abi_layout initial final ->
 registers_preserved initial final /\ memory_safe pow2_program size initial final /\
 output_initialized pow2_program initial final.
Proof.
 destruct initial as [c d]. intros [[incoming Init] _] Returns. cbn [fst] in Init; subst c.
 pose proof (frame_checked incoming) as Check.
 destruct (record_path 1024 pow2_program abi_layout (initial_control incoming)) as [[last es]|] eqn:R;
   [|discriminate].
 apply (f_equal (fun result => match result with Some obs => fst obs | None => [] end)) in Check as Regs.
 apply (f_equal (fun result => match result with Some obs => snd obs | None => false end)) in Check as Safe.
 change (forallb write_ok es && check_stack [(caller_slot,Caller)] es = true) in Safe.
 apply andb_true_iff in Safe as [W B].
 apply write_ok_sound in W. apply check_stack_sound in B.
 destruct (record_path_sound _ _ _ _ _ _ R) as [P _].
 pose proof (path_returns _ _ _ _ _ _ P d) as Ends.
 pose proof (return_unique _ _ _ _ _ Returns Ends) as ->.
 split; [unfold registers_preserved; cbn [fst]; apply map_values; exact Regs|]. split.
 - exists 1024%nat,es. split; [exact R|]. split; [exact W|]. split; [exact B|]. now apply trace_frame.
 - exists (output,0),1024%nat,es. split; [reflexivity|]. split; [exact R|].
   pose proof (Execution.control_path_checked incoming) as Path.
   rewrite P in Path. cbn [Execution.observe_path] in Path.
   injection Path as _ _ Ops.
   intros loc k K. change (writes_at loc es (origin loc output+0+k)).
   rewrite Z.add_0_r. apply output_trace_covered; assumption.
Qed.
