From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory ExecutionProperties.
Require Import Program Pow2ABI Pow2Memory.
Require Execution.
From Machine Require Import MemoryCoverage ByteExecution.
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


Lemma trace_frame size c d last es :
 record_path 1024 pow2_program abi_layout c = Some (last,es) ->
 writes_only allowed_write es -> balanced [(caller_slot,Caller)] es ->
 flat_frame pow2_program size es (c,d) (last,effects pow2_program (data_effects es) d).
Proof.
 intros R W B loc Place; cbn [fst snd].
 split; [intros; eapply permitted_bytes; eassumption|].
 intros before M.
 eapply recorded_frame with (live:=[(caller_slot,Caller)]); try eassumption.
 - eapply placement_separates; exact Place.
 - intros; eapply permitted_bytes; eassumption.
 - intros; eapply caller_byte_protected; eassumption.
 - intros a [<-|[]]; now right.
 - intros a H; now left.
Qed.

Lemma output_vector_coverage : covers_vectors output 10 Execution.expected_path=true.
Proof. vm_compute;reflexivity. Qed.

Lemma output_trace_covered es : data_effects es = Execution.expected_path ->
 forall loc k, 0 <= k < 640 -> writes_at loc es (origin loc output+k).
Proof.
 intros E; apply (MemoryCoverage.output_trace_covered output 10 es).
 rewrite E; exact output_vector_coverage.
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
 split; [unfold registers_preserved; cbn [fst]; apply ext_in_map; exact Regs|]. split.
 - exists 1024%nat,es. split; [exact R|]. split; [exact W|]. split; [exact B|]. now apply trace_frame.
 - exists (output,0),1024%nat,es. split; [reflexivity|]. split; [exact R|].
   pose proof (Execution.control_path_checked incoming) as Path.
   rewrite P in Path. cbn [Execution.observe_path] in Path.
   injection Path as _ _ Ops.
   intros loc k K. change (writes_at loc es (origin loc output+0+k)).
   rewrite Z.add_0_r. apply output_trace_covered; assumption.
Qed.
