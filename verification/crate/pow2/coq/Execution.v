From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks isa.Instructions execution.Dependencies.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Pow2 Require Import Pow2Caller Linked Program Pow2Spec.
From Ed25519Simd.Pow2 Require Export Pow2ABI.
Import ListNotations.
Open Scope Z_scope.

Definition stores region base := map (fun i => Write i (limb_address region base i)) (seq 0 10).
Definition entry_effects := [Broadcast 28 19; Broadcast 29 (2^51-1)] ++
 map (fun i => Read i (limb_address (if Nat.ltb i 5 then input_a else input_b) 0 (i mod 5))) (seq 0 10).
Definition action_effects op := match op with
 | Store slot => stores stack (640 * Z.of_nat slot)
 | Square => [Evaluate 0 []]
 | Product slot => [Evaluate 1 [(8%nat,(stack,640*Z.of_nat slot))]] end.
Definition expected_path := entry_effects ++ flat_map action_effects chain ++
 stores output 0 ++ [ClearUpper].
Definition observe_path (result:option (control * list effect)) := match result with
 | Some (c,es) => Some (rip c,Blocks.gpr c 4%nat,es) | None => None end.
Theorem block_layout_checked :
 valid_program pow2_program = true.
Proof. vm_compute; reflexivity. Qed.

(* Compute only public control and effective addresses. Vector data and input
   memory remain universally quantified throughout the proof below. *)
Theorem control_path_checked incoming :
 observe_path (path 1024 pow2_program abi_layout (initial_control incoming)) =
 Some (Caller,Ptr (stack,1936),expected_path).
Proof. vm_compute. reflexivity. Qed.

Definition live_input i := Nat.ltb i 10 || Nat.eqb i 28 || Nat.eqb i 29.
Definition live_read (sq:bool) base d :=
 negb sq && Nat.eqb base 8 && (0 <=? d) && (d <? 640) && (d mod 64 =? 0).
Definition check_dependencies sq code :=
 forallb (agreement (live_read sq) code live_input) (seq 0 10) &&
 forallb (fun ins => negb (Nat.eqb (fst ins) 28)) code &&
 forallb (fun ins => negb (Nat.eqb (fst ins) 29)) code.
Theorem kernel_dependencies :
 check_dependencies true square_code = true /\ check_dependencies false multiply_code = true.
Proof. split; vm_compute; reflexivity. Qed.

Definition matches (s:data) j (st:Pow2Caller.machine) :=
 (forall i, (i<10)%nat -> Blocks.zmm s j i = fst st i) /\
 Blocks.zmm s j 28%nat = 19 /\ Blocks.zmm s j 29%nat = 2^51-1 /\
 forall slot i, (i<10)%nat ->
 memory s (limb_address stack (640*Z.of_nat slot) i) j = snd st slot i.

Lemma fragment_agrees (sq:bool) s j x y bases :
 let code := if sq then square_code else multiply_code in
 (forall i, (i<10)%nat -> Blocks.zmm s j i = x i) ->
 Blocks.zmm s j 28%nat = 19 -> Blocks.zmm s j 29%nat = 2^51-1 ->
 (forall b d, live_read sq b d = true ->
   effective_load s bases j b d = rhs_memory (feed x y) b d) ->
 forall i, (i<10)%nat ->
 run (effective_load s bases j) code (Blocks.zmm s j) i = run_kernel code (feed x y) i.
Proof.
 intros code X C M L i I.
 apply (agreement_sound (live_read sq) code live_input); auto.
 - intros r R. unfold live_input in R. unfold feed.
   destruct (Nat.ltb r 10) eqn:T; [apply X; now apply Nat.ltb_lt|].
   cbn in R. destruct (Nat.eqb r 28) eqn:E.
   + apply Nat.eqb_eq in E; subst; exact C.
   + cbn in R; rewrite R. apply Nat.eqb_eq in R; subst; exact M.
 - assert (D:check_dependencies sq code = true) by
     (unfold code; destruct sq; apply kernel_dependencies).
   unfold check_dependencies in D. apply Bool.andb_true_iff in D as [D _].
   apply Bool.andb_true_iff in D as [D _]. rewrite forallb_forall in D.
   apply D; apply in_seq; lia.
Qed.

Lemma constants_preserved (sq:bool) load r :
 let code := if sq then square_code else multiply_code in
 run load code r 28%nat = r 28%nat /\ run load code r 29%nat = r 29%nat.
Proof.
 intros code. assert (D: check_dependencies sq code = true)
 by (unfold code; destruct sq; apply kernel_dependencies).
 unfold check_dependencies in D. apply Bool.andb_true_iff in D as [D B].
 apply Bool.andb_true_iff in D as [_ A]. split; apply untouched; assumption.
Qed.

Lemma ptr_equal a b : ptr_eq a b = true <-> a = b.
Proof. destruct a as [r n], b as [s m]. unfold ptr_eq; cbn.
 rewrite Bool.andb_true_iff,Nat.eqb_eq,Z.eqb_eq. split; [intros [-> ->]|intros [= -> ->]]; auto.
Qed.
Definition recovered_index (a:pointer) base := Z.to_nat ((snd a-base)/64).
Lemma recover_limb region base i :
 recovered_index (limb_address region base i) base = i.
Proof. unfold recovered_index,limb_address; cbn [snd].
 replace (base+64*Z.of_nat i-base) with (Z.of_nat i*64) by ring.
 rewrite Z.div_mul by lia. apply Nat2Z.id. Qed.

Lemma writes_registers p region base xs s :
 Blocks.zmm (effects p (map (fun i=>Write i (limb_address region base i)) xs) s) = Blocks.zmm s.
Proof. revert s; induction xs as [|i xs IH]; intros s; [reflexivity|].
 transitivity (Blocks.zmm (apply_effect p s (Write i (limb_address region base i)))); [apply IH|reflexivity].
Qed.
Lemma writes_memory p region base xs s k j :
 memory (effects p (map (fun i=>Write i (limb_address region base i)) xs) s) k j =
 if existsb (fun i=>ptr_eq k (limb_address region base i)) xs
 then Blocks.zmm s j (recovered_index k base) else memory s k j.
Proof.
 revert s; induction xs as [|i xs IH]; intro s; [reflexivity|].
 change (memory (effects p (map (fun k=>Write k (limb_address region base k)) xs)
   (apply_effect p s (Write i (limb_address region base i)))) k j =
   if existsb (fun i=>ptr_eq k (limb_address region base i)) (i::xs)
   then Blocks.zmm s j (recovered_index k base) else memory s k j).
 cbn [existsb].
 rewrite IH. cbn [apply_effect memory Blocks.zmm].
 destruct (ptr_eq k (limb_address region base i)) eqn:E; cbn.
 - apply ptr_equal in E; subst k. rewrite recover_limb.
   destruct (existsb _ xs); reflexivity.
 - destruct (existsb _ xs); reflexivity.
Qed.
Lemma stored_limb p region base s i j : (i<10)%nat ->
 memory (effects p (stores region base) s) (limb_address region base i) j = Blocks.zmm s j i.
Proof.
 intros I. unfold stores. rewrite writes_memory,recover_limb.
 destruct (existsb _ _) eqn:E; auto. exfalso.
 assert (existsb (fun k=>ptr_eq (limb_address region base i) (limb_address region base k))
     (seq 0 10) = true).
 { apply existsb_exists; exists i; split; [apply in_seq;lia | apply ptr_equal;reflexivity]. }
 congruence.
Qed.
Lemma other_slot p s slot other i j : slot <> other -> (i<10)%nat ->
 memory (effects p (stores stack (640*Z.of_nat slot)) s) (limb_address stack (640*Z.of_nat other) i) j =
 memory s (limb_address stack (640*Z.of_nat other) i) j.
Proof.
 intros N I; unfold stores; rewrite writes_memory.
 destruct (existsb _ _) eqn:E; auto. apply existsb_exists in E as [k [K E]].
 apply in_seq in K. apply ptr_equal in E. pose proof (f_equal (@snd nat Z) E) as D. unfold limb_address in D; cbn [snd] in D; lia.
Qed.

Lemma square_step s j x slots : matches s j (x,slots) ->
 matches (effects pow2_program (action_effects Square) s) j
   (advance square_code multiply_code Square (x,slots)).
Proof.
 intros [X [C [M S]]].
 change (matches (Data (fun j=>run (effective_load s [] j) square_code (Blocks.zmm s j)) (memory s)) j
   (run_kernel square_code (feed x x),slots)).
 destruct (constants_preserved true (effective_load s [] j) (Blocks.zmm s j)) as [A B].
 split; [|split; [rewrite <- C;exact A|split; [rewrite <- M;exact B|exact S]]].
 apply (fragment_agrees true); auto; discriminate.
Qed.
Lemma product_step s j x slots slot : matches s j (x,slots) ->
 matches (effects pow2_program (action_effects (Product slot)) s) j
   (advance square_code multiply_code (Product slot) (x,slots)).
Proof.
 intros [X [C [M S]]]. set (bases := [(8%nat,(stack,640*Z.of_nat slot))]).
 change (matches (Data (fun j=>run (effective_load s bases j) multiply_code (Blocks.zmm s j)) (memory s)) j
   (run_kernel multiply_code (feed x (slots slot)),slots)).
 destruct (constants_preserved false (effective_load s bases j) (Blocks.zmm s j)) as [A B].
 split; [|split; [rewrite <- C;exact A|split; [rewrite <- M;exact B|exact S]]].
 apply (fragment_agrees false); auto.
 intros b d H. unfold live_read in H. repeat rewrite Bool.andb_true_iff in H.
 destruct H as [[[[ _ B8] D0] D1] Align]. apply Nat.eqb_eq in B8; subst.
 apply Z.leb_le in D0; apply Z.ltb_lt in D1; apply Z.eqb_eq in Align.
 set (i:=Z.to_nat (d/64)).
 assert (Index:Z.of_nat i=d/64) by (unfold i;rewrite Z2Nat.id;[reflexivity|apply Z.div_pos;lia]).
 assert (Disp:d=64*Z.of_nat i) by (rewrite Index;pose proof (Z.div_mod d 64 ltac:(lia));lia).
 assert (I:(i<10)%nat) by lia.
 change (memory s (stack,640*Z.of_nat slot+d) j = feed x (slots slot) (32+i)%nat).
 rewrite Disp at 1.
 change (memory s (limb_address stack (640*Z.of_nat slot) i) j = feed x (slots slot) (32+i)%nat).
 rewrite (S slot i I).
 unfold feed.
 assert (L:Nat.ltb (32+i) 10=false) by (apply Nat.ltb_ge;lia).
 assert (N:Nat.eqb (32+i) 28=false) by (apply Nat.eqb_neq;lia).
 assert (M':Nat.eqb (32+i) 29=false) by (apply Nat.eqb_neq;lia).
 assert (Lo:Nat.leb 32 (32+i)=true) by (apply Nat.leb_le;lia).
 assert (Hi:Nat.ltb (32+i) 42=true) by (apply Nat.ltb_lt;lia).
 rewrite L,N,M',Lo,Hi.
 replace (32+i-32)%nat with i by lia. reflexivity.
Qed.

Lemma action_step s j st op : matches s j st ->
 matches (effects pow2_program (action_effects op) s) j
         (advance square_code multiply_code op st).
Proof.
 destruct st as [x slots],op as [slot|slot|]; [|apply product_step|apply square_step].
 intros [X [C [M S]]]. unfold matches. cbn [action_effects advance fst snd].
 unfold stores at 1 2 3. rewrite writes_registers. split; [exact X|]. split; [exact C|].
 split; [exact M|]. intros k i I. unfold put; destruct (Nat.eqb slot k) eqn:E.
 - apply Nat.eqb_eq in E; subst. rewrite stored_limb by exact I. apply X;exact I.
 - apply Nat.eqb_neq in E. rewrite other_slot by assumption. apply S;exact I.
Qed.

Lemma action_sequence ops s j st : matches s j st ->
 matches (effects pow2_program (flat_map action_effects ops) s) j
         (fold_left (fun st op=>advance square_code multiply_code op st) ops st).
Proof.
 revert s st; induction ops as [|op ops IH]; intros s st H; [exact H|].
 cbn [flat_map fold_left]. unfold effects; rewrite fold_left_app.
 apply IH, action_step, H.
Qed.

Lemma read_words m region i j : (j<8)%nat ->
 words_at m region (i*8+j)%nat = m (limb_address region 0 i) j.
Proof.
 intros J; unfold words_at.
 assert (D: ((i*8+j)/8=i)%nat) by (symmetry;apply Nat.div_unique with (r:=j);lia).
 assert (R: ((i*8+j) mod 8=j)%nat) by (symmetry;apply Nat.mod_unique with (q:=i);lia).
 now rewrite D,R.
Qed.
Definition scratch_of s j slot i := memory s (limb_address stack (640*Z.of_nat slot) i) j.
Lemma entry_matches s a b j : entry_buffers s a b -> (j<8)%nat ->
 matches (effects pow2_program entry_effects s) j
   (input_lane a b j,scratch_of s j).
Proof.
 intros [A B] J. split.
 - intros i I. change (Blocks.zmm (effects pow2_program entry_effects s) j i = input_lane a b j i).
   assert (Read: Blocks.zmm (effects pow2_program entry_effects s) j i =
     memory s (limb_address (if Nat.ltb i 5 then input_a else input_b) 0 (i mod 5)) j).
   { do 10 (destruct i as [|i]; [reflexivity|]); lia. }
   rewrite Read. unfold input_lane. destruct (Nat.ltb i 5) eqn:E.
   + apply Nat.ltb_lt in E. rewrite Nat.mod_small by lia. rewrite <- read_words by assumption.
     apply A;lia.
   + apply Nat.ltb_ge in E. assert (R:(i mod 5=i-5)%nat).
     { symmetry. apply Nat.mod_unique with (q:=1%nat);lia. }
     rewrite R. rewrite <- read_words by assumption. apply B;lia.
 - split; [reflexivity|split;reflexivity].
Qed.

Lemma effects_app p a b s :
 effects p (a++b) s = effects p b (effects p a s).
Proof. unfold effects; apply fold_left_app. Qed.
Lemma flush_output s k : (k<80)%nat ->
 words_at (memory (effects pow2_program (stores output 0 ++ [ClearUpper]) s)) output k =
 Blocks.zmm s (k mod 8)%nat (k/8)%nat.
Proof.
 intro K. rewrite effects_app.
 change (memory (effects pow2_program (stores output 0) s) (limb_address output 0 (k/8)) (k mod 8)%nat =
   Blocks.zmm s (k mod 8)%nat (k/8)%nat).
 apply stored_limb. pose proof (Nat.div_mod k 8 ltac:(lia));lia.
Qed.
Local Opaque pow2_program chain square_code multiply_code action_effects entry_effects stores.
Lemma output_agrees s a b : entry_buffers s a b ->
 forall k, (k<80)%nat ->
 words_at (memory (effects pow2_program expected_path s)) output k =
 execute8 square_code multiply_code chain a b (scratch_of s) k.
Proof.
 intros E k K. set (j:=(k mod 8)%nat). set (i:=(k/8)%nat).
 assert (J:(j<8)%nat) by (apply Nat.mod_upper_bound;lia).
 assert (I:(i<10)%nat) by (unfold i;pose proof (Nat.div_mod k 8 ltac:(lia));lia).
 pose proof (entry_matches s a b j E J) as Start.
 pose proof (action_sequence chain _ _ _ Start) as End.
 destruct End as [R _]. specialize (R i I).
 unfold expected_path. rewrite effects_app,effects_app,flush_output by exact K. exact R.
Qed.

Lemma spec_ext a b out other :
 (forall k, (k<80)%nat -> other k = out k) -> pow2_spec a b out -> pow2_spec a b other.
Proof.
 intros E H In side j J. destruct (H In side j J) as [B P].
 assert (Cell:forall i, (i<10)%nat -> cell other i j = cell out i j)
   by (intros; unfold cell; apply E;lia).
 destruct side; cbn zeta in *; split.
 - intros i I; rewrite Cell by lia; apply B;assumption.
 - unfold field_at,limbs in *; repeat rewrite Cell by lia;exact P.
 - intros i I; rewrite Cell by lia; apply B;assumption.
 - unfold field_at,limbs in *; repeat rewrite Cell by lia;exact P.
Qed.

Theorem pow2_returns_correct initial a b :
 valid_pow2_entry initial a b ->
 exists final, returns pow2_program abi_layout initial final /\
   stack_restored initial final /\
   pow2_spec a b (output_words initial final).
Proof.
 destruct initial as [c s]. intros [[incoming Init] E]. cbn [fst] in Init; subst c.
 pose proof (control_path_checked incoming) as Check.
 destruct (path 1024 pow2_program abi_layout (initial_control incoming)) as [[last es]|] eqn:T;
   [|discriminate].
 cbn [observe_path] in Check. injection Check as PC SP Ops. subst es.
 exists (last,effects pow2_program expected_path s). split.
 - apply (path_returns _ _ _ _ _ _ T).
 - split; [unfold stack_restored, SysV.restores_rsp; cbn [fst]; rewrite SP; reflexivity|]. eapply spec_ext; [|apply linked_pow2_correct].
   intros k K. apply (output_agrees s a b E k K).
Qed.
