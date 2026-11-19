From Coq Require Import List ZArith Lia.
From Machine Require Import Instructions Blocks VectorSequence.
Import ListNotations.
Open Scope Z_scope.

(* Expand every shared fragment before making comparisons at instruction
   boundaries. Ordinary instructions emitted by expand_op are never VectorCode. *)
Inductive body_instruction := Ordinary (op : operation) | SIMD (i : instruction).
Definition expand_op p op := match op with
 | VectorCode id => match lookup_fragment p id with
   | Some code => map SIMD code | None => [Ordinary op] end
 | _ => [Ordinary op] end.
Definition instructions p b := flat_map (expand_op p) (body b).
Definition no_fragments := Program [] [].
Definition instruction_bytes i := match i with
 | Ordinary op => op_bytes no_fragments op | SIMD v => encode v end.
Definition byte_count (bytes : list Z) := Z.of_nat (length bytes).
Definition width i := byte_count (instruction_bytes i).
Definition span code := byte_count (flat_map instruction_bytes code).

Definition set_pc ip c := Control ip (Blocks.gpr c) (zf c) (return_memory c).
Definition at_address addr (s : state) : state := (set_pc (At addr) (fst s), snd s).
Definition operation_effect p l op (s : state) :=
 apply_result p (snd s) (exec_op p l (fst s) op).
Definition instruction_effect l i (s : state) : option state := match i with
 | Ordinary (VectorCode _) => None
 | Ordinary op => operation_effect no_fragments l op s
 | SIMD v => option_map (fun d => (fst s,d)) (vector_step l (fst s) v (snd s)) end.

(* Each step reads the current data, applies its effects immediately and
   publishes the next PC. The explicit address is the fetch address. *)
Definition instruction_step l addr i s :=
 option_map (at_address (addr + width i)) (instruction_effect l i s).
Definition exit_step l addr e (s : state) : option state :=
 option_map (fun c => (c,snd s)) (transfer l (fst s) (addr + byte_count (exit_bytes e)) e).
Fixpoint sequential l addr code e s := match code with
 | [] => exit_step l addr e s
 | i::rest => bind (instruction_step l addr i s) (sequential l (addr + width i) rest e) end.

Lemma SIMD_sequence l c code d :
 sequence (instruction_effect l) (map SIMD code) (c,d) =
 option_map (fun d' => (c,d')) (sequence (vector_step l c) code d).
Proof.
 revert d; induction code as [|i rest IH]; intro d; cbn; auto.
 destruct (vector_step l c i d); cbn; auto.
Qed.

Lemma expand_op_correct p l op s :
 operation_effect p l op s = sequence (instruction_effect l) (expand_op p op) s.
Proof.
 destruct s as [c d]. destruct op; try solve [
   unfold operation_effect; cbn [expand_op sequence instruction_effect];
   unfold operation_effect; cbn [exec_op fst snd];
   repeat match goal with
   | |- context [Blocks.gpr c ?r] => destruct (Blocks.gpr c r)
   | |- context [pointer_at c ?r ?n] => destruct (pointer_at c r n)
   | |- context [vector_ok l ?a ?w] => destruct (vector_ok l a w)
   | |- context [match ?v with pair _ _ => _ end] => destruct v
   end; reflexivity ].
 cbn [expand_op]. destruct (lookup_fragment p fragment) as [code|] eqn:F.
 - rewrite SIMD_sequence, (vector_sequence _ _ _ _ _ (capture_covers _ _)).
   unfold operation_effect; cbn [exec_op fst snd]; rewrite F.
   unfold readable; destruct (forallb _ (load_operands code));
   cbn [apply_result effects fold_left apply_effect];
   try rewrite (lookup_fragment_code _ _ _ F); reflexivity.
 - unfold operation_effect; cbn [exec_op fst snd]; rewrite F; reflexivity.
Qed.

Lemma body_effects_sequential p l ops s :
 apply_result p (snd s) (exec_body p l (fst s) ops) =
 sequence (instruction_effect l) (flat_map (expand_op p) ops) s.
Proof.
 revert s; induction ops as [|op rest IH]; intros [c d]; [reflexivity|].
 cbn [exec_body flat_map fst snd]. rewrite sequence_app, <- expand_op_correct.
 unfold operation_effect; cbn [fst snd].
 destruct (exec_op p l c op) as [[mid head]|]; [|reflexivity].
 cbn [bind apply_result]. rewrite <-IH; cbn [fst snd].
 destruct (exec_body p l mid rest) as [[last tail]|]; cbn [apply_result]; auto.
 unfold effects. now rewrite fold_left_app.
Qed.

Lemma byte_count_app a b : byte_count (a ++ b) = byte_count a + byte_count b.
Proof. unfold byte_count. rewrite length_app, Nat2Z.inj_add. reflexivity. Qed.

Lemma expanded_bytes p ops :
 flat_map instruction_bytes (flat_map (expand_op p) ops) = flat_map (op_bytes p) ops.
Proof.
 induction ops as [|op rest IH]; [reflexivity|].
 cbn [flat_map]. rewrite flat_map_app, IH. f_equal.
 destruct op; cbn [expand_op flat_map instruction_bytes op_bytes]; try apply app_nil_r.
 unfold fragment_code; destruct (lookup_fragment p fragment) as [code|]; cbn.
 - induction code as [|i tail T]; cbn; congruence.
 - unfold fragment_code, lookup_fragment, no_fragments; destruct fragment; reflexivity.
Qed.

Lemma encoded_end p b :
 after p b = start b + span (instructions p b) + byte_count (exit_bytes (terminator b)).
Proof.
 unfold after, block_bytes, span, instructions. rewrite expanded_bytes.
 fold (byte_count (flat_map (op_bytes p) (body b) ++ exit_bytes (terminator b))). rewrite byte_count_app. lia.
Qed.

(* Body operations preserve the incoming PC and do not read it as an operand. *)
Lemma exec_op_set_pc p l ip c op :
 exec_op p l (set_pc ip c) op =
 option_map (fun '(c',es) => (set_pc ip c',es)) (exec_op p l c op).
Proof.
 destruct c as [old regs flag stack], op; cbn [exec_op];
 unfold capture, pointer_at, set_pc, set_gpr; cbn [Blocks.gpr zf rip return_memory].
 all: repeat match goal with
 | |- context [match ?v with _ => _ end] => destruct v eqn:?
 end; reflexivity.
Qed.

Lemma transfer_set_pc l ip c next e : transfer l (set_pc ip c) next e = transfer l c next e.
Proof. destruct c,e; reflexivity. Qed.

Lemma step_ignores_old_pc l addr i ip c d :
 instruction_step l addr i (set_pc ip c,d) = instruction_step l addr i (c,d).
Proof.
 destruct i as [op|[dst op]].
 - destruct op; unfold instruction_step, instruction_effect, operation_effect; cbn [fst snd]; try reflexivity;
   rewrite exec_op_set_pc; destruct (exec_op no_fragments l c _) as [[mid es]|]; reflexivity.
 - unfold instruction_step, instruction_effect, vector_step; cbn [fst snd].
   destruct c; destruct (forallb _ _); reflexivity.
Qed.

Lemma sequential_ignores_old_pc l addr code e ip c d :
 sequential l addr code e (set_pc ip c,d) = sequential l addr code e (c,d).
Proof.
 destruct code; cbn [sequential].
 - unfold exit_step; cbn [fst snd]. now rewrite transfer_set_pc.
 - now rewrite step_ignores_old_pc.
Qed.

Lemma span_cons i rest : span (i::rest) = width i + span rest.
Proof. unfold span, width; apply byte_count_app. Qed.

(* These three laws determine the result of any block evaluator. *)
Theorem block_laws_suffice l
 (eval : Z -> list body_instruction -> exit -> state -> option state) :
 (forall a e s, eval a [] e s = exit_step l a e s) ->
 (forall a i s, eval a [i] Next s = instruction_step l a i s) ->
 (forall a xs ys e s, eval a (xs ++ ys) e s =
    bind (eval a xs Next s) (eval (a + span xs) ys e)) ->
 forall code a e s, eval a code e s = sequential l a code e s.
Proof.
 intros empty single split code. induction code as [|i rest IH]; intros a e s.
 - apply empty.
 - change (i::rest) with ([i] ++ rest) at 1. rewrite split, single, span_cons.
   change (span []) with 0. rewrite Z.add_0_r. cbn [sequential].
   destruct (instruction_step l a i s); cbn [bind]; auto.
Qed.

Lemma sequential_effects l addr code e s :
 sequential l addr code e s =
 bind (sequence (instruction_effect l) code s) (exit_step l (addr + span code) e).
Proof.
 revert s addr; induction code as [|i rest IH]; intros s addr.
 - cbn [sequential sequence bind]. unfold span; cbn. now rewrite Z.add_0_r.
 - cbn [sequential sequence]. unfold instruction_step.
   destruct (instruction_effect l i s) as [[mid d]|]; [|reflexivity].
   cbn [option_map bind]. unfold at_address; cbn [fst snd]. rewrite sequential_ignores_old_pc, IH, span_cons.
   now rewrite Z.add_assoc.
Qed.

Theorem block_sequential p l b s :
 execute_block p l b s = sequential l (start b) (instructions p b) (terminator b) s.
Proof.
 rewrite sequential_effects. unfold instructions. rewrite <- body_effects_sequential.
 unfold execute_block, block_control, exit_step. destruct s as [c d]; cbn [fst snd].
 destruct (exec_body p l c (body b)) as [[mid es]|]; [|reflexivity].
 cbn [bind apply_result fst snd]. rewrite encoded_end. unfold instructions.
 destruct (transfer l mid _ (terminator b)); reflexivity.
Qed.

(* Empty fallthrough and empty bodies with a real control instruction. *)
Theorem block_empty p l b s : instructions p b = [] ->
 execute_block p l b s = exit_step l (start b) (terminator b) s.
Proof. intro H; rewrite block_sequential, H. reflexivity. Qed.

Corollary empty_fallthrough_identity p l b s :
 rip (fst s) = At (start b) -> instructions p b = [] -> terminator b = Next ->
 execute_block p l b s = Some s.
Proof.
 intros R I E. rewrite (block_empty _ _ _ _ I), E.
 destruct s as [[ip regs flag stack] d]; cbn in R; subst ip.
 unfold exit_step; cbn. now rewrite Z.add_0_r.
Qed.

Theorem block_singleton p l b i s : instructions p b = [i] -> terminator b = Next ->
 execute_block p l b s = instruction_step l (start b) i s.
Proof.
 intros I E. rewrite block_sequential, I, E. cbn [sequential]. unfold instruction_step.
 destruct (instruction_effect l i s) as [[c d]|]; cbn; [|reflexivity].
 now rewrite Z.add_0_r.
Qed.

Lemma sequential_split l addr prefix suffix e s :
 sequential l addr (prefix ++ suffix) e s =
 bind (sequential l addr prefix Next s) (sequential l (addr + span prefix) suffix e).
Proof.
 revert s addr; induction prefix as [|i rest IH]; intros s addr.
 - destruct s as [c d]. cbn [app sequential exit_step transfer bind option_map fst snd].
   change (span []) with 0. change (byte_count (exit_bytes Next)) with 0.
   rewrite Z.add_0_r. symmetry. apply sequential_ignores_old_pc.
 - cbn [app sequential]. rewrite span_cons, Z.add_assoc.
   destruct (instruction_step l addr i s); cbn [bind]; auto.
Qed.

(* Choose the cut using an instruction count. Empty prefixes and suffixes are
   included as local executions, even though a zero-byte block cannot be fetched
   as a separate entry in a valid program. *)
Theorem block_cut p l b k s :
 let code := instructions p b in
 let prefix := firstn k code in
 let suffix := skipn k code in
 execute_block p l b s =
 bind (sequential l (start b) prefix Next s)
      (sequential l (start b + span prefix) suffix (terminator b)).
Proof.
 cbn zeta. rewrite block_sequential, <- sequential_split, firstn_skipn. reflexivity.
Qed.

(* Prefix and suffix may use different fragment tables, including a division
   inside a vector fragment. Their common unit of comparison is the ISA line. *)
Theorem block_split p p1 p2 l whole left right s :
 instructions p whole = instructions p1 left ++ instructions p2 right ->
 start left = start whole -> terminator left = Next ->
 start right = after p1 left -> terminator right = terminator whole ->
 execute_block p l whole s =
 bind (execute_block p1 l left s) (execute_block p2 l right).
Proof.
 intros code entry fall middle final. rewrite !block_sequential, code, entry, fall.
 rewrite (sequential_split l (start whole) (instructions p1 left)).
 destruct (sequential l (start whole) (instructions p1 left) Next s); [|reflexivity].
 cbn [bind]. rewrite block_sequential, middle, encoded_end, entry, fall, final.
 change (byte_count (exit_bytes Next)) with 0. now rewrite Z.add_0_r.
Qed.

(* Fetch is the only difference between step and direct execution of a block. *)
Lemma step_at p l b s :
 rip (fst s) = At (start b) -> lookup (sections p) (start b) = Some b ->
 step p l s = execute_block p l b s.
Proof. intros R B. unfold step, dispatch. now rewrite R, B. Qed.

Theorem step_sequential p l b s :
 rip (fst s) = At (start b) -> lookup (sections p) (start b) = Some b ->
 step p l s = sequential l (start b) (instructions p b) (terminator b) s.
Proof. intros R B. rewrite (step_at _ _ _ _ R B). apply block_sequential. Qed.

Lemma fallthrough_pc p l b s t :
 terminator b = Next -> execute_block p l b s = Some t -> rip (fst t) = At (after p b).
Proof.
 intros E. unfold execute_block, block_control. rewrite E.
 destruct (exec_body p l (fst s) (body b)) as [[mid es]|]; [|discriminate].
 now intros [= <-].
Qed.

(* The original layout fetches one block. The split layout fetches the left
   block at the same PC and its successor at the first byte after it. *)
Theorem step_split p split l whole left right s :
 rip (fst s) = At (start whole) ->
 lookup (sections p) (start whole) = Some whole ->
 lookup (sections split) (start left) = Some left ->
 lookup (sections split) (start right) = Some right ->
 instructions p whole = instructions split left ++ instructions split right ->
 start left = start whole -> terminator left = Next ->
 start right = after split left -> terminator right = terminator whole ->
 step p l s = bind (step split l s) (step split l).
Proof.
 intros pc fetch L R code entry fall middle final.
 assert (pc_left : rip (fst s) = At (start left)) by now rewrite entry.
 rewrite (step_at _ _ _ _ pc fetch), (step_at _ _ _ _ pc_left L).
 rewrite (block_split _ _ _ _ _ _ _ _ code entry fall middle final).
 destruct (execute_block split l left s) as [t|] eqn:T; [|reflexivity].
 cbn [bind]. symmetry. apply step_at; [rewrite middle; eapply fallthrough_pc; eassumption | exact R].
Qed.
