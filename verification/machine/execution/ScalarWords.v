From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.ScalarBytes execution.MappedFetch execution.LinkedRun execution.StoreInstructions
 memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Machine Require execution.IndexedRegisterWords isa.QwordRegister isa.VectorMoves isa.IndexedLoad execution.Packed execution.IndexedLoads.
Import ListNotations. Local Open Scope Z_scope.

(* Defined words in the scalar decoder, including the indexed vector loads
   that manipulate the batch's descriptor and pointer rows. *)
Lemma indexed_words i s : well_formed s -> well_formed (IndexedLoads.execute [i] s).
Proof. apply IndexedRegisterWords.execute_words. Qed.

Lemma low8_words s r v : well_formed s -> well_formed (low_byte s r v).
Proof.
 intro W;apply set_wf;[exact W|]. pose proof (proj1 W r) as R.
 pose proof (Z.div_mod (regs s r) 256 ltac:(lia)).
 pose proof (Z.mod_pos_bound (regs s r) 256 ltac:(lia)).
 pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
 assert (Quotient:regs s r / 256<2^56) by
   (apply Z.div_lt_upper_bound;unfold word64 in *;lia).
 unfold word64 in *;lia.
Qed.
Lemma pop_words s r : well_formed s -> well_formed (pop s r).
Proof.
 intros [G [V B]];split;[|split;assumption]. intros j;apply put_words.
 - exact (put_words (regs s) 4 (word(regs s 4%nat+8)) G (mod64_word _)).
 - apply read_word_bound,B.
Qed.

Lemma commit_words s w : well_formed s ->
 (forall k,0<=k<Z.of_nat(size w) -> 0<=payload w k<256) ->
 well_formed (with_words s (regs s) (commit (mem s) w)).
Proof. intros [G [V B]] W;split;[exact G|split;[exact V|apply write_bytes_well_formed;assumption]]. Qed.
Lemma set_vector_words s r vec : well_formed s -> (forall j,(j<8)%nat -> word64(vec j)) ->
 well_formed (CPU (regs s) (fun j=>put (vectors s j) r (vec j)) (flag s) (mem s)).
Proof. intros [G [V B]] W;split;[exact G|split;[intros j k J;apply put_words;auto|exact B]]. Qed.

Lemma qword_wf next s i v : well_formed s -> qword_op next s i=Some v -> well_formed v.
Proof.
 intros W;destruct i as [[d op]| | | | |sub d a b disp];cbn [qword_op];try destruct (_=?0);intro R;try discriminate;
 injection R as <-;apply set_vector_words;try exact W;intros j J.
 - apply bits_words;[intros;apply read_word_bound,W|intros;apply W,J].
 - apply mod64_word.
 - apply W;pose proof(Z.mod_pos_bound (vectors s j idx mod 16) 8 ltac:(lia));lia.
 - apply read_word_bound,W.
 - apply low64_word.
 - destruct sub;apply low64_word.
Qed.

Lemma step_wf origin off n op s c t ws : well_formed s ->
 step origin off n op s c=Some(t,ws) -> well_formed(cpu_state t).
Proof.
 intros W;destruct op;cbn [step];intro S.
 all: try solve [destruct (qword_op _ _ _) as [v|] eqn:QV;try discriminate;injection S as <- <-;eapply qword_wf;eassumption].
 all: try match type of S with context[VectorMoves.writing ?i]=>destruct (VectorMoves.writing i) end.
 all: try match type of S with context[if ?b then Some _ else Some _]=>destruct b end.
 all: try match type of S with context[option_map _ ?b]=>destruct b as [[]|];try discriminate end.
 all: try match type of S with context[if ?align then Some (_,_) else None]=>destruct align;try discriminate end.
 all: try (injection S as <- <-;cbn [cpu_state]).
 all: try solve [apply set_wf;[exact W|pose proof (Z.mod_pos_bound (mem s (effective s a)) 256 ltac:(lia));unfold word64;lia]].
 all: try solve [exact W | apply set_wf;[exact W|apply read_word_bound,W] | apply low8_words,W |
     apply set_wf;[exact W|apply mod64_word] | apply set_wf;[exact W|apply mod32_word] |
     apply set_wf;[exact W|unfold word64;lia] | apply set_wf;[exact W|pose proof (Z.mod_pos_bound (regs s src) 256 ltac:(lia));unfold word64;lia] | apply wf_copy,W | apply pop_words,W | apply push_wf,W].
 all: try solve [apply commit_words;[exact W|intros;apply word_byte_bound]|
   apply commit_words;[exact W|intros;apply Z.mod_pos_bound;lia]].
 all: try solve [apply set_vector_words;[exact W|intros;apply W]|
   apply set_vector_words;[exact W|intros;apply mod64_word]|
   apply set_vector_words;[exact W|intros;apply read_word_bound,W]|
   apply set_vector_words;[exact W|intros;destruct (_<?_)%nat;[apply read_word_bound,W|unfold word64;lia]]].
 - apply set_wf;[exact W|]. pose proof (Z.mod_pos_bound (regs s 0%nat) (2^32) ltac:(lia)).
   change (word64 ((regs s 0%nat mod 2^32)/2));unfold word64;split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia.
 - destruct a;apply set_wf;[exact W|apply mod64_word].
 - destruct op;injection S as <- <-;cbn [cpu_state];try solve [apply indexed_words,W].
   all: apply commit_words;[exact W|intros;apply word_byte_bound].
 - destruct W as [G [V M]];split;[exact G|split;[|exact M]];intros j r J;cbn [vectors].
   match goal with |- context[if ?b then _ else _]=>destruct b end;[unfold word64;lia|apply V,J].
 - apply set_wf;[exact W|]. pose proof(read_le_bound 4 (mem s) (effective s a) (proj2(proj2 W))) as H.
   exact (conj (proj1 H) (Z.lt_trans _ 4294967296 (2^64) (proj2 H) ltac:(vm_compute;reflexivity))).
Qed.

Lemma fetched_wf o text s t ws : well_formed(cpu_state s) -> ScalarBytes.fetch o text s=Some(t,ws) ->
 well_formed(cpu_state t).
Proof.
 intros W;unfold ScalarBytes.fetch;destruct (loc s);try discriminate;
   destruct (_<?_);try discriminate;destruct (decode _) as [[n op]|];try discriminate.
 exact (step_wf _ _ _ _ _ _ _ _ W).
Qed.
Lemma mapped_run_wf o len n : forall s t ws,well_formed(cpu_state s) ->
 run n (MappedFetch.fetch o len) s=Some(t,ws) -> well_formed(cpu_state t).
Proof.
 induction n as [|n IH];intros s t ws W R;[injection R as <- <-;exact W|].
 cbn [run] in R;destruct (MappedFetch.fetch _ _ s) as [[u own]|] eqn:F;[|discriminate].
 destruct (run n _ u) as [[v tail]|] eqn:T;[|discriminate].
 injection R as <- _;exact (IH _ _ _ (fetched_wf _ _ _ _ _ W F) T).
Qed.
Lemma segment_wf origin text n p q : well_formed(machine p) -> segment origin text n p=Some q ->
 well_formed(machine q).
Proof.
 intros W;unfold segment;destruct(run _ _ _) as [[s ws]|] eqn:Steps;[|discriminate].
 intro F;injection F as <-;exact (mapped_run_wf _ _ _ (State (Running (ip p-origin)) (machine p) (carry p)) _ _ W Steps).
Qed.

Lemma returning_wf origin size fuel p q : well_formed(machine p) -> returning origin size fuel p=Some q ->
 well_formed(machine q).
Proof.
 intros W;unfold returning;destruct(until_return _ _ _) as [[s ws]|] eqn:R;[|discriminate].
 intro Out;injection Out as <-;destruct(returned_run _ _ _ _ _ _ R) as [n [back [_ [Run _]]]].
 exact(mapped_run_wf _ _ _ (State(Running(ip p-origin)) (machine p) (carry p)) s ws W Run).
Qed.
