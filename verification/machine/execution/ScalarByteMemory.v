From Coq Require Import List ZArith Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.ScalarBytes
 execution.MappedFetch execution.StoreInstructions memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Machine Require isa.VectorMoves.
Local Open Scope Z_scope.

(* Memory remains byte-valued independently of the caller's register file. *)
Lemma step_bytes o off n op s c t ws : byte_memory (mem s) ->
 step o off n op s c=Some(t,ws) -> byte_memory(mem(cpu_state t)).
Proof.
 intros B;destruct op;cbn [step];intro R.
 all: try solve [destruct (qword_op _ _ _) as [v|] eqn:QV;try discriminate;injection R as <- <-;cbn [cpu_state];rewrite (proj1(qword_state _ _ _ _ QV));exact B].
 all: try match type of R with context[VectorMoves.writing ?i]=>destruct (VectorMoves.writing i) end.
 all: try match type of R with context[if ?b then Some _ else Some _]=>destruct b end.
 all: try match type of R with context[option_map _ ?b]=>destruct b as [[]|];try discriminate end.
 all: try match type of R with context[if ?b then Some (_,_) else None]=>destruct b;try discriminate end.
 all: try (injection R as <- <-;cbn [cpu_state]).
 all: try exact B.
 all: try solve [apply write_bytes_well_formed;[exact B|intros;apply word_byte_bound]|
   apply write_bytes_well_formed;[exact B|intros;apply Z.mod_pos_bound;lia]].
 destruct op;injection R as <- <-;try exact B.
 all: apply write_bytes_well_formed;[exact B|intros;apply word_byte_bound].
Qed.

Lemma fetched_bytes o text s t ws : byte_memory(mem(cpu_state s)) ->
 ScalarBytes.fetch o text s=Some(t,ws) -> byte_memory(mem(cpu_state t)).
Proof.
 intro B;unfold ScalarBytes.fetch;destruct(loc s);try discriminate;destruct (_<?_);try discriminate.
 destruct(decode _) as [[n op]|];try discriminate;apply step_bytes,B.
Qed.
Theorem run_bytes n o len : forall s t ws,byte_memory(mem(cpu_state s)) ->
 run n (MappedFetch.fetch o len) s=Some(t,ws) -> byte_memory(mem(cpu_state t)).
Proof.
 induction n as [|n IH];intros s t ws B R;[injection R as <- <-;exact B|].
 cbn [run] in R;destruct(MappedFetch.fetch _ _ s) as [[u own]|] eqn:F;[|discriminate].
 destruct(run n _ u) as [[v tail]|] eqn:T;[|discriminate].
 injection R as <- _;exact (IH _ _ _ (fetched_bytes _ _ _ _ _ B F) T).
Qed.
