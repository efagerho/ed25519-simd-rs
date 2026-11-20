From Coq Require Import List ZArith Bool.
From Machine Require Import isa.Instructions execution.Blocks.

(* Calling a verified block routine from a concrete word machine requires
   concrete final GPRs. No successful instruction manufactures Unknown. *)
Definition known_registers c := forall r,gpr c r<>Unknown.
Local Lemma put_known rs i v : (forall r,rs r<>Unknown) -> v<>Unknown ->
 forall r,put rs i v r<>Unknown.
Proof. intros R V r;unfold put;destruct Nat.eqb;auto. Qed.
Local Ltac preserve_known :=
 inversion 1;subst;unfold known_registers;cbn [set_gpr gpr];
 repeat first [assumption|apply put_known|discriminate].
Lemma op_known p l c op mid es : known_registers c ->
 exec_op p l c op=Some(mid,es) -> known_registers mid.
Proof.
 intros K;destruct op;cbn [exec_op];repeat match goal with
 | |- context [match ?v with _ => _ end] => destruct v eqn:?
 end;try discriminate;unfold known_registers in K;preserve_known.
 apply K.
Qed.
Lemma body_known p l c ops mid es : known_registers c ->
 exec_body p l c ops=Some(mid,es) -> known_registers mid.
Proof.
 revert c es;induction ops as [|op tail IH];intros c es K;cbn [exec_body].
 - intros [= <- _];exact K.
 - destruct(exec_op p l c op)as[[next head]|]eqn:O;try discriminate.
   destruct(exec_body p l next tail)as[[last events]|]eqn:B;try discriminate.
   intros [= -> _];eapply IH;[eapply op_known;eassumption|exact B].
Qed.
Lemma transfer_known l c next e last :
 known_registers c -> transfer l c next e=Some last -> known_registers last.
Proof.
 intros K;unfold known_registers in K;destruct e;unfold transfer,transfer_recorded;
 cbn beta iota zeta;repeat match goal with
 | |- context [match ?v with _ => _ end] => destruct v eqn:?
 end;try discriminate;preserve_known.
Qed.
Lemma step_known p l s t : known_registers(fst s) ->
 step p l s=Some t -> known_registers(fst t).
Proof.
 destruct s as[c d];cbn [fst];intros K;unfold step,dispatch;cbn [fst snd].
 destruct(rip c)as[pc| |n];try discriminate.
 destruct(lookup(sections p)pc)as[b|];try discriminate;unfold block_control.
 destruct(exec_body p l c(body b))as[[m es]|]eqn:B;try discriminate.
 destruct(transfer l m (after p b)(terminator b))as[last|]eqn:T;try discriminate.
 intros [= <-];eapply transfer_known;[eapply body_known;eassumption|exact T].
Qed.
Theorem reaches_known p l s t : reaches p l s t ->
 known_registers(fst s) -> known_registers(fst t).
Proof. induction 1;intros K;[exact K|apply IHreaches;eapply step_known;eassumption]. Qed.
