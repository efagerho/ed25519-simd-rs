From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords
 execution.WordBounds execution.VectorProcedure execution.CircuitFacts memory.ByteMemory.
From Machine Require execution.MaskTransfer.
From Ed25519Simd.VerifyBatch Require Import BatchDecode DecoderSave KeySquare
 SetupTail PairedSetup DecoderPower.
From Ed25519Simd.VerifyBatch Require DecoderKernel DecoderProduct DecoderUnpack.
Local Open Scope Z_scope.

Definition words (f:procedure):=forall p q,well_formed(machine p) -> f p=Some q -> well_formed(machine q).
Lemma sequence f g : words f -> words g -> words(then_run f g).
Proof. intros F G p q W;unfold then_run;destruct(f p) eqn:R;[now apply G,(F _ _ W R)|discriminate]. Qed.
Lemma block base text n : words(segment base text n).
Proof. exact (segment_wf base text n). Qed.
Lemma call base text retbase rettext f : words f -> words(wrapped base text retbase rettext f).
Proof. intro F;change (words(then_run (segment base text 1) (then_run f (segment retbase rettext 1))));
 apply sequence;[apply block|apply sequence;[exact F|apply block]]. Qed.

Lemma kernels bias : words(DecoderProduct.multiply_call bias) /\ words(square bias) /\ words(finish_setup bias).
Proof.
 unfold finish_setup,square,set_rhs,step_at,carry_call,DecoderProduct.multiply_call,DecoderProduct.multiply_body,
 DecoderProduct.product,DecoderProduct.columns,DecoderProduct.native.
 split;[|split];repeat first [apply sequence|apply call|apply block].
Qed.

Lemma mask_op op p bank q k : well_formed(machine p) -> MaskTransfer.tick op p bank=Some(q,k) -> well_formed(machine q).
Proof.
 intro W;unfold MaskTransfer.tick;destruct(MaskTransfer.valid _);[|discriminate].
 destruct(list_eq_dec _ _ _);[|discriminate];destruct op as [index src|dst index];intro R;injection R as <- <-;[exact W|].
 apply set_wf;[exact W|];pose proof(proj1(MaskTransfer.kmov_value (bank index)));unfold word64;lia.
Qed.
Lemma unpack_words bias p bank q k : well_formed(machine p) -> unpack bias p bank=Some(q,k) -> well_formed(machine q).
Proof.
 intro W;unfold unpack,DecoderUnpack.take_signs.
 destruct(MaskTransfer.tick (MaskTransfer.Signs 2 6) p bank) as [[a ma]|] eqn:A;[|discriminate].
 destruct(MaskTransfer.tick (MaskTransfer.ToEax 2) a ma) as [[b mb]|] eqn:B;[|discriminate].
 destruct(segment (bias+DecoderFrame.origin) DecoderFrame.code 15 b) as [t|] eqn:T;[|discriminate].
 intro Eq;injection Eq as <- <-;eapply segment_wf;[|exact T];eapply mask_op;[|exact B];eapply mask_op;eassumption.
Qed.
Lemma setup_square_words bias p bank q k : well_formed(machine p) -> square_input bias p bank=Some(q,k) ->
 well_formed(machine q).
Proof.
 intro W;unfold square_input,save_input;destruct(transpose bias p) as [v|] eqn:V;[|discriminate];cbn [bind].
 destruct(unpack bias v bank) as [[y ks]|] eqn:Y;[|discriminate];cbn [bind].
 destruct(preserve bias y) as [stored|] eqn:S;[|discriminate];cbn [bind option_map].
 destruct(square bias stored) as [sq|] eqn:Sq;[|discriminate];intro Eq;injection Eq as <- <-.
 eapply (proj1(proj2(kernels bias)));[|exact Sq];eapply segment_wf;[|exact S].
 eapply unpack_words;[|exact Y];eapply segment_wf;eassumption.
Qed.
Lemma input_words_after bias p bank r : well_formed(machine p) -> input_setup bias p bank=Some r ->
 well_formed(machine(in_decoder r)).
Proof.
 intro W;unfold input_setup;destruct(square_input bias p bank) as [[sq k]|] eqn:Sq;[|discriminate];cbn [bind].
 destruct(finish_setup bias sq) as [t|] eqn:T;[|discriminate];intro Eq;injection Eq as <-.
 eapply (proj2(proj2(kernels bias)));[|exact T];eapply setup_square_words;eassumption.
Qed.

Theorem pow2_entry_words bias p bank r : well_formed(machine p) -> DecoderPower.observe bias p bank=Some r ->
 well_formed(machine(exponent_entry r)).
Proof.
 intro W;unfold DecoderPower.observe,observe_pair,SetupTail.observe.
 destruct(inner bias p) as [a|] eqn:A;[|discriminate];cbn [bind].
 destruct(input_setup bias a bank) as [aa|] eqn:AA;[|discriminate];cbn [bind].
 destruct(next_input bias (in_decoder aa)) as [b|] eqn:B;[|discriminate];cbn [bind].
 destruct(input_setup bias b (masks aa)) as [bb|] eqn:BB;[|discriminate];cbn [bind option_map signature_r].
 destruct(DecoderPower.enter bias (in_decoder bb)) as [child|] eqn:C;[|discriminate];intro Eq;injection Eq as <-.
 eapply segment_wf;[|exact C];eapply input_words_after;[|exact BB];eapply segment_wf;[|exact B].
 eapply input_words_after;[|exact AA];eapply segment_wf;eassumption.
Qed.
