From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory WordBounds ByteMemory ExecutionProperties.
Import ListNotations. Open Scope Z_scope.

(* The placement-specific premises are supplied by each routine's ABI proof.
   Balanced stack events and the actual recorded path determine every pop. *)
Theorem recorded_frame fuel p l c last es d loc allowed tracked writable sp live before :
 record_path fuel p l c=Some(last,es) ->
 writes_only allowed es -> balanced live es ->
 agrees loc tracked d (return_memory c) before ->
 separated loc allowed tracked ->
 (forall ops x, writes_only allowed ops -> writes_at loc ops x -> writable x) ->
 (forall k, 0<=k<8 -> ~writable(sp+k)) ->
 (forall a, In a (map fst live) -> tracked(ReturnSlot a)) ->
 (forall a, allowed(ReturnSlot a) -> tracked(ReturnSlot a)) ->
 let after:=replay p loc es d before in
 agrees loc tracked (effects p(data_effects es)d) (return_memory last) after /\
 (forall x, ~writable x -> after x=before x) /\
 (forall pre tail, es=pre++tail ->
  agrees loc tracked (effects p(data_effects pre)d)
   (fold_left update_slots pre(return_memory c)) (replay p loc pre d before) /\
  forall k,0<=k<8 -> replay p loc pre d before(sp+k)=before(sp+k)) /\
 (forall pre a t tail k,es=pre++Pop a t::tail ->0<=k<8 ->
  replay p loc pre d before(address_of loc a+k)=word_byte(pc_word loc t)k).
Proof.
 intros R W B M Sep Permitted Protected Live Pushed; cbn zeta.
 destruct(record_path_sound _ _ _ _ _ _ R)as[_[Slots Reads]].
 assert(Prefix:forall pre tail,es=pre++tail ->
 agrees loc tracked(effects p(data_effects pre)d)
 (fold_left update_slots pre(return_memory c))(replay p loc pre d before)).
 { intros pre tail ->;apply Forall_app in W as[W _];eapply replay_agrees;eassumption. }
 split;[rewrite <-Slots;eapply replay_agrees;eassumption|].
 split;[intros x Outside;apply replay_frame;intro I;apply Outside;eapply Permitted;eassumption|].
 split.
 { intros pre tail E;split;[exact(Prefix _ _ E)|]. intros k K;apply replay_frame;intro I.
   apply(Protected _ K);rewrite E in W;apply Forall_app in W as[W _];eapply Permitted;eassumption. }
 intros pre a t tail k E K;specialize(Prefix _ _ E).
 assert(I:In(Pop a t)es)by(rewrite E;apply in_or_app;right;now left).
 assert(Map:tracked(ReturnSlot a)).
 { destruct(balanced_pop_location _ _ _ _ B I)as[A|[u P]].
   - now apply Live.
   - apply Pushed;apply Forall_forall with(x:=Push a u)in W;assumption. }
 rewrite E,reads_app in Reads;destruct Reads as[_[Read _]].
 apply(Prefix(ReturnSlot a)k _ Map K);unfold cell_byte;now rewrite Read.
Qed.

Definition vector_reads loc tracked d flat := forall a j,
 tracked(VectorCell a) -> (j<8)%nat ->
 read_word flat(address_of loc a+8*Z.of_nat j)=memory d a j.
Definition byte_execution p l loc tracked writable initial final before after :=
 (forall middle,reaches p l initial middle ->state_words middle) /\
 byte_memory after /\ vector_reads loc tracked(snd final)after /\
 (forall x,~writable x ->after x=before x) /\
 exists fuel es,record_path fuel p l(fst initial)=Some(fst final,es) /\
 after=replay p loc es(snd initial)before /\
 (forall pre tail,es=pre++tail ->
 let d:=effects p(data_effects pre)(snd initial)in
 let flat:=replay p loc pre(snd initial)before in
 data_words d /\byte_memory flat /\vector_reads loc tracked d flat) /\
 (forall pre a t tail,es=pre++Pop a t::tail ->
 read_word(replay p loc pre(snd initial)before)(address_of loc a)=pc_word loc t mod 2^64).

Theorem recorded_bytes fuel p l loc tracked writable initial final before es :
 reaches p l initial final -> state_words initial -> byte_memory before ->
 record_path fuel p l(fst initial)=Some(fst final,es) ->
 agrees loc tracked(snd final)(return_memory(fst final))(replay p loc es(snd initial)before) ->
 (forall x,~writable x ->replay p loc es(snd initial)before x=before x) ->
 (forall pre tail,es=pre++tail ->
 agrees loc tracked(effects p(data_effects pre)(snd initial))
 (fold_left update_slots pre(return_memory(fst initial)))(replay p loc pre(snd initial)before)) ->
 (forall pre a t tail k,es=pre++Pop a t::tail ->0<=k<8 ->
 replay p loc pre(snd initial)before(address_of loc a+k)=word_byte(pc_word loc t)k) ->
 byte_execution p l loc tracked writable initial final before(replay p loc es(snd initial)before).
Proof.
 intros R W Bytes Trace A Outside Prefixes Pops.
 pose proof(execution_preserves_words _ _ _ _ R W)as Final.
 split;[intros middle Reach;eapply execution_preserves_words;eassumption|].
 split;[now apply replay_well_formed|].
 split;[intros a j M J;eapply agrees_read_vector;eauto;exact(proj2 Final)|].
 split;[exact Outside|];exists fuel,es;split;[exact Trace|];split;[reflexivity|];split.
 - intros pre tail E.
   assert(D:data_words(effects p(data_effects pre)(snd initial)))by
     (destruct initial;eapply recorded_prefix_words;eassumption).
   split;[exact D|];split;[now apply replay_well_formed|].
   intros a j M J;eapply agrees_read_vector;eauto;exact(Prefixes _ _ E).
 - intros pre a t tail E;apply read_word_encoded;intros k K;exact(Pops _ _ _ _ _ E K).
Qed.


Lemma read_buffer_vector loc tracked d flat region k :
 vector_reads loc tracked d flat ->tracked(VectorCell(region,64*Z.of_nat(k/8))) ->
 buffer_words flat(origin loc region)k=memory d(region,64*Z.of_nat(k/8))(k mod 8)%nat.
Proof.
 intros Reads M;unfold buffer_words;rewrite <-vector_word_address.
 apply Reads;[exact M|apply Nat.mod_upper_bound;lia].
Qed.
