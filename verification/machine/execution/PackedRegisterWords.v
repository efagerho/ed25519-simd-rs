From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.ProgramLayout execution.LinkedCalls execution.WordBounds execution.Packed
 memory.FlatMemory memory.ByteMemory.
From Machine Require execution.IndexedRegisterWords.
Local Open Scope Z_scope.

Definition octet x:=0<=x<256.
Definition bounded s v:=match v with
 | Words f=>forall j,(j<8)%nat -> word64(value s (f j))
 | Bytes f=>forall i,(i<64)%nat -> octet(value s (f i)) end.

Lemma qword_ok s v : bounded s v -> forall j,(j<8)%nat -> word64(value s (qword v j)).
Proof. destruct v as [f|f];intros B j J;[apply B,J|apply low64_word]. Qed.
Lemma byte_ok s v : bounded s v -> forall i,(i<64)%nat -> octet(value s (byte v i)).
Proof. destruct v as [f|f];intros B i I;[apply word_byte_bound|apply B,I]. Qed.
Lemma and_octet a b : octet b -> octet (Z.land a b).
Proof.
 intro B;assert (M:Z.land b (Z.ones 8)=b) by (rewrite Z.land_ones,Z.mod_small;unfold octet in *;lia).
 rewrite <-M,Z.land_assoc,Z.land_ones by lia;apply Z.mod_pos_bound;lia.
Qed.
Record words s st:=WordsOK {
 accumulator:word64(value s (acc st));
 registers:forall r,bounded s (zmm st r);
 memory_rows:forall row v,stores st row=Some v -> bounded s v
}.
Lemma set_vector s st d v : words s st -> bounded s v -> words s (putv st d v).
Proof.
 intros [A V M] B;constructor;[exact A|exact (IndexedRegisterWords.update _ _ _ (bounded s) V B)|exact M].
Qed.
Lemma store_ok s st row r : words s st ->
 words s (State (acc st) (zmm st) (update (stores st) row (Some(zmm st r)))).
Proof. intros [A V M];constructor;[exact A|exact V|intros i v];unfold update;cbn [stores];unfold update;destruct (_=?_)%nat;[intros E;injection E as <-;apply V|apply M]. Qed.
Definition literals op:=match op with Imm _ n=>word64 n | _=>True end.

Lemma step_words s st op : well_formed s -> words s st -> literals op -> words s (step st op).
Proof.
 intros W OK Lit;pose proof(registers _ _ OK) as V.
 destruct op;cbn [step];try solve [apply store_ok,OK].
 - constructor;[exact Lit|exact V|exact (memory_rows _ _ OK)].
 - apply set_vector;[exact OK|destruct octets;cbn [bounded];intros;[apply word_byte_bound|apply (accumulator _ _ OK)]].
 - apply set_vector;[exact OK|intros j J;apply low64_word].
 - apply set_vector;[exact OK|intros j J;apply low64_word].
 - apply set_vector;[exact OK|intros j J;destruct left;[apply low64_word|apply shr_word,qword_ok;auto]].
 - apply set_vector;[exact OK|intros i I;apply and_octet,byte_ok;auto].
 - apply set_vector;[exact OK|intros i I;apply Z.mod_pos_bound;lia].
 - apply set_vector;[exact OK|intros i I;destruct (Nat.even i);apply byte_ok;try apply V].
   all:pose proof(Nat.mod_upper_bound i 16 ltac:(lia));assert ((i/16<4)%nat) by (apply Nat.div_lt_upper_bound;lia);
     assert ((i mod 16/2<8)%nat) by (apply Nat.div_lt_upper_bound;lia);destruct high;lia.
 - apply set_vector;[exact OK|intros i I;unfold unpack_source;apply byte_ok;try apply V].
   assert (J:(i/8<8)%nat) by (apply Nat.div_lt_upper_bound;lia).
   pose proof(IndexedRegisterWords.unpack_range high _ J);pose proof(Nat.mod_upper_bound i 8 ltac:(lia));lia.
 - apply set_vector;[exact OK|intros i I;unfold shuffle_source;apply byte_ok;try apply V].
   pose proof(IndexedRegisterWords.shuffle_range imm (i/8));pose proof(Nat.mod_upper_bound i 8 ltac:(lia));lia.
 - constructor;[exact (accumulator _ _ OK)| |exact (memory_rows _ _ OK)];intro r;cbn [zmm].
   destruct (r<?16)%nat;[intros j J;destruct (j<?2)%nat;[apply qword_ok;auto|unfold word64;cbn;lia]|apply V].
Qed.

Lemma initial_words s : well_formed s -> words s initial.
Proof. intro W;constructor;[apply W|intros r j J;apply W,J|intros r v E;discriminate]. Qed.

Theorem execute_words rows ops s : well_formed s -> Forall literals ops -> well_formed (execute rows ops s).
Proof.
 intros W L;assert (K:words s (fold_left step ops initial)).
 { pose proof(initial_words _ W) as Start;revert Start;generalize initial.
   induction L as [|op rest H T IH];intros st K;[exact K|apply IH,step_words;assumption]. }
 set (st:=fold_left step ops initial) in *;split;[|split].
 - intro r;change (word64(update (regs s) 0 (value s (acc st)) r));unfold update;destruct (_=?_)%nat;[exact (accumulator _ _ K)|apply W].
 - intros j r J;apply qword_ok;[exact (registers _ _ K r)|exact J].
 - intro x;unfold execute,finish;fold st;cbn [mem].
   destruct (_ && _)%bool;[|apply W];destruct (stores st _) as [v|] eqn:Row;[|apply W].
   apply byte_ok;[eapply (memory_rows _ _ K);exact Row|pose proof (Z.mod_pos_bound (x-regs s 7%nat) 64 ltac:(lia));lia].
Qed.
