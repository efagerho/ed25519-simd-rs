From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.WordBounds execution.IndexedLoads
 execution.Packed execution.MaskedWords memory.ByteMemory.
Local Open Scope Z_scope.

Definition fits_word x:=(0<=?x)&&(x<?2^64).
Lemma fits_word_ok x : fits_word x=true -> word64 x.
Proof. unfold fits_word,word64;rewrite andb_true_iff,Z.leb_le,Z.ltb_lt;auto. Qed.

(* Certificates for the scalar and vector result expressions of a decoded
   fragment. Address intermediates can exceed a machine word before masking. *)
Definition indexed (e:term) := match e with
 | K n=>fits_word n | G _ | W64 _ | W32 _=>true | V _ j=>(j<?8)%nat
 | Read n _=>(n<=?8)%nat | _=>false end.
Lemma indexed_ok s e : well_formed s -> indexed e=true -> word64(eval s e).
Proof.
 intros [GPR [Vec B]] Ok;destruct e;cbn [indexed] in Ok;try discriminate;cbn [eval].
 - apply fits_word_ok,Ok.
 - apply GPR.
 - apply Vec,Nat.ltb_lt,Ok.
 - apply mod64_word.
 - apply mod32_word.
 - apply Nat.leb_le in Ok;pose proof(read_le_bound width (mem s) (eval s e) B) as [L H].
   unfold word64;split;[exact L|eapply Z.lt_le_trans;[exact H|change (256^Z.of_nat width<=256^8);apply Z.pow_le_mono_r;lia]].
Qed.

Fixpoint packed (e:Packed.expr) := match e with
 | Lit n=>fits_word n | Acc | Packed.Load _ _ | Packed.Add _ _ | LeftQ _ _ | Octet _ _ | SubB _ _=>true
 | Initial _ j=>(j<?8)%nat | RightQ a _=>packed a | AndB _ b=>packed b end.
Lemma packed_ok s e : well_formed s -> packed e=true -> word64(Packed.value s e).
Proof.
 intros [GPR [Vec B]];induction e;cbn [packed Packed.value];intro Ok.
 - apply fits_word_ok,Ok.
 - apply GPR.
 - apply Vec,Nat.ltb_lt,Ok.
 - apply read_word_bound,B.
 - apply low64_word.
 - apply low64_word.
 - apply shr_word,IHe,Ok.
 - pose proof(word_byte_bound (Packed.value s e) (Z.of_nat k));unfold word64;lia.
 - apply and_word,IHe2,Ok.
 - pose proof(Z.mod_pos_bound (Packed.value s e1-Packed.value s e2) 256 ltac:(lia));unfold word64;lia.
Qed.

Definition lane_words (l:lane) := word64(rax l) /\ forall r,word64(zmm l r).
Definition literal op := match op with MoveImm _ n=>fits_word n | _=>true end.
Lemma masked_step lo rd l op : lane_words l -> literal op=true -> lane_words (MaskedWords.step lo rd l op).
Proof.
 intros [A V] Ok;destruct op;cbn [literal] in Ok;cbn [lane_words MaskedWords.step rax zmm];
 unfold Packed.update;split;try assumption;try apply fits_word_ok,Ok;
 intro r;cbn [zmm];repeat match goal with |-context[if ?b then _ else _]=>destruct b end;
 try solve [apply V|apply xor_word;apply V|apply low64_word|exact A].
Qed.
Lemma masked_code ops : forall l lo rd, lane_words l -> forallb literal ops=true ->
 lane_words(fold_left (MaskedWords.step lo rd) ops l).
Proof.
 induction ops as [|op ops IH];intros;[assumption|]. cbn [forallb] in *.
 apply andb_true_iff in H0 as [Head Rest];apply IH;[apply masked_step;assumption|exact Rest].
Qed.
