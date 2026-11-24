From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.X86 isa.Instructions execution.LinkedCalls execution.WordSemantics
 execution.MaskTrace execution.CircuitFacts execution.MappedFetch execution.LinkedRun memory.ByteMemory.
Import ListNotations. Local Open Scope Z_scope.

(* The separate opmask bank is explicit on both sides of each instruction.
   Every transfer checks its full encoding at the current absolute RIP. *)
Definition bank := (nat->nat->bool)%type.
Inductive transfer := Signs (k src:nat) | ToGpr (dst k:nat).
Definition ToEax := ToGpr 0.
Definition encoding op := match op with
 | Signs k src=>rr 2 2 0x39 k 0 src | ToGpr dst k=>MaskTrace.kmov_to_gpr dst k end.
Definition valid op := match op with Signs k src=>(k<?8)%nat && (src<?32)%nat | ToGpr dst k=>(dst<?16)%nat && (k<?8)%nat end.
Definition sign_bits s r j := (j<?8)%nat && Z.testbit (vectors s j r) 63.
Definition mask16 (b:nat->bool) := mask_word 16 (fun j=>Z.b2z (b j)).
Definition effect s (ks:bank) op := match op with
 | Signs k src=>(s,put ks k (sign_bits s src))
 | ToGpr dst k=>(set s dst (mask16 (ks k)),ks) end.
Definition tick op p (ks:bank) :=
 let bs:=encoding op in if valid op then
 if list_eq_dec Z.eq_dec (snapshot (mem(machine p)) (ip p) (length bs)) bs then
 let '(t,next):=effect (machine p) ks op in Some(Cursor (word(ip p+Z.of_nat(length bs))) t (carry p) (log p),next)
 else None else None.

Lemma fetched op p ks : valid op=true -> mapped (mem(machine p)) (ip p) (encoding op) ->
 tick op p ks=let '(t,next):=effect (machine p) ks op in
 Some(Cursor (word(ip p+Z.of_nat(length(encoding op)))) t (carry p) (log p),next).
Proof.
 intros V Map;unfold tick;rewrite V,(snapshot_mapped _ _ _ Map);destruct(list_eq_dec _ _ _);congruence.
Qed.
Local Lemma bit_iff a b : (a=true <-> Z.b2z b=1) -> a=b.
Proof. destruct a,b;cbn [Z.b2z];intuition discriminate. Qed.
Lemma kmov_value b : 0<=mask16 b<2^16 /\ forall j,(j<16)%nat -> Z.testbit (mask16 b) (Z.of_nat j)=b j.
Proof.
 destruct(mask_word_bits 16 (fun j=>Z.b2z(b j))
   ltac:(intros j J;cbv beta;destruct(b j);[right|left];reflexivity)) as [V Bits].
 split;[exact V|intros j J;apply bit_iff;exact (Bits j J)].
Qed.
Example kmov_extended_register : encoding (ToGpr 10 2)=[0xc5;0x78;0x93;0xd2].
Proof. reflexivity. Qed.
Lemma low_mask_byte b : (forall j,(8<=j)%nat -> b j=false) -> 0<=mask16 b<256.
Proof.
 intro High;set (f:=fun j=>Z.b2z(b j)).
 assert (Tail:forall n,mask_word (n+8) f=mask_word 8 f).
 { induction n as [|n IH];[reflexivity|].
   change (mask_word (n+8) f+f (n+8)%nat*2^Z.of_nat(n+8)=mask_word 8 f).
   rewrite IH;unfold f;rewrite High by lia;cbn [Z.b2z];ring. }
 change (0<=mask_word (8+8) f<256);rewrite (Tail 8%nat).
 apply (proj1(mask_word_bits 8 f ltac:(intros j J;unfold f;destruct(b j);[right|left];reflexivity))).
Qed.
Lemma sign_word s src : 0<=mask16 (sign_bits s src)<256 /\ forall j,(j<8)%nat ->
 Z.testbit (mask16 (sign_bits s src)) (Z.of_nat j)=Z.testbit (vectors s j src) 63.
Proof.
 split;[apply low_mask_byte;intros j J;unfold sign_bits;now rewrite (proj2(Nat.ltb_ge j 8) J)|].
 intros j J;rewrite (proj2(kmov_value _) j ltac:(lia));unfold sign_bits;now rewrite (proj2(Nat.ltb_lt j 8) J).
Qed.

Lemma subimage m base text off fragment : mapped m base text ->
 (off+length fragment<=length text)%nat -> firstn (length fragment) (skipn off text)=fragment ->
 mapped m (base+Z.of_nat off) fragment.
Proof.
 intros Map Len Bound j J;replace (base+Z.of_nat off+Z.of_nat j) with (base+Z.of_nat(off+j)) by lia.
 rewrite Map by lia;rewrite <-Bound;rewrite nth_firstn,nth_skipn,(proj2(Nat.ltb_lt _ _) J);reflexivity.
Qed.
