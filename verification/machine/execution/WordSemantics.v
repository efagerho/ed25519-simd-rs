From Coq Require Import ZArith Lia.
From Machine Require Import isa.Instructions memory.ByteMemory memory.FlatMemory.
Local Open Scope Z_scope.

Definition word n := n mod 2^64.

Lemma small_relative o a b : -2^62<a<2^62 -> 0<=b<2^32 -> word(o+a)-o=b -> a=b.
Proof.
 intros A B Eq;unfold word in Eq;pose proof(Z.div_mod (o+a) (2^64) ltac:(lia)) as D.
 assert ((o+a)/2^64=0) by lia;lia.
Qed.
Definition signed_value half n := let u := n mod (2*half) in
 if u <? half then u else u-2*half.

(* These instructions preserve flags, vector registers and all unmentioned
   state. Callers supply only the registers and bytes they actually read. *)
Inductive register_source :=
| FromRegister (src : nat)
| Unsigned32 (imm : Z)
| EffectiveAddress (base : nat) (disp : Z).

Definition register_write (rs : nat -> Z) dst src :=
 put rs dst (match src with
 | FromRegister r => rs r
 | Unsigned32 n => word (n mod 2^32)
 | EffectiveAddress b n => word (rs b + signed_value (2^31) n)
 end).

Definition store_word flat addr value := write_bytes flat addr 8 (word_byte value).
Definition push_words (rs : nat -> Z) flat value :=
 let sp := word (rs 4%nat - 8) in
 (put rs 4 sp, store_word flat sp value).
Definition advance_rsp (rs : nat -> Z) := put rs 4 (word (rs 4%nat + 8)).
Definition stack_top (rs : nat -> Z) flat := read_word flat (word (rs 4%nat)).

Inductive stack_instruction :=
| PushRegister (r : nat) | PopRegister (r : nat)
| NearCall (disp : Z) | NearReturn.

Record word_result := WordResult { target_ip : Z; result_regs : nat -> Z; result_mem : bytes }.

(* next is the link-time fallthrough address. bias relocates the image. *)
Definition stack_step bias next op (rs : nat -> Z) flat :=
 let push ip value := let '(rs', flat') := push_words rs flat value in
                      WordResult (word ip) rs' flat' in
 match op with
 | PushRegister r => push (bias+next) (rs r)
 | PopRegister r => WordResult (word (bias+next))
      (put (advance_rsp rs) r (stack_top rs flat)) flat
 | NearCall d => push (bias+(next+signed_value (2^31) d)) (bias+next)
 | NearReturn => WordResult (word (stack_top rs flat)) (advance_rsp rs) flat
 end.
