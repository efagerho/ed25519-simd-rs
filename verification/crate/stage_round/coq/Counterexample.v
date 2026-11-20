From Coq Require Import List ZArith Lia Bool.
From Machine Require Import execution.IndexedLoads execution.LinkedCalls memory.ByteMemory
  memory.MemoryGeometry memory.FlatMemory execution.WordBounds.
From Ed25519Simd.StageRound Require Import Program Audit MutantBytes.
Import ListNotations. Local Open Scope Z_scope.

(* Each mutant has its own Program.v and linked ELF. The failure below
   uses stage_correct on an admissible call, independently of linked_code. *)
Example changed_code_is_bound : image=symbol_bytes /\ valid_code=true.
Proof. vm_compute;split;reflexivity. Qed.

Definition arg r : Z := match r with
 | 7%nat=>4096 | 6%nat=>8192 | 2%nat=>32768 | 1%nat=>69632
 | 8%nat=>70656 | 4%nat=>73736 | _=>0 end.
Definition sample := CPU arg (fun _ _=>0) None (fun x=>
 if (8192<=?x) && (x<?8256) then word_byte 16384 (x mod 8)
 else if (69632<=?x) && (x<?70144) then 0
 else if (70656<=?x) && (x<?71168) then 248 else x mod 251).
Ltac each_lane l :=
 do 8 (destruct l as [|l];[vm_compute;intuition discriminate|]);lia.
Lemma sample_keys l : (l<8)%nat -> key_table sample l=16384.
Proof. intro L;each_lane l. Qed.
Lemma placed : placement 77824 (Z.of_nat (length symbol_bytes)) sample.
Proof.
 constructor.
 1-6: vm_compute;intuition discriminate.
 - intros l L;rewrite sample_keys by assumption;vm_compute;intuition discriminate.
 - vm_compute;intuition discriminate.
 - intros r [->| ->];vm_compute;intuition discriminate.
 - vm_compute;intuition discriminate.
 - intros r l p R L J;assert (p=0 \/ p=1) by lia.
   destruct R as [->| ->], H as [->| ->];each_lane l.
Qed.
Lemma formed : well_formed sample.
Proof.
 split;[intros r;do 9 (destruct r as [|r];[vm_compute;intuition discriminate|]);vm_compute;intuition discriminate|].
 split;[intros;vm_compute;intuition discriminate|].
 intro x;cbn [sample mem];repeat destruct (_ && _)%bool;
 auto using word_byte_bound;try lia;pose proof (Z.mod_pos_bound x 251 ltac:(lia));lia.
Qed.
Definition before := IndexedLoads.execute prefix sample.
Definition last_load := hd (K 0,0%nat) (loads (summary (load_block Odd))).
Lemma last_seen : In last_load (loads (summary (load_block Odd))).
Proof. apply in_eq. Qed.
(* With −8 in every key lane, the selected [8]P occupies bytes
   18944..19103. The damaged 32-byte load starts at 19104. *)
Lemma read_extent_violation : mutation=2%nat ->
 ~ input_access sample Odd (eval before (fst last_load)) (snd last_load).
Proof.
 intro M;try discriminate.
all: change (~input_access sample Odd 19104 32).
all: assert (S:forall l, (l<8)%nat -> selected sample Odd l=18944) by (intros l L;each_lane l).
all: intros [l [L Bounds]];change (within 19104 32 (selected sample Odd l) 160) in Bounds;
 rewrite S in Bounds by exact L;unfold within in Bounds;lia.
Qed.
Definition wrong_first_word :=
 let out:=snd (run 77824 sample) in
 read_word (mem out) 4096 <> read_word (mem sample) (selected sample Odd 0).
Lemma routed_word_violation : mutation<>2%nat -> wrong_first_word.
Proof. intro M;first [exfalso;apply M;reflexivity|vm_compute;discriminate]. Qed.

Theorem mutated_public_contract_fails : ~stage_contract symbol_bytes.
Proof.
 intro H;destruct (stage_correct _ H 77824 sample placed formed)
 as [Reads [_ [_ [_ [_ [_ [_ [_ Words]]]]]]]].
 destruct (Nat.eq_dec mutation 2) as [M|M].
 - apply (read_extent_violation M);destruct last_load as [a n] eqn:E;cbn [fst snd].
   apply Reads;pose proof last_seen as I;now rewrite E in I.
 - apply (routed_word_violation M);exact (Words Odd 0%nat 0%nat ltac:(cbn;lia) ltac:(lia)).
Qed.
