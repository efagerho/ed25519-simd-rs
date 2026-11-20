From Coq Require Import List ZArith Lia.
From Curve25519 Require Import SignedRadix16.
From Machine Require Import execution.IndexedLoads execution.LinkedCalls execution.WordSemantics
  memory.FlatMemory memory.MemoryGeometry memory.ByteMemory.
From Ed25519Simd.StageRound Require Import Program Audit Routing.
Import ListNotations. Local Open Scope Z_scope.

Definition advanced s r := if ((r =? 1)%nat || (r =? 8)%nat)%bool
  then regs s r + 2*regs s 9%nat else regs s r.
Record ready s st : Prop := {
  arguments : forall r, In r kept -> regs st r = advanced s r;
  unchanged : preserved (fun x=> ~destination s x) (mem s) (mem st)
}.
Lemma read_source s st b len a n : ready s st -> source s b len ->
  within a (Z.of_nat n) b len -> read_le n (mem st) a = read_le n (mem s) a.
Proof.
 intros R [_ D] W;apply (preserved_read _ _ _ _ _ (unchanged _ _ R)).
 unfold within in W;unfold destination,disjoint in *;intros;lia.
Qed.
Lemma unwrapped s b len a : source s b len -> b<=a<b+len -> word a=a.
Proof. intros [[L H] _] A;unfold word;apply Z.mod_small;lia. Qed.
Definition raw s r l p := mem s (digit_addr s r l p).
Definition legal b := 0<=b<256 /\ -8<=signed_byte b<8.
(* Exhaust the 16 legal signed-digit encodings, including the high nibble
   of each two’s-complement byte when the affine index folds two digits. *)
Definition alphabet := map (fun i=>(Z.of_nat i-8) mod 256) (seq 0 16).
Lemma member b : legal b -> In b alphabet.
Proof.
 intros [B D];apply in_map_iff;exists (Z.to_nat (signed_byte b+8)).
 split;[|apply in_seq;lia]. rewrite Z2Nat.id by lia.
 replace (signed_byte b+8-8) with (signed_byte b) by ring.
 unfold signed_byte;destruct (b<?128);[apply Z.mod_small;lia|].
 replace (b-256) with (b+(-1)*256) by ring;rewrite Z.mod_add,Z.mod_small by lia;reflexivity.
Qed.
Definition key_offset s b := eval s (key_calc (K b)).
Definition affine_offset s lo hi := eval s (base_calc (K (lo+256*hi))).
Lemma key_index s b : legal b -> key_offset s b = 160*(7-signed_byte b).
Proof.
 intro B;assert (H:forallb (fun x=>key_offset s x =? 160*(7-signed_byte x)) alphabet=true)
 by reflexivity.
 apply Z.eqb_eq,(proj1 (forallb_forall _ _) H),member,B.
Qed.
Lemma affine_index s lo hi : legal lo -> legal hi ->
  affine_offset s lo hi=120*(136+signed_byte lo+16*signed_byte hi).
Proof.
 intros L H;assert (E:forallb (fun x=>forallb (fun y=>affine_offset s x y =?
    120*(136+signed_byte x+16*signed_byte y)) alphabet) alphabet=true) by reflexivity.
 apply (proj1 (forallb_forall _ _)) with (x:=lo) in E;auto using member.
 apply Z.eqb_eq,(proj1 (forallb_forall _ _) E),member,H.
Qed.

Section Entries.
Context {s st pc n} (P:placement pc n s) (R:ready s st) (B:byte_memory (mem s)).
Local Ltac reg r := rewrite (arguments _ _ R r ltac:(cbv [kept In];tauto)).
Lemma digit_window r l p width : (r=1%nat \/ r=8%nat) -> (l<8)%nat ->
  0<=p -> 1<=width -> p+width<=2 ->
  within (digit_addr s r l p) width (regs s r) 512.
Proof. intros;pose proof (pair_range _ _ _ P);unfold within,digit_addr;lia. Qed.
Lemma digit_address k l : (l<8)%nat ->
 eval st (digit_term k l)=digit_addr s (match k with Base=>1|_=>8 end)%nat l (Audit.parity k).
Proof.
 intro L;destruct k; unfold digit_term,direct_term;cbn [eval];first [reg 8%nat|reg 1%nat];
 unfold advanced;cbn [Nat.eqb orb];unfold digit_addr,Audit.parity;
 rewrite Nat2Z.inj_add,Nat2Z.inj_mul.
 all: match goal with |- word ?a = _ => transitivity a end; [|ring].
 all: match goal with |- word (regs s ?r + _ + _) = _ =>
   apply (unwrapped s (regs s r) 512); [apply (digits_range _ _ _ P);auto|]
 end;pose proof (pair_range _ _ _ P);lia.
Qed.
Lemma ptr_address l : (l<8)%nat -> eval st (ptr_term l)=regs s 6%nat+8*Z.of_nat l.
Proof.
 intro L;unfold ptr_term,direct_term;cbn [eval];reg 6%nat;unfold advanced.
 rewrite Nat2Z.inj_mul;apply (unwrapped _ _ _ _ (pointers_range _ _ _ P)).
 change (regs s 6%nat<=regs s 6%nat+8*Z.of_nat l<regs s 6%nat+64);lia.
Qed.
Lemma pointer_value l : (l<8)%nat -> eval st (Read 8 (ptr_term l))=key_table s l.
Proof.
 intro L;cbn [eval];rewrite ptr_address by assumption;unfold key_table,read_word.
 apply (read_source _ _ _ _ _ _ R (pointers_range _ _ _ P));unfold within;lia.
Qed.
Lemma raw_legal r l p : (r=1%nat \/ r=8%nat) -> (l<8)%nat -> 0<=p<=1 ->
 legal (raw s r l p).
Proof. intros;split;[apply B|apply (signed_digits _ _ _ P);assumption]. Qed.
Lemma key_byte k l : k<>Base -> (l<8)%nat ->
 eval st (Read 1 (digit_term k l))=raw s 8%nat l (Audit.parity k).
Proof.
 intros K L;cbn [eval];rewrite digit_address by assumption.
 destruct k;try contradiction; rewrite (read_source _ _ _ _ _ _ R
  (digits_range _ _ _ P 8%nat (or_intror eq_refl))) by (apply digit_window;auto;cbn;lia);
 unfold raw;cbn [read_le];ring.
Qed.
Lemma base_pair l : (l<8)%nat -> eval st (Read 2 (digit_term Base l))=
 raw s 1%nat l 0+256*raw s 1%nat l 1.
Proof.
 intro L;cbn [eval];rewrite digit_address by assumption.
 rewrite (read_source _ _ _ _ _ _ R (digits_range _ _ _ P 1%nat (or_introl eq_refl)))
 by (apply digit_window;auto;cbn;lia).
 cbn [read_le Audit.parity];unfold raw,digit_addr;
 replace (regs s 1%nat+64*Z.of_nat l+2*regs s 9%nat+0+1) with
 (regs s 1%nat+64*Z.of_nat l+2*regs s 9%nat+1) by ring;ring.
Qed.
Local Lemma eval_key e : eval st (key_calc e)=key_offset st (eval st e).
Proof. reflexivity. Qed.
Local Lemma eval_base l : (l<8)%nat -> eval st (base_calc (Read 2 (digit_term Base l)))=
  affine_offset st (raw s 1%nat l 0) (raw s 1%nat l 1).
Proof.
 intro L;pose proof (base_pair l L) as E.
 change (eval st (base_calc (K (eval st (Read 2 (digit_term Base l))))) =
         affine_offset st (raw s 1%nat l 0) (raw s 1%nat l 1));
 rewrite E;reflexivity.
Qed.
Lemma table_value k l : (l<8)%nat ->
 eval st (table_term k l)=selected s k l-Z.of_nat (bias k).
Proof.
 intro L;destruct k.
 1,3: match goal with |- _=selected _ ?kk _ - _ => change
 (word (eval st (key_calc (Read 1 (digit_term kk l))) + eval st (Read 8 (ptr_term l))) =
 selected s kk l-Z.of_nat (bias kk)) end;rewrite eval_key;
 rewrite key_byte,pointer_value by (auto;discriminate);
 rewrite key_index by (apply raw_legal;auto;cbn;lia);
 unfold selected,digit,bias,raw;cbn [Audit.parity];
 rewrite (unwrapped _ _ _ _ (key_range _ _ _ P l L));
 [ring|pose proof (signed_digits _ _ _ P 8%nat l 1 (or_intror eq_refl) L ltac:(lia));
  pose proof (signed_digits _ _ _ P 8%nat l 0 (or_intror eq_refl) L ltac:(lia));
 unfold digit in *;lia].
 change (regs st 2%nat + eval st (base_calc (Read 2 (digit_term Base l)))=selected s Base l-Z.of_nat (bias Base)).
 reg 2%nat.
 rewrite eval_base by assumption.
 rewrite affine_index by (apply raw_legal;auto;lia).
 change (regs s 2%nat + 120*(136+signed_byte (raw s 1%nat l 0)+16*signed_byte (raw s 1%nat l 1)) = selected s Base l - 0);unfold selected,raw,digit;ring.
Qed.
Lemma entry_bounds k l : (l<8)%nat ->
 let '(a,len):=match k with Base=>(regs s 2%nat,273*120)|_=>(key_table s l,17*160) end in
 source s a len /\ within (selected s k l) (8*Z.of_nat (columns k)) a len.
Proof.
 intro L;destruct k;split;try apply (affine_range _ _ _ P);try now apply (key_range _ _ _ P).
 all: unfold selected,within;cbn [columns Audit.parity];
 pose proof (signed_digits _ _ _ P 8%nat l 0 (or_intror eq_refl) L ltac:(lia));
 pose proof (signed_digits _ _ _ P 8%nat l 1 (or_intror eq_refl) L ltac:(lia));
 pose proof (signed_digits _ _ _ P 1%nat l 0 (or_introl eq_refl) L ltac:(lia));
 pose proof (signed_digits _ _ _ P 1%nat l 1 (or_introl eq_refl) L ltac:(lia));lia.
Qed.
Lemma entry_source k l : (l<8)%nat -> source s (selected s k l) (8*Z.of_nat (columns k)).
Proof.
 intro L;pose proof (entry_bounds k l L) as H;destruct k;
 destruct H as [[[A T] D] I];unfold source,fits64,disjoint,within in *;intuition lia.
Qed.
Lemma tile_value k l t : (l<8)%nat -> (t<columns k)%nat ->
 eval st (tile_addr k l t)=selected s k l +8*Z.of_nat t.
Proof.
 intros L T;unfold tile_addr;cbn [eval];rewrite table_value by assumption.
 rewrite Nat2Z.inj_add,Nat2Z.inj_mul.
 replace (selected s k l-Z.of_nat (bias k)+(Z.of_nat (bias k)+Z.of_nat 8*Z.of_nat t))
 with (selected s k l+8*Z.of_nat t) by ring.
 apply (unwrapped _ _ _ _ (entry_source k l L));lia.
Qed.
Lemma selected_word k l c : (l<8)%nat -> (c<columns k)%nat ->
 eval st (word_term k l c)=read_word (mem s) (selected s k l+8*Z.of_nat c).
Proof.
 intros L C;assert(T:(tile_start k c<=c)%nat).
 { destruct k;unfold tile_start;repeat match goal with |- context[(?x <? ?y)%nat] => destruct (Nat.ltb_spec x y) end;lia. }
 unfold word_term;cbn [eval];rewrite tile_value by (auto;lia).
 rewrite Nat2Z.inj_mul,Nat2Z.inj_sub by assumption.
 replace (selected s k l+8*Z.of_nat (tile_start k c)+Z.of_nat 8*(Z.of_nat c-Z.of_nat (tile_start k c)))
 with (selected s k l+8*Z.of_nat c) by ring.
 apply (read_source _ _ _ _ _ _ R (entry_source k l L));unfold within;lia.
Qed.
End Entries.
