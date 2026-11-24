From Coq Require Import ZArith List Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.LinkedCalls execution.LinkedRun execution.MappedFetch memory.ByteMemory.
From Machine Require execution.MaskTransfer execution.MaskedWords.
Import ListNotations. Local Open Scope Z_scope.

(* These instructions only update opmasks. The register/memory source,
   write mask, predicate bit and RIP displacement use MaskedWords' ISA.
   Bits above the architectural destination width are cleared. *)
Definition destination op:=match op with
 | MaskedWords.Compare _ d _ _ _ | MaskedWords.Union d _ _=>Some d | _=>None end.
Definition update origin s (bank:MaskTransfer.bank) d op:=put bank d (fun j=>
 (j<?16)%nat && MaskedWords.mask
   (MaskedWords.step (j<?8)%nat (fun t=>read_word (mem s) (word(origin+t)))
     (MaskedWords.Lane (vectors s j) (fun r=>bank r j) (regs s 0%nat)) op) d).
Fixpoint evaluate origin s (bank:MaskTransfer.bank) ops:=match ops with
 | []=>Some bank | op::rest=>match destination op with None=>None | Some d=>evaluate origin s (update origin s bank d op) rest end end.

Definition execute origin ops p (bank:MaskTransfer.bank):=
 match MaskedWords.assemble (ip p-origin) ops with None=>None | Some code=>
 if list_eq_dec Z.eq_dec (snapshot (mem(machine p)) (ip p) (length code)) code then
 option_map (fun ks=>(Cursor (word(ip p+Z.of_nat(length code))) (machine p) (carry p) (log p),ks))
  (evaluate origin (machine p) bank ops) else None end.

Lemma mapped_block origin off ops p bank code ks : ip p=origin+off ->
 MaskedWords.assemble off ops=Some code -> mapped (mem(machine p)) (ip p) code ->
 evaluate origin (machine p) bank ops=Some ks ->
 execute origin ops p bank=Some(Cursor (word(ip p+Z.of_nat(length code))) (machine p) (carry p) (log p),ks).
Proof.
 intros At Enc Map Result;unfold execute;replace (ip p-origin) with off by lia.
 rewrite Enc,(snapshot_mapped _ _ _ Map);destruct(list_eq_dec _ _ _);[now rewrite Result|contradiction].
Qed.

Definition operand origin s j v:=match v with MaskedWords.Reg r=>vectors s j r
 | MaskedWords.Rip target=>read_word (mem s) (word(origin+target)) end.
Lemma compare origin s ks less d gate src rhs j :
 update origin s ks d (MaskedWords.Compare less d gate src rhs) d j=
 ((j<?8)%nat && ((gate=?0)%nat || ks gate j) &&
   (if less then vectors s j src <? operand origin s j rhs else vectors s j src =? operand origin s j rhs))%bool.
Proof.
 unfold update,put;rewrite Nat.eqb_refl;cbn [MaskedWords.step MaskedWords.zmm MaskedWords.mask MaskedWords.rax].
 unfold Packed.update;rewrite Nat.eqb_refl;destruct(Nat.ltb_spec j 16);[destruct rhs;reflexivity|].
 rewrite (proj2 (Nat.ltb_ge j 8) ltac:(lia));reflexivity.
Qed.
Lemma union origin s ks d a b j :
 update origin s ks d (MaskedWords.Union d a b) d j=((j<?16)%nat && (ks a j || ks b j))%bool.
Proof. unfold update,put;rewrite Nat.eqb_refl;cbn [MaskedWords.step MaskedWords.mask];unfold Packed.update;now rewrite Nat.eqb_refl. Qed.
Lemma other origin s ks d op r : r<>d -> update origin s ks d op r=ks r.
Proof. intro N;unfold update,put;now rewrite (proj2(Nat.eqb_neq d r) ltac:(lia)). Qed.

Lemma unchanged origin ops p bank q out :
 execute origin ops p bank=Some(q,out) -> machine q=machine p.
Proof.
 unfold execute;destruct(MaskedWords.assemble _ _) as [code|];[|discriminate].
 destruct(list_eq_dec _ _ _);[|discriminate].
 destruct(evaluate _ _ _ _);[|discriminate];intro E;injection E as <- <-;reflexivity.
Qed.
