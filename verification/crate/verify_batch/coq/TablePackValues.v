From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.LinkedCalls execution.LinkedRun.
From Machine Require execution.PackedStores execution.PermutationBlock execution.MaskedResult.
From Ed25519Simd.KeyTable Require Pack Rows.
From Ed25519Simd.VerifyBatch Require TableMask TablePackRows.
Import ListNotations. Local Open Scope nat_scope.

Fixpoint known (w:Pack.word):bool:=match w with Pack.Unknown=>false | Pack.Subtract _ v=>known v | _=>true end.
Definition register_file:=nat->nat->Pack.word.
Definition represents f (r:register_file) s:=forall n j,j<8 -> known (r n j)=true -> vectors s j n=Rows.eval f (r n j).
Definition advance (r:register_file) op:=match op with
 | Pack.Unpack h d a b=>PermutationBlock.rearrange r (PermutationBlock.Unpack h d a b)
 | Pack.Shuffle d a b imm=>PermutationBlock.rearrange r (PermutationBlock.Shuffle d a b imm)
 | _=>fst(Pack.step (r,[]) op) end.
Definition mask_ok (ks:MaskTransfer.bank):=forall j,j<8 -> ks 1 j=Z.testbit Pack.mask (Z.of_nat j).

Lemma rearranged f r s op : represents f r s ->
 represents f (PermutationBlock.rearrange r op) (IndexedLoads.execute [PermutationBlock.instruction op] s).
Proof.
 intros R n j J;destruct (PermutationBlock.one 0 0 op s None) as [_ [_ [_ [_ V]]]].
 unfold PermutationBlock.live in V;rewrite V;unfold PermutationBlock.rearrange.
 destruct(Nat.eqb n (PermutationBlock.destination op));[|apply R,J].
 destruct op as [h d a b|d a b imm];cbn [PermutationBlock.source Packed.unpack_source Packed.shuffle_source].
 - apply R;pose proof(Nat.div_mod j 2 ltac:(lia));destruct h;lia.
 - apply R;pose proof(Nat.mod_upper_bound (imm/4^(j/2)) 4 ltac:(lia));pose proof(Nat.mod_upper_bound j 2 ltac:(lia));lia.
Qed.

Lemma one f r s ks op o off : mask_ok ks -> represents f r s ->
 represents f (advance r op) (PackedStores.apply_op o off s ks (TablePackRows.lower op)).
Proof.
 intros Mask R;destruct op as [h d a b|d a b imm|d a|d idx b|d a b|pos off' src|pos off' src half].
 1,2: apply rearranged,R.
 - intros n j J;cbn [advance Pack.step fst TablePackRows.lower PackedStores.apply_op PackedStores.effect with_words ScalarBytes.vector_dest vectors];unfold put;
   destruct(Nat.eqb d n);apply R,J.
 - intros n j J;cbn [advance Pack.step fst TablePackRows.lower PackedStores.apply_op PackedStores.effect with_words ScalarBytes.vector_dest vectors];unfold put;
   destruct(Nat.eqb d n);[|apply R,J].
   destruct(r idx j) as [|z| |] eqn:Idx;try discriminate.
     pose proof(R idx j J ltac:(rewrite Idx;reflexivity)) as Index;rewrite Idx in Index;cbn [Rows.eval] in Index;rewrite Index.
     set (k:=(z mod 16)%Z);pose proof(Z.mod_pos_bound z 16 ltac:(lia)) as K;fold k in K.
     replace (Z.to_nat k <? 8) with (k<?8)%Z by (symmetry;destruct(Z.ltb_spec k 8);[apply Nat.ltb_lt|apply Nat.ltb_ge];lia).
     replace (Z.to_nat k mod 8) with (Z.to_nat(k mod 8)) by (rewrite Z2Nat.inj_mod by lia;reflexivity).
     apply R;pose proof(Z.mod_pos_bound k 8 ltac:(lia));lia.
 - intros n j J;cbn [advance Pack.step fst TablePackRows.lower PackedStores.apply_op PackedStores.effect with_words
   MaskedResult.merge ScalarBytes.vector_dest vectors];unfold put;destruct(Nat.eqb d n) eqn:D;[|apply R,J].
   apply Nat.eqb_eq in D;subst n;rewrite Mask by exact J;cbn [Nat.eqb orb].
   destruct(Z.testbit Pack.mask (Z.of_nat j));[|apply R,J].
   destruct(r a j) as [|z| |] eqn:A;try discriminate;intro Know.
   pose proof(R a j J ltac:(rewrite A;reflexivity)) as Bias;rewrite A in Bias;cbn [Rows.eval] in Bias.
   cbn [known] in Know;cbn [Rows.eval];now rewrite Bias,(R b j J Know).
 - exact R.
 - exact R.
Qed.

(* The two transposed vectors per key precede four columns still in the
   original lane order. Registers that have no promised contents stay unknown. *)
Definition initial n j:=match n with
 | 16|17|18|19|20|21|22|23=>Pack.Input j (n-16)
 | 24|25=>Pack.Input (8+j) (n-24)
 | 5|6|7|8|9=>Pack.Input (8+j) (n-3)
 | 0=>Pack.Input (8+j) 7
 | 1|2|3|4=>Pack.Input (16+(n-1)) j
 | 28|29|30=>Pack.Literal (nth j (TablePackLiterals.words (n-28)) 0%Z)
 | _=>Pack.Unknown end.
Lemma from_registers f s :
 (forall b j i,(j<8)%nat -> (i<8)%nat -> vectors s i (TableTranspose.reg b j)=f j (TablePackedInputs.index b i)) ->
 (forall j i,(j<8)%nat -> (i<4)%nat -> vectors s j (1+i)%nat=f j (16+i)%nat) ->
 (forall i j,(i<3)%nat -> (j<8)%nat -> vectors s j (28+i)%nat=nth j (TablePackLiterals.words i) 0%Z) ->
 represents f initial s.
Proof.
 intros Pair Tail Literals n j J;do 31 (destruct n as [|n];[shelve|]);try discriminate. Unshelve. all:cbn [initial known Rows.eval];try discriminate;intro Know.
 all: match goal with |-vectors _ _ ?reg=_=>
  let which:=(eval compute in (if reg=?0 then 0 else if reg<?5 then 1 else if reg<?10 then 2 else if reg<?24 then 3 else if reg<?26 then 4 else 5)) in
  lazymatch which with
  | 0=>exact (Pair true 7 j ltac:(lia) J)
  | 1=>let i:=(eval compute in (reg-1)) in exact (Tail j i J ltac:(lia))
  | 2=>let i:=(eval compute in (reg-3)) in exact (Pair true i j ltac:(lia) J)
  | 3=>let i:=(eval compute in (reg-16)) in exact (Pair false i j ltac:(lia) J)
  | 4=>let i:=(eval compute in (reg-24)) in exact (Pair true i j ltac:(lia) J)
  | 5=>let i:=(eval compute in (reg-28)) in exact (Literals i j ltac:(lia) J)
  end end.
Qed.
Lemma incoming pol bias e p a ks : TableMask.ready pol bias e p a ks ->
 represents (TablePackedInputs.column e (machine p)) initial (machine a).
Proof. intro A;apply from_registers;[apply (TableMask.packed _ _ _ _ _ _ A)|apply (TableMask.tail _ _ _ _ _ _ A)|apply (TableMask.literals _ _ _ _ _ _ A)]. Qed.
