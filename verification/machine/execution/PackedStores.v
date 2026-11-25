From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions isa.QwordRegister execution.WordSemantics execution.WordBounds
 execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords
 execution.MappedFetch execution.InstructionRoute memory.WriteTrace.
From Machine Require execution.PermutationBlock execution.VectorOutputs execution.MaskTransfer execution.MaskedResult.
Import ListNotations. Local Open Scope Z_scope.

(* One fetched path may mix scalar-decoder vector instructions with merge-masked
   instructions. Keep the mask bank live and attach each store to the instruction
   that supplied both its effective address and its payload. *)
Inductive op :=
 | Rearrange (v:PermutationBlock.permutation)
 | Move (dst src:nat)
 | Select (dst indices rhs:nat)
 | MaskSub (dst mask lhs rhs:nat)
 | Write (w:VectorOutputs.output).

Definition width v:=match v with
 | Rearrange p=>PermutationBlock.width p
 | Move d a=>length (Instructions.encode(d,Instructions.Copy a))
 | Select d i b=>length(QwordRegister.encoding(Permute2 d i b))
 | MaskSub d k a b=>length(MaskedResult.encode 0 (MaskedResult.Subtract d k a b))
 | Write w=>VectorOutputs.width w end.
Definition linked_at text off v:=
 let decoded i:=ScalarBytes.decode (skipn off text)=Some(width v,i) in match v with
 | Rearrange p=>decoded (VectorMove(VectorMoves.Input(PermutationBlock.instruction p)))
 | Move d a=>decoded (QwordOp(Alu(d,Instructions.Copy a)))
 | Select d i b=>decoded (QwordOp(Permute2 d i b))
 | Write w=>decoded (VectorMove(VectorOutputs.native w))
 | MaskSub d k a b=>let cmd:=MaskedResult.Subtract d k a b in
    let bs:=MaskedResult.encode (Z.of_nat off) cmd in
    MaskedResult.assemble (Z.of_nat off) [cmd]=Some bs /\
    firstn (width v) (skipn off text)=bs
 end.
Fixpoint image text off ops:=match ops with []=>True | v::tail=>
 linked_at text off v /\ image text (off+width v)%nat tail end.
Fixpoint stop off ops:=match ops with []=>off | v::tail=>stop (off+width v)%nat tail end.

Definition exec_one o text v p ks:=match v with
 | MaskSub d k a b=>MaskedResult.execute o [MaskedResult.Subtract d k a b] p ks
 | _=>option_map (fun q=>(q,ks)) (segment o text 1 p) end.
Fixpoint execute o text ops p ks:=match ops with []=>Some(p,ks) | v::tail=>
 bind (exec_one o text v p ks) (fun '(q,bank)=>execute o text tail q bank) end.

Definition stores o off s v:=match v with
 | Write w=>[VectorOutputs.event o (Z.of_nat off) s w] | _=>[] end.
Definition effect s ks v:=match v with
 | Rearrange p=>IndexedLoads.execute [PermutationBlock.instruction p] s
 | Move d a=>vector_dest s d (fun j=>vectors s j a)
 | Select d i b=>vector_dest s d (fun j=>let k:=vectors s j i mod 16 in vectors s (Z.to_nat(k mod 8)) (if k<?8 then d else b))
 | MaskSub d k a b=>MaskedResult.merge s ks d k (fun j=>Arithmetic.vpsubq (vectors s j a) (vectors s j b))
 | Write _=>s end.
Definition apply_op o off s ks v := let t:=effect s ks v in with_words t (regs t) (replay (mem s) (stores o off s v)).
Lemma gprs s ks v : regs(effect s ks v)=regs s.
Proof. destruct v as [[]| | | |];reflexivity. Qed.
Lemma effect_memory s ks v : mem(effect s ks v)=mem s.
Proof. destruct v as [[]| | | |];reflexivity. Qed.

Definition span o len := 0<=o /\ o+Z.of_nat len<=2^64.
Lemma next_bound off ops : (off<=stop off ops)%nat.
Proof. revert off;induction ops;intro off;cbn [stop];[lia|specialize (IHops (off+width a)%nat);lia]. Qed.

Lemma single o text off v p ks e allowed : linked_at text off v ->
 (off+width v<length text)%nat -> span o (length text) -> ip p=o+Z.of_nat off ->
 accounted e allowed p -> mapped (mem(machine p)) o text ->
 (forall x,o<=x<o+Z.of_nat(length text)->~allowed x) ->
 well_formed(machine p) -> confined allowed (stores o off (machine p) v) ->
 exists q,exec_one o text v p ks=Some(q,ks) /\ ip q=o+Z.of_nat(off+width v) /\
 accounted e allowed q /\ well_formed(machine q) /\ machine q=apply_op o off (machine p) ks v /\
 log q=log p++stores o off (machine p) v.
Proof.
 intros Link Bound [L H] PC Acc Map Sep W Safe.
 destruct v as [perm|d a|d i b|d k a b|w] eqn:V.
 4:{ set (cmd:=MaskedResult.Subtract d k a b);destruct Link as [Asm Bytes].
     set (bs:=MaskedResult.encode (Z.of_nat off) cmd) in *.
     assert (Mapped:mapped (mem(machine p)) (ip p) bs) by
       (rewrite PC;apply MaskTransfer.subimage with (text:=text);[exact Map|exact (Nat.lt_le_incl _ _ Bound)|exact Bytes]).
     set (t:=effect (machine p) ks (MaskSub d k a b)).
     assert (Eval:MaskedResult.evaluate o (machine p) ks [cmd]=Some(t,ks)) by reflexivity.
     pose proof(MaskedResult.mapped_block o (Z.of_nat off) [cmd] p ks bs t ks PC Asm Mapped Eval) as Run.
     eexists;split;[exact Run|];cbn [ip machine log];split.
     - change (length bs) with (width (MaskSub d k a b));rewrite PC,Nat2Z.inj_add;rewrite word_fits;[ring|unfold word64;lia].
     - split;[exact Acc|split;[apply (proj2(proj2(proj2(MaskedResult.stable _ _ _ _ _ _ Eval)))),W|]].
       split;[reflexivity|symmetry;apply app_nil_r]. }
 all: assert (One:run 1 (ScalarBytes.fetch o text) (State(Running(Z.of_nat off)) (machine p) (LinkedRun.carry p))=
        Some(State(Running(Z.of_nat off+Z.of_nat(width v))) (apply_op o off (machine p) ks v) (LinkedRun.carry p),stores o off (machine p) v))
   by (subst v; cbn [run ScalarBytes.fetch loc cpu_state cf];
       rewrite (proj2(Z.ltb_ge _ _) (Nat2Z.is_nonneg off)),Nat2Z.id;unfold linked_at in Link;rewrite Link;
       first [reflexivity|destruct perm;reflexivity|destruct w as [src reg disp [|[]]];reflexivity]).
 all: destruct(at_segment _ _ p o text 1 _ _ _ Acc PC Map Sep One ltac:(subst v;exact Safe)) as [Step Paid];
      subst v;eexists;split;[unfold exec_one;rewrite Step;reflexivity|];
      split;[cbn [ip finish absolute loc];rewrite Nat2Z.inj_add;ring|split;[exact Paid|split;[exact (segment_wf _ _ _ _ _ W Step)|split;reflexivity]]].
Qed.

Fixpoint simulate o off ops s ks : cpu*list store := match ops with
 | []=>(s,[]) | v::tail=>
    let '(t,ws):=simulate o (off+width v)%nat tail (apply_op o off s ks v) ks in
    (t,stores o off s v++ws) end.

(* The address check uses only the incoming GPRs. No instruction in this
   family changes one, even when its vector destination is also a source. *)
Definition safe allowed s v:=match v with
 | Write w=>forall x,VectorOutputs.address s w<=x<VectorOutputs.address s w+Z.of_nat(VectorOutputs.size w) -> allowed x
 | _=>True end.
Lemma same_safe allowed s t v : regs t=regs s -> safe allowed s v -> safe allowed t v.
Proof. destruct v;try tauto;intros G;unfold safe,VectorOutputs.address;now rewrite G. Qed.
Lemma store_safe o off s v allowed : safe allowed s v -> confined allowed (stores o off s v).
Proof. destruct v;intro S;cbn [stores];constructor;[exact S|constructor]. Qed.

Theorem checked o text ops : forall off p ks e allowed,
 image text off ops -> (stop off ops<length text)%nat -> span o (length text) -> ip p=o+Z.of_nat off ->
 accounted e allowed p -> mapped (mem e) o text -> (forall x,o<=x<o+Z.of_nat(length text)->~allowed x) ->
 well_formed(machine p) -> Forall (safe allowed (machine p)) ops ->
 exists q,execute o text ops p ks=Some(q,ks) /\ ip q=o+Z.of_nat(stop off ops) /\
 accounted e allowed q /\ well_formed(machine q) /\ regs(machine q)=regs(machine p) /\
 let '(s,ws):=simulate o off ops (machine p) ks in machine q=s /\ log q=log p++ws.
Proof.
 induction ops as [|v tail IH];intros off p ks e allowed Code End Span PC Acc Map Sep W Safe.
 - exists p;split;[reflexivity|split;[exact PC|split;[exact Acc|split;[exact W|]]]];cbn [simulate];rewrite app_nil_r;auto.
 - destruct Code as [First Rest];apply Forall_cons_iff in Safe as [S SS].
   pose proof(next_bound (off+width v)%nat tail) as Lower;cbn [stop] in End.
   destruct(single o text off v p ks e allowed First ltac:(lia) Span PC Acc (image_after _ _ _ _ _ Acc Map Sep) Sep W
     (store_safe _ _ _ _ _ S)) as [q [Run [Next [Paid [Q [Effect Log]]]]]].
   assert (G:regs(machine q)=regs(machine p)) by (rewrite Effect;apply gprs).
   destruct(IH _ q ks _ _ Rest End Span Next Paid Map Sep Q
     ltac:(eapply Forall_impl;[intros a;apply same_safe,G|exact SS])) as [t [R [At [Fin [TW [TG M]]]]]].
   exists t;split;[cbn [execute];rewrite Run;exact R|split;[exact At|split;[exact Fin|split;[exact TW|split;[now rewrite TG,G|]]]]].
   cbn [simulate];rewrite <-Effect;destruct(simulate o _ tail (machine q) ks) as [last ws];destruct M as [T F].
   split;[exact T|now rewrite F,Log,app_assoc].
Qed.
