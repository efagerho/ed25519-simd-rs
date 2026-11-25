From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.StoreHistory
 memory.FlatMemory memory.ByteMemory abi.SysV.
From Curve25519.group Require Import Affine Representation.
From Ed25519Simd Require Import Wide51 PointResults.
From Ed25519Simd.FullLadder Require Import LinkedBytes Operands ScalarAction Execution Native Audit.
From Ed25519Simd.FullLadder Require TopCall TopPoint RoundOperands.
Import ListNotations. Local Open Scope Z_scope.
Definition point s:=regs s 7%nat.
Definition allowed s:=TopPoint.region (point s) (base_of s).
Definition images_at slide m:=mapped m (slide+entry_pc) symbol_bytes /\
 forall k,mapped m (slide+TopCall.target k) (TopPoint.bytes k).
Record ready slide s q:Prop:=Ready {
 words:well_formed(machine q); stack:regs(machine q) 4%nat=base_of s; ptr:regs(machine q) 3%nat=point s;
 code:images_at slide (mem(machine q)); staged:RoundOperands.selected s (base_of s) 31 (mem(machine q))
}.
Lemma outside_image slide s a n : placement slide s -> In (a,n) images ->
 forall x,slide+a<=x<slide+a+n -> ~allowed s x.
Proof.
 intros P I;destruct(loaded_images _ _ P _ _ I) as [_ [C S]].
 unfold allowed,TopPoint.region,point,base_of,Program.staging,pad_of,disjoint in *;
 pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));intros;lia.
Qed.
Lemma next_ready slide s k p q : placement slide s -> ready slide s p ->
 TopPoint.result slide k (point s) (base_of s) p q -> ready slide s q.
Proof.
 intros P R T;destruct(code _ _ _ R) as [Map Leaf];pose proof(TopPoint.writes _ _ _ _ _ _ T) as H.
 constructor;[exact (TopPoint.words _ _ _ _ _ _ T)|exact (TopPoint.stack _ _ _ _ _ _ T)| | |].
 - rewrite (TopPoint.saved _ _ _ _ _ _ T) by (cbv [In sysv_saved];tauto);apply (ptr _ _ _ R).
 - split.
   + eapply StoreHistory.image;[exact H|exact Map|apply outside_image;[exact P|left;reflexivity]].
   + intro l;eapply StoreHistory.image;[exact H|apply Leaf|apply outside_image;[exact P|]].
     destruct l;[do 3 right;left|do 4 right;left|do 4 right;left];reflexivity.
 - apply (RoundOperands.stable _ _ _ _ _ (staged _ _ _ R));intros x X;apply (StoreHistory.preserves _ _ _ H).
   pose proof(LA.cache_point _ _ _ _ _ (ladder_placement _ _ _ (child_layout _ _ P))) as Apart.
   unfold disjoint,allowed,TopPoint.region,point in *;lia.
Qed.
Definition phase slide s k p:=TopPoint.execute slide (base_of s) k p.
Lemma step slide s k p : placement slide s -> ready slide s p -> ip p=slide+entry_pc+TopCall.start k ->
 exists q,phase slide s k p=Some q /\ TopPoint.result slide k (point s) (base_of s) p q /\ ready slide s q.
Proof.
 intros P R PC;destruct(code _ _ _ R) as [Code Leaf].
 destruct(TopPoint.checked slide k s p P PC (words _ _ _ R) (stack _ _ _ R) (ptr _ _ _ R) Code (Leaf k)) as [q [Run T]].
 exists q;split;[exact Run|split;[exact T|eapply next_ready;eassumption]].
Qed.
Definition execute slide base p:=bind (TopPoint.execute slide base TopCall.Four p) (fun a=>
 bind (TopPoint.execute slide base TopCall.Affine a) (TopPoint.execute slide base TopCall.Even)).
Definition accumulator s q:=buffer_words (mem(machine q)) (point s).
Record result slide s B A p q : Prop:=Result {
 next:ip q=slide+entry_pc+822;
 resumed:ready slide s q;
 history:StoreHistory.extends (allowed s) p q;
 kept:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 reduced:strict (accumulator s q);
 value:seeded_xyz (accumulator s q) (accumulated s B A 1);
 omitted:zero_t (accumulator s q)
}.
Theorem checked slide s B A p : placement slide s -> valid_inputs (slide+stage_pc) (pad_of s) s ->
 valid_tables s B A -> ready slide s p -> ip p=slide+entry_pc+768 -> loose_xyz (accumulator s p) ->
 seeded_xyz (accumulator s p) (fun j=>operand_point s B A j 31 S.Odd) ->
 exists q,execute slide (base_of s) p=Some q /\ result slide s B A p q.
Proof.
 intros P V T Ready PC Bound Odd.
 destruct(step slide s TopCall.Four p P Ready PC) as [d [D [DR Dready]]].
 destruct(step slide s TopCall.Affine d P Dready (TopPoint.at_next _ _ _ _ _ _ DR)) as [a [C [AR Aready]]].
 destruct(step slide s TopCall.Even a P Aready (TopPoint.at_next _ _ _ _ _ _ AR)) as [q [E [ER Qready]]].
 pose proof(TopPoint.point _ _ _ _ _ _ DR) as Doubled.
 destruct(first_double _ _ _ Doubled Bound Odd) as [DB DQ].
 pose proof(RoundOperands.checked _ _ _ _ 31%nat _ S.Base B A V T ltac:(lia) (staged _ _ _ Dready)) as [BB BR].
 pose proof(RoundOperands.checked _ _ _ _ 31%nat _ S.Even B A V T ltac:(lia) (staged _ _ _ Aready)) as [EB EV].
 destruct(point_add _ _ _ _ _ _ _ (TopPoint.point _ _ _ _ _ _ AR) (handoff_bounds _ _ DB) BB DQ BR) as [AB AQ].
 pose proof(TopPoint.point _ _ _ _ _ _ ER) as Even.
 destruct(point_add _ _ _ _ _ _ _ Even (handoff_bounds _ _ AB) EB AQ EV) as [QB QQ].
 exists q;split.
 - unfold phase in D,C,E;unfold execute;now rewrite D;cbn [bind];rewrite C;cbn [bind].
 - constructor;[exact (TopPoint.at_next _ _ _ _ _ _ ER)|exact Qready| | |exact QB| |exact ((proj1 Even) eq_refl)].
   + eapply StoreHistory.compose;[exact (TopPoint.writes _ _ _ _ _ _ DR)|].
     eapply StoreHistory.compose;[exact (TopPoint.writes _ _ _ _ _ _ AR)|exact (TopPoint.writes _ _ _ _ _ _ ER)].
   + intros r R;rewrite (TopPoint.saved _ _ _ _ _ _ ER),(TopPoint.saved _ _ _ _ _ _ AR),(TopPoint.saved _ _ _ _ _ _ DR) by exact R;reflexivity.
   + intros j J;specialize(QQ j J);apply proj1 in QQ;unfold operand_point,affine,weight in QQ;cbn iota in QQ;rewrite top_pair in QQ.
     unfold accumulated;cbn [remaining_digits];rewrite !Z.mul_0_r,!Z.add_0_r;exact QQ.
Qed.
