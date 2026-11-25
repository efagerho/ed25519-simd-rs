From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords
 execution.WordSemantics execution.WordBounds execution.MaskTransfer execution.PredicateFlags
 execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterLoad.
Import ListNotations. Local Open Scope Z_scope.

Definition branch:list line:=[(303,6%nat,ScalarBytes.Branch Equal (543-309))].
Definition save:=ToGpr 1 1.
Lemma image : firstn 4 (skipn 299 FilterLoad.text)=MaskTrace.encoding(MaskTrace.TestMask 1) /\ linked FilterLoad.text branch /\
 firstn 4 (skipn 309 FilterLoad.text)=MaskTransfer.encoding save.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Inductive outcome:=Done (q:cursor) | CompareZ (q:cursor).
Definition stopped v:=match v with Done q | CompareZ q=>q end.
Definition execute bias p ks:=let o:=bias+FilterLoad.site in
 bind (PredicateFlags.test 1 p ks) (fun a=>bind (segment o FilterLoad.text 1 a) (fun b=>
 if ip b=?o+543 then Some(Done b) else option_map (fun '(q,_)=>CompareZ q) (MaskTransfer.tick save b ks))).

Theorem checked bias e p ks : loaded Dalek bias (mem e) (writable e) -> ip p=bias+FilterLoad.site+299 ->
 accounted e (writable e) p -> well_formed(machine p) -> exists v,execute bias p ks=Some v /\
 let q:=stopped v in accounted e (writable e) q /\ well_formed(machine q) /\
 mem(machine q)=mem(machine p) /\ log q=log p /\ vectors(machine q)=vectors(machine p) /\
 match v with Done _=>mask16(ks 1%nat)=0 /\ ip q=bias+FilterLoad.site+543 /\ regs(machine q)=regs(machine p)
 | CompareZ _=>mask16(ks 1%nat)<>0 /\ ip q=bias+FilterLoad.site+313 /\ regs(machine q)=put (regs(machine p)) 1 (mask16(ks 1%nat)) end.
Proof.
 intros I PC Acc W;set (o:=bias+FilterLoad.site) in *;set (m:=mask16(ks 1%nat));set (a:=tested p m).
 destruct(mapped_now _ _ _ I _ _ _ Acc StrictFilterCall.in_filter) as [Map Sep];fold o in Map,Sep.
 destruct(proj1(symbols _ _ _ _ I _ _ StrictFilterCall.in_filter)) as [L H];change (0<=o) in L;change (o+551<=2^64) in H.
 assert (Test:PredicateFlags.test 1 p ks=Some a).
 { apply mapped_test;[lia|rewrite PC;change (mapped (mem(machine p)) (o+Z.of_nat 299) (MaskTrace.encoding(MaskTrace.TestMask 1)));
    apply subimage with (text:=FilterLoad.text);[exact Map|change (299+4<=551)%nat;lia|exact (proj1 image)]]. }
 assert (AP:ip a=o+303) by (unfold a,tested;cbn [ip];rewrite PC,word_fits by (unfold word64;lia);ring).
 set (off:=if m=?0 then 543 else 309).
 assert (R:run 1 (ScalarBytes.fetch o FilterLoad.text) (State(Running 303) (machine a) (LinkedRun.carry a))=
   Some(State(Running off) (machine a) (LinkedRun.carry a),[])).
 { apply (InstructionRoute.checked _ _ _ (proj1(proj2 image)));unfold off,a,tested;cbn [branch follow loc cpu_state cf
    ScalarBytes.step eval_condition machine carry with_zf flag option_map];destruct (m=?0);reflexivity. }
 destruct(at_segment _ _ a o FilterLoad.text 1 303 _ _ Acc AP Map Sep R (Forall_nil _)) as [Step Paid].
 set (b:=LinkedRun.finish o a (State(Running off) (machine a) (LinkedRun.carry a),[])) in *.
 assert (WB:well_formed(machine b)) by exact W.
 assert (BPC:ip b=o+off) by reflexivity.
 assert (Log:log b=log p) by (change (log p++[]=log p);apply app_nil_r).
 unfold execute;fold o;rewrite Test;cbn [bind];rewrite Step;cbn [bind];fold b;rewrite BPC;unfold off.
 destruct(Z.eqb_spec m 0) as [Nil|Live].
 - rewrite Z.eqb_refl;exists (Done b);split;[reflexivity|];split;[exact Paid|split;[exact WB|split;[reflexivity|split;[exact Log|split;[reflexivity|]]]]].
   split;[exact Nil|split;[change (ip b=o+543);rewrite BPC;unfold off;try rewrite Nil;reflexivity|reflexivity]].
 - rewrite (proj2(Z.eqb_neq (o+309) (o+543)) ltac:(lia));assert (Off:off=309) by reflexivity.
   assert (Bytes:mapped (mem(machine b)) (ip b) (MaskTransfer.encoding save)).
   { rewrite BPC,Off;change (mapped (mem(machine p)) (o+Z.of_nat 309) (MaskTransfer.encoding save));
     apply subimage with (text:=FilterLoad.text);[exact Map|change (309+4<=551)%nat;lia|exact (proj2(proj2 image))]. }
   rewrite (MaskTransfer.fetched save b ks eq_refl Bytes);cbn [option_map MaskTransfer.effect save].
   eexists;split;[reflexivity|split;[exact Paid|split;[|split;[reflexivity|split;[exact Log|split;[reflexivity|]]]]]].
   + apply set_wf;[exact WB|pose proof(proj1(kmov_value (ks 1%nat)));unfold word64;lia].
   + split;[exact Live|split;[|reflexivity]];change (word(ip b+4)=o+313);rewrite BPC,Off,word_fits by (unfold word64;lia);ring.
Qed.
