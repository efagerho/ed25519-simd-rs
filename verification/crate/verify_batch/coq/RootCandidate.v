From Coq Require Import ZArith List Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.LinkedCalls execution.LinkedRun execution.MappedFetch
 execution.ScalarBytes execution.ScalarWords execution.InstructionRoute execution.VectorProcedure execution.AlignedRows memory.ByteMemory
 memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.Decode Require Power Kernels.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderFinish DecoderProduct RowProduct FieldStores.
Import ListNotations. Local Open Scope Z_scope.

Definition mov:list line:=[(1076,3%nat,CopyG 8 6)].
Lemma code : linked text mov /\
 ScalarBytes.decode(skipn 1079 text)=Some(5%nat,CallRelative(0xa57-1084)) /\
 linked text (AlignedRows.route true 1084 0 7 960 5).
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias:=then_run (segment (base bias) text 1)
 (then_run (DecoderProduct.multiply_call bias) (segment (base bias) text 5)).
Definition candidate s j:=Power.apply_kernel DecoderProduct.kernel Kernels.Multiply
 (vectors s j) (row s (regs s 6%nat) j).

Record result sig pol bias e p q : Prop:=Result {
 next_call:ip q=base bias+1119;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 regs_after:forall r,regs(machine q) r=if (r=?8)%nat then regs(machine p) 6%nat else regs(machine p) r;
 high:RowProduct.constants(machine q);
 frame:preserved (fun x=> ~(link_slot pol e-24<=x<link_slot pol e) /\
   ~(point e sig+960<=x<point e sig+1280)) (mem(machine p)) (mem(machine q));
 live_x:forall j i,(j<8)%nat -> (i<5)%nat ->
  vectors(machine q) j i=candidate (machine p) j i /\
  row (machine q) (point e sig+960) j i=candidate (machine p) j i
}.

Theorem checked sig pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=base bias+1076 -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 4%nat=link_slot pol e -> regs(machine p) 7%nat=point e sig ->
 regs(machine p) 6%nat=link_slot pol e+8+DecoderFinish.power_offset sig -> RowProduct.constants(machine p) ->
 exists q,execute bias p=Some q /\ result sig pol bias e p q.
Proof.
 intros P I PC Acc W SP DI SI C;set (s:=machine p) in *;set (o:=base bias) in *;set (a:=regs s 6%nat).
 set (v:=set s 8 a).
 assert (Move:run 1 (ScalarBytes.fetch o text) (State (Running 1076) s (LinkedRun.carry p))=
  Some(State (Running 1079) v (LinkedRun.carry p),[])).
 { apply (checked _ _ _ (proj1 code));reflexivity. }
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text 1 1076 _ _ Acc PC Map Sep Move (Forall_nil _)) as [Next Paid].
 set (mid:=LinkedRun.finish o p (State (Running 1079) v (LinkedRun.carry p),[])) in *.
 assert (WM:well_formed(machine mid)) by exact (segment_wf _ _ _ _ _ W Next).
 pose proof(depth pol e) as Depth;destruct(Return.stack_ok _ P) as [[Lo Hi] _].
 assert (Al:a mod 64=0).
 { unfold a;rewrite SI;unfold link_slot,DecoderFrame.top;set (x:=common_top pol e-112-40);
   pose proof(Z.div_mod x 64 ltac:(lia));apply Z.mod_divide;[lia|].
   destruct sig;cbn [DecoderFinish.power_offset];[exists(x/64-5)|exists(x/64-10)];lia. }
 assert (Fit:fits64 a 320) by (unfold a,fits64;rewrite SI;destruct sig;cbn [DecoderFinish.power_offset];lia).
 assert (Away:forall x,a<=x<a+320 -> ~(link_slot pol e-8<=x<link_slot pol e)).
 { unfold a;rewrite SI;destruct sig;cbn [DecoderFinish.power_offset];lia. }
 destruct(RowProduct.called pol bias e 1079 mid P I ltac:(lia) ltac:(lia) (proj1(proj2 code))
   eq_refl Paid WM SP C Al Fit Away) as [mul [Call M]].
 destruct M as [At Safe Words G Keep Consts Product].
 assert (Dst:regs(machine mul) 7%nat=point e sig) by (rewrite G;exact DI).
 destruct(FieldStores.execute sig pol bias e 1084 960 mul P I (proj2(proj2 code)) ltac:(lia) eq_refl
   At Safe Words Dst) as [q [Store [End Done WF Reg Vec Rows Unchanged]]].
 exists q;split;[unfold execute,then_run;fold o;rewrite Next;cbn [bind];rewrite Call;exact Store|constructor].
 - exact End.
 - exact Done.
 - exact WF.
 - intro r;rewrite Reg,G;change (put (regs s) 8 a r=if (r=?8)%nat then a else regs s r).
   unfold put;now rewrite Nat.eqb_sym.
 - intros i j N;rewrite Vec;apply Consts,N.
 - intros x [X Y];rewrite Unchanged by lia;exact (Keep x X).
 - intros j i J N;assert (Data:vectors(machine mul) j i=candidate s j i) by exact (Product j i J N).
   split;[rewrite Vec;exact Data|unfold row;rewrite (Rows i j N J);exact Data].
Qed.

From Ed25519Simd.VerifyBatch Require Selection RootTest RootDecision.
Record trace:=Trace { decision:Selection.trace; saved_x:cursor }.
Definition observe pol bias e p bank:=bind (Selection.observe pol bias e p bank) (fun r=>
 option_map (Trace r) (execute bias (Selection.selection r))).
Record post pol bias e t : Prop:=Post {
 selection:Selection.post pol bias e (decision t);
 native:result false pol bias e (Selection.selection(decision t)) (saved_x t)
}.

Theorem from_decoder pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 exists t,observe pol bias e p bank=Some t /\ post pol bias e t.
Proof.
 intros P I Al Entry W;destruct(Selection.from_decoder _ _ _ _ bank P I Al Entry W) as [r [R S]].
 pose proof(Selection.test_result _ _ _ _ S) as T.
 destruct(RootTest.finish_arguments _ _ _ _ T) as [_ [_ [_ [SP [DI [SI _]]]]]].
 destruct(RootTest.root_product _ _ _ _ T) as [_ [_ [_ [G _]]]].
 assert (Reg:forall n,n<>8%nat -> n<>10%nat -> regs(machine(Selection.selection r)) n=
   regs(machine(RootTest.finish_entry(Selection.test r))) n) by
   (intros n B K;rewrite (Selection.scalar_registers _ _ _ _ S n K);apply G,B).
 destruct(checked false pol bias e (Selection.selection r) P I (Selection.at_selection _ _ _ _ S)
   (Selection.writes _ _ _ _ S) (Selection.machine_words _ _ _ _ S)
   ltac:(rewrite Reg by discriminate;exact SP) ltac:(rewrite Reg by discriminate;exact DI)
   ltac:(rewrite Reg by discriminate;exact SI) (Selection.curve_constants _ _ _ _ S))
   as [q [Run Result]].
 exists(Trace r q);split;[unfold observe;rewrite R;cbn [bind];now rewrite Run|exact (Post pol bias e (Trace r q) S Result)].
Qed.
