From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.VectorProcedure execution.AlignedRows
 memory.ByteMemory memory.MemoryGeometry memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.Decode Require Decode Kernels Power.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderProduct DecoderFrame RowProduct FieldStores SetupValues ProjectiveOne.
Import ListNotations. Local Open Scope Z_scope.

Definition pointer:list line:=[(1333,7%nat,LeaG 8 (Address 7 None 320))].
Lemma code:linked text (AlignedRows.route true 1299 0 7 0 5) /\ linked text pointer /\
 ScalarBytes.decode(skipn 1340 text)=Some(5%nat,CallRelative(0xa57-1345)) /\ linked text (AlignedRows.route true 1345 0 7 960 5).
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition step bias:=segment (base bias) text.
Definition execute bias:=then_run (step bias 5) (then_run (step bias 1) (then_run (DecoderProduct.multiply_call bias)
 (then_run (step bias 5) (ProjectiveOne.execute bias)))).
Definition protected sig pol e x:=let a:=point e sig in
 ~(link_slot pol e-24<=x<link_slot pol e) /\ ~(a<=x<a+320) /\ ~(a+640<=x<a+1280).
Record result sig pol bias e p q : Prop:=Result {
 next:ip q=base bias+1431;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 gprs:forall r,regs(machine q) r=if (r=?8)%nat then point e sig+320 else regs(machine p) r;
 frame:preserved (protected sig pol e) (mem(machine p)) (mem(machine q));
 point_rows:forall j i,(j<8)%nat -> (i<5)%nat ->
  let a:=point e sig in let x:=vectors(machine p) j in let y:=row (machine p) (a+320) j in
  row (machine q) a j i=x i /\ row (machine q) (a+320) j i=y i /\
  row (machine q) (a+640) j i=Decode.one i /\
  row (machine q) (a+960) j i=Power.apply_kernel DecoderProduct.kernel Kernels.Multiply x y i
}.

Theorem checked sig pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=base bias+1299 -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 4%nat=link_slot pol e -> regs(machine p) 7%nat=point e sig -> RowProduct.constants(machine p) ->
 exists q,execute bias p=Some q /\ result sig pol bias e p q.
Proof.
 intros P I PC Acc W SP DI C;set (a:=point e sig) in *;set (o:=base bias) in *;set (st:=link_slot pol e) in *.
 destruct code as [StoreX [Lea [Multiply StoreT]]].
 destruct(FieldStores.execute sig pol bias e 1299 0 p P I StoreX ltac:(lia) eq_refl PC Acc W DI)
  as [x [X [At Paid WX GX VX SavedX NotX]]].
 set (s:=machine x) in *;set (v:=set s 8 (a+320)).
 destruct(scratch_ok _ P) as [[L H] Al];pose proof(depth pol e) as Depth;fold st in Depth.
 assert (Fit:fits64 (a+320) 320) by (unfold fits64,a,point,point_offset;destruct sig;lia).
 assert (A:a mod 64=0) by (apply point_aligned,Al).
 assert (Split:forall z,a<=z<a+1280 -> ~(st-24<=z<st)) by
  (intros z Z;destruct(scratch_stack _ P);unfold disjoint,a,point,point_offset in *;destruct sig;lia).
 assert (R:run 1 (ScalarBytes.fetch o text) (State (Running 1333) s (LinkedRun.carry x))=
  Some(State (Running 1340) v (LinkedRun.carry x),[])).
 { apply (InstructionRoute.checked _ _ _ Lea);cbn [pointer follow step ScalarBytes.step loc cf cpu_state effective option_map].
   rewrite GX,DI,Z.add_0_r,word_fits by (unfold fits64,word64 in *;lia);reflexivity. }
 destruct(mapped_now _ _ _ I _ _ _ Paid (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text 1 1333 _ _ Paid At Map Sep R (Forall_nil _)) as [Next More].
 set (mid:=LinkedRun.finish o x (State (Running 1340) v (LinkedRun.carry x),[])) in *.
 assert (WM:well_formed(machine mid)) by exact (segment_wf o text 1 x _ WX Next).
 assert (CM:RowProduct.constants(machine mid)) by (intros i j N;change (vectors s j (28+i)%nat=DecoderFrame.constant i);rewrite VX;apply C,N).
 assert (SM:regs(machine mid) 4%nat=st) by (change (regs s 4%nat=st);now rewrite GX).
 destruct(RowProduct.called pol bias e 1340 mid P I ltac:(lia) ltac:(lia) Multiply eq_refl More WM SM CM
   ltac:(change ((a+320) mod 64=0);replace 320 with (5*64) by ring;now rewrite Z.mod_add by lia)
   Fit ltac:(intros z Z;change (a+320<=z<a+320+320) in Z;specialize(Split z ltac:(lia));lia))
  as [mul [Call [End Safe WF GM KM _ XY]]].
 assert (DM:regs(machine mul) 7%nat=a) by (rewrite GM;change (regs s 7%nat=a);now rewrite GX).
 destruct(FieldStores.execute sig pol bias e 1345 960 mul P I StoreT ltac:(lia) eq_refl End Safe WF DM)
  as [t [T [AtZ PaidZ WT GT VT SavedT NotT]]].
 destruct(ProjectiveOne.checked sig pol bias e t P I AtZ PaidZ WT ltac:(rewrite GT;exact DM))
  as [q [Z [Last [Done [WQ [GQ [NotZ One]]]]]]].
 assert (Outside:preserved (protected sig pol e) (mem(machine p)) (mem(machine q))).
 { intros z [K [Xout TZ]];rewrite NotZ,NotT,KM by lia;apply NotX;fold a;lia. }
 fold o in X,T;exists q;split;[unfold execute,then_run,step;fold o;rewrite X;cbn [bind];rewrite Next;cbn [bind];rewrite Call;cbn [bind];rewrite T;exact Z|constructor].
 - exact Last.
 - exact Done.
 - exact WQ.
 - intro r;rewrite GQ,GT,GM;change (put (regs s) 8 (a+320) r=if (r=?8)%nat then a+320 else regs(machine p) r).
   unfold put;now rewrite GX,Nat.eqb_sym.
 - exact Outside.
 - intros j i J N;fold a.
   assert (KeepX:preserved (fun z=>a<=z<a+320) (mem s) (mem(machine q))).
   { intros z Xr;rewrite NotZ,NotT,KM;[reflexivity|apply Split;lia|fold a;lia|fold a;lia]. }
   assert (Y:forall k,(k<5)%nat -> row s (a+320) j k=row (machine p) (a+320) j k).
   { intros k B;eapply SetupValues.keep_row;[exact NotX|intros z Xr;change (~(a+0<=z<a+0+320));lia|exact J|exact B]. }
   split.
   + rewrite (SetupValues.keep_row _ _ a _ KeepX ltac:(auto) j i J N).
     unfold AlignedRows.saved in SavedX;rewrite Z.add_0_r in SavedX;apply SavedX;assumption.
   + split;[eapply SetupValues.keep_row;[exact Outside|intros z Xr;unfold protected;fold a st;split;[apply Split|split];lia|exact J|exact N]|].
     split;[apply One;assumption|].
     rewrite (SetupValues.keep_row _ _ (a+960) _ NotZ ltac:(intros z Xr;change (~(a+640<=z<a+960));lia) j i J N).
     transitivity (vectors(machine mul) j i);[exact (SavedT i j N J)|rewrite (XY j i J N);apply RowProduct.ext].
     * intros k B;change (vectors s j k=vectors(machine p) j k);now rewrite VX.
     * exact Y.
Qed.
