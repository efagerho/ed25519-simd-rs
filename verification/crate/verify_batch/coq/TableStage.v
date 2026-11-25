From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.InstructionRoute execution.MappedFetch execution.AlignedRows
 memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.KeyTable Require Frame Image.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableEntry TableFrame TableProduct.
Import ListNotations. Local Open Scope Z_scope.

Definition branch:list line:=[(622,4%nat,Compare32 15 1);(626,2%nat,Branch Unequal 119)].
Definition select:list line:=[(747,3%nat,Compare32 3 1);(750,6%nat,Branch Equal (1078-756))].
Lemma image:linked TableFrame.text branch /\ linked TableFrame.text (route true 628 16 4 0 10) /\
 linked TableFrame.text (route true 707 5 4 640 5) /\ linked TableFrame.text select.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition buffer a x:=a<=x<a+960.
Definition initialized a (s t:cpu):=forall i j,(i<15)%nat -> (j<8)%nat ->
 read_word (mem t) (a+64*Z.of_nat i+8*Z.of_nat j)=vectors s j (Image.reg_for i).

Lemma store_rows o a s c : regs s 4%nat=a -> a mod 64=0 -> fits64 a 960 -> well_formed s ->
 exists t ws,run 15 (ScalarBytes.fetch o TableFrame.text) (State(Running 628) s c)=Some(State(Running 747) t c,ws) /\
 regs t=regs s /\ vectors t=vectors s /\ confined (buffer a) ws /\ initialized a s t.
Proof.
 intros SP Al Fit [_ [W _]].
 destruct(AlignedRows.stores o _ 10 628 16 4 0 a s c (proj1(proj2 image)) ltac:(lia) Al
   ltac:(unfold fits64 in *;change (Z.of_nat 10) with 10;lia) ltac:(intros;apply W;assumption)) as [b [ws [A [G [V [F [Head Rows]]]]]]].
 destruct(AlignedRows.stores o _ 5 707 5 4 640 (a+640) b c (proj1(proj2(proj2 image))) ltac:(now rewrite G,SP)
   ltac:(replace (a+640) with (a+10*64) by ring;now rewrite Z.mod_add by lia)
   ltac:(unfold fits64 in *;change (Z.of_nat 5) with 5;lia) ltac:(intros;rewrite V;apply W;assumption)) as [t [tail [B [GB [VB [_ [Tail Last]]]]]]].
 change (AlignedRows.after true 628 16 4 0 10) with 707 in A;change (AlignedRows.after true 707 5 4 640 5) with 747 in B.
 exists t,(ws++tail);split;[exact (run_append _ _ _ _ _ A _ _ _ B)|].
 split;[now rewrite GB,G|split;[now rewrite VB,V|split]].
 - apply Forall_app;split;[eapply Forall_impl;[|exact Head]|eapply Forall_impl;[|exact Tail]];
   intros w Q x X;specialize(Q x X);unfold range,buffer in *;lia.
 - intros i j N J;unfold Image.reg_for;destruct(Nat.ltb_spec i 10) as [First|Later].
   + rewrite <- (Rows i j First J);apply preserved_read with (outside:=fun x=>~range (a+640) 5 x).
     * pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ B)) as M;change (mem t=WriteTrace.replay (mem b) tail) in M;
       intros x X;rewrite M;apply (WriteTrace.frame _ _ Tail),X.
     * intros k K;change (0<=k<8) in K;unfold range;lia.
   + rewrite (proj2(Nat.ltb_lt i 15) N).
     replace (a+64*Z.of_nat i+8*Z.of_nat j) with (a+640+64*Z.of_nat(i-10)+8*Z.of_nat j) by lia.
     rewrite (Last (i-10)%nat j ltac:(lia) J),V;f_equal;lia.
Qed.
Definition digit bias:=segment (TableFrame.base bias) TableFrame.text 2.
Definition store bias:=segment (TableFrame.base bias) TableFrame.text 15.
Definition select_bulk bias:=segment (TableFrame.base bias) TableFrame.text 2.
Definition execute bias p:=bind (digit bias p) (fun d=>
 bind (if regs(machine d) 15%nat=?1 then store bias d else Some d) (select_bulk bias)).
Record post pol bias e digit p q : Prop:=Post {
 address:ip q=TableFrame.base bias+756;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 registers:regs(machine q)=regs(machine p);
 bank:vectors(machine q)=vectors(machine p);
 positive:digit=1 -> initialized (TableProduct.frame pol e) (machine p) (machine q);
 later:digit<>1 -> mem(machine q)=mem(machine p);
 outside:preserved (fun x=>~buffer (TableProduct.frame pol e) x) (mem(machine p)) (mem(machine q))
}.

Theorem checked pol bias e n p : placement e -> loaded pol bias (mem e) (writable e) -> 1<=n<=8 ->
 ip p=TableFrame.base bias+622 -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 15%nat=n -> regs(machine p) 3%nat=8 -> regs(machine p) 4%nat=TableProduct.frame pol e ->
 exists q,execute bias p=Some q /\ post pol bias e n p q.
Proof.
 intros P I N PC Acc W Digit Count SP;set (s:=machine p) in *;set (o:=TableFrame.base bias) in *;
 set (a:=TableProduct.frame pol e) in *;set (z:=n=?1);set (v:=with_zf s z);set (cf0:=Some(n<?1)).
 assert (Branch:run 2 (ScalarBytes.fetch o TableFrame.text) (State(Running 622) s (LinkedRun.carry p))=
    Some(State(Running(if z then 628 else 747)) v cf0,[])).
 { apply (InstructionRoute.checked _ _ _ (proj1 image));cbn [branch follow loc cpu_state cf step option_map eval_condition flag with_zf];
   rewrite Digit,(Z.mod_small n (2^32)) by lia;change (1 mod 2^32) with 1;fold z;destruct z;reflexivity. }
 destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 destruct(at_segment _ _ p o TableFrame.text 2 622 _ _ Acc PC Map Sep Branch (Forall_nil _)) as [Reached Paid].
 set (d:=LinkedRun.finish o p (State(Running(if z then 628 else 747)) v cf0,[])) in *.
 assert (DW:=segment_wf _ _ _ _ _ W Reached).
 assert (Stage:exists h,(if z then store bias d else Some d)=Some h /\ ip h=o+747 /\ accounted e (writable e) h /\
   well_formed(machine h) /\ regs(machine h)=regs s /\ vectors(machine h)=vectors s /\
   (z=true -> initialized a s (machine h)) /\ (z=false -> mem(machine h)=mem s) /\
   preserved (fun x=>~buffer a x) (mem s) (mem(machine h))).
 { destruct z eqn:Z.
   - assert (Align:a mod 64=0).
     { unfold a,TableProduct.frame,KeyTable.Frame.staging,KeyTable.Frame.allocation;rewrite Zminus_mod,KeyTable.Frame.aligned;reflexivity. }
     assert (Bounds:Return.sp e-2500<=a /\ a+960<=Return.sp e).
     { unfold a,TableProduct.frame,KeyTable.Frame.staging,KeyTable.Frame.allocation,KeyTable.Frame.align64;
       change KeyTable.Frame.saved_size with 48;pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia)).
       unfold TableEntry.frame,common_top,Rows.frame,sp in *;destruct pol;lia. }
     destruct(stack_ok _ P) as [[L H] _].
     destruct(store_rows o a v cf0 SP Align ltac:(unfold fits64;lia) DW) as [t [ws [R [G [V [Safe Rows]]]]]].
     assert (Ok:confined (writable e) ws) by (eapply Forall_impl;[|exact Safe];intros w F x X;
       specialize(F x X);left;unfold span,buffer in *;lia).
     assert (At:ip d=o+628) by reflexivity.
     destruct(at_segment _ _ d o TableFrame.text 15 628 _ _ Paid At Map Sep R Ok) as [Run Done].
     eexists;split;[exact Run|split;[reflexivity|split;[exact Done|split;[exact (segment_wf _ _ _ _ _ DW Run)|]]]].
     split;[exact G|split;[exact V|split;[intros _;exact Rows|split;[discriminate|]]]].
     pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)) as M;change (mem t=WriteTrace.replay (mem v) ws) in M.
     intros x X;change (mem t x=mem s x);rewrite M;exact (WriteTrace.frame _ _ Safe _ x X).
   - exists d;split;[reflexivity|split;[reflexivity|]].
     split;[exact Paid|split;[exact DW|split;[reflexivity|split;[reflexivity|split;[discriminate|split;[intros;reflexivity|intros x X;reflexivity]]]]]]. }
 destruct Stage as [h [Staged [At [Ok [HW [G [V [Row [Later Outside]]]]]]]]].
 set (out:=with_zf (machine h) false).
 assert (Select:run 2 (ScalarBytes.fetch o TableFrame.text) (State(Running 747) (machine h) (LinkedRun.carry h))=
   Some(State(Running 756) out (Some false),[])).
 { apply (InstructionRoute.checked _ _ _ (proj2(proj2(proj2 image))));cbn [select follow loc cpu_state cf step option_map eval_condition flag with_zf];rewrite G,Count;reflexivity. }
 destruct(mapped_now _ _ _ I _ _ _ Ok (TableEntry.image pol)) as [MapH _].
 destruct(at_segment _ _ h o TableFrame.text 2 747 _ _ Ok At MapH Sep Select (Forall_nil _)) as [Run End].
 eexists;split.
 - unfold execute,digit;fold o;rewrite Reached;cbn [bind];change (regs(machine d) 15%nat) with (regs s 15%nat);rewrite Digit;fold z;rewrite Staged;exact Run.
 - constructor;[reflexivity|exact End|exact (segment_wf _ _ _ _ _ HW Run)|exact G|exact V| | |exact Outside].
   + intros One;apply Row;unfold z;now apply Z.eqb_eq.
   + intros Many;apply Later;unfold z;now apply Z.eqb_neq.
Qed.
