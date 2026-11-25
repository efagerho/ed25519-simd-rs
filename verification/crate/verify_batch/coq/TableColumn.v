From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.InstructionRoute execution.MappedFetch execution.AlignedRows
 execution.QwordBlock execution.VectorProcedure memory.MemoryGeometry memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.KeyTable Require Fields.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableFrame TableEntry TableProduct TableLinear TableKernels.
Module L:=TableLinear.
Local Open Scope Z_scope.
Definition src f:=320*Z.of_nat(Fields.source(L.operation f)).
Definition coord e s j c i:=read_word (mem s) (TableEntry.point e+320*Z.of_nat c+64*Z.of_nat i+8*Z.of_nat j).
Definition value f e s j:=Fields.compute DecoderProduct.kernel (coord e s j) (L.operation f).
Definition prepare bias f:=segment (TableFrame.base bias) TableFrame.text (10+length(L.linear f)).
Definition execute bias f:=then_run (prepare bias f) (TableKernels.call bias (L.operation f)).
Lemma route f : linked TableFrame.text (AlignedRows.route false (L.start f+30) 0 12 (src f) 5) /\
 QwordBlock.after (L.start f) (L.keep f)=L.start f+30 /\ AlignedRows.after false (L.start f+30) 0 12 (src f) 5=L.at_linear f /\
 QwordBlock.after (L.at_linear f) (L.linear f)=TableKernels.site (L.operation f).
Proof. destruct f;repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Record column f e s t : Prop:=Column {
 limbs:forall j i,(i<5)%nat -> vectors t j i=value f e s j i;
 saved:forall j i,(i<5)%nat -> vectors t j (L.save_register f+i)%nat=vectors s j i;
 other:forall j r,L.reserved r=true -> (r<L.save_register f \/ L.save_register f+5<=r)%nat -> vectors t j r=vectors s j r
}.
Definition constants s:=forall j i,(i<4)%nat -> vectors s j (28+i)%nat=DecoderFrame.constant i.

Theorem checked pol bias e f p : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=TableFrame.base bias+L.start f -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 12%nat=TableEntry.point e -> regs(machine p) 4%nat=TableProduct.frame pol e -> constants(machine p) ->
 exists q,execute bias f p=Some q /\ ip q=TableFrame.base bias+(TableKernels.site(L.operation f)+5) /\
 accounted e (writable e) q /\ well_formed(machine q) /\ (forall r,regs(machine q) r=regs(machine p) r) /\
 preserved (fun x=>~(TableProduct.frame pol e-8<=x<TableProduct.frame pol e)) (mem(machine p)) (mem(machine q)) /\
 column f e (machine p) (machine q).
Proof.
 intros P I PC Acc W R12 SP Constants;set (s:=machine p) in *;set (o:=TableFrame.base bias) in *;
 set (pt:=TableEntry.point e) in *;set (c:=LinkedRun.carry p).
 destruct(L.image f) as [Copy Linear];destruct(route f) as [Loads [Off1 [Off2 Off3]]].
 destruct(QwordBlock.execute o _ _ _ s c Copy) as [a [A [GA [MA [FA CopyRows]]]]].
 rewrite Off1 in A;assert (Five:length(L.keep f)=5%nat) by (unfold L.keep;rewrite length_map;reflexivity);rewrite Five in A.
 assert (Al:(pt+src f) mod 64=0).
 { replace (pt+src f) with (scratch e+(16+5*Z.of_nat(Fields.source(L.operation f)))*64)
      by (unfold pt,src,TableEntry.point;ring);rewrite Z.mod_add by lia;exact (proj2(scratch_ok _ P)). }
 destruct(scratch_ok _ P) as [[Low High] _].
 assert (Bound:fits64 (pt+src f) (64*Z.of_nat 5)) by (unfold fits64,pt,TableEntry.point;destruct f;change (src _) with 320 || change (src _) with 640;lia).
 destruct(AlignedRows.loads o _ 5 _ _ _ _ (pt+src f) a c Loads ltac:(now rewrite GA,R12) Al Bound)
   as [b [B [GB [MB [FB [Rows Held]]]]]];rewrite Off2 in B.
 destruct(QwordBlock.execute o _ _ _ b c Linear) as [t [T [GT [MT [FT Out]]]]];rewrite Off3 in T.
 pose proof(run_append _ _ _ _ _ (run_append _ _ _ _ _ A _ _ _ B) _ _ _ T) as Run.
 destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 destruct(at_segment _ _ p o TableFrame.text _ _ _ _ Acc PC Map Sep Run (Forall_nil _)) as [Setup Paid].
 set (mid:=LinkedRun.finish o p (State(Running(TableKernels.site(L.operation f))) t c,nil)) in *.
 assert (G:regs t=regs s) by now rewrite GT,GB,GA.
 assert (M:mem t=mem s) by now rewrite MT,MB,MA.
 assert (Depth:TableKernels.depth(L.operation f)=0) by (destruct f;reflexivity).
 assert (Space:room (DecoderProduct.area e) (8+TableKernels.depth(L.operation f)) t).
 { unfold room,DecoderProduct.area;cbn [bottom ceiling];rewrite Depth,G,SP;unfold TableProduct.frame,
   KeyTable.Frame.staging,KeyTable.Frame.align64,KeyTable.Frame.allocation;change KeyTable.Frame.saved_size with 48.
   pose proof(Z.mod_pos_bound (TableEntry.frame pol e-48) 64 ltac:(lia)).
   unfold TableEntry.frame,common_top,Rows.frame,Return.sp in *;destruct pol;lia. }
 destruct(TableKernels.checked _ _ _ (L.operation f) P I mid eq_refl Paid Space) as [q [Call [End Done Reg Safe Result]]].
 assert (K:TableKernels.code(L.operation f)=Kernels.carry DecoderProduct.kernel) by (destruct f;reflexivity).
 assert (Higher:forall j r,(5<=r)%nat -> vectors t j r=lane (vector_load s j) (vectors s j) (L.keep f) r).
 { intros j r R;rewrite Out,L.linear_other,Held,CopyRows by lia;reflexivity. }
 assert (Both:forall j i,(i<5)%nat -> vectors b j i=coord e s j (Fields.source(L.operation f)) i).
 { intros j i N;pose proof(Rows j i N) as Row;rewrite MA in Row;exact Row. }
 assert (X:forall j, f<>Fields.Twice -> forall i,(i<5)%nat -> vector_load b j 12 (64*Z.of_nat i)=coord e s j (Fields.rhs (L.operation f)) i).
 { intros j F i N;unfold vector_load,coord;rewrite GB,GA,R12,MB,MA.
   rewrite word_fits by (unfold word64,pt,TableEntry.point;lia).
   destruct f;[| |contradiction];cbn [Fields.rhs L.operation];fold pt;replace (pt+320*Z.of_nat 0) with pt by ring;reflexivity. }
 assert (Const:forall j i,(i<4)%nat -> vectors b j (28+i)%nat=DecoderFrame.constant i).
 { intros j i N;rewrite Held,CopyRows,L.keep_other by (destruct f;cbn [L.save_register];lia);apply Constants,N. }
 exists q;split;[unfold execute,then_run;change (prepare bias f p=Some mid) in Setup;rewrite Setup;exact Call|split;[exact End|split;[exact Done|split]]].
 - exact (TableKernels.preserves_words _ _ _ _ (segment_wf _ _ _ _ _ W Setup) Call).
 - split;[intro r;rewrite Reg;exact (f_equal (fun rs=>rs r) G)|split].
   + intros x Outside;rewrite Safe;[exact (f_equal (fun m=>m x) M)|];change (~(regs t 4%nat-(8+TableKernels.depth(L.operation f))<=x<regs t 4%nat));now rewrite G,SP,Depth.
   + constructor.
     * intros j i N;rewrite (Result j),K;change (vectors(machine mid) j) with (vectors t j);rewrite Out.
       pose proof(L.column f (vector_load b j) (vectors b j) (coord e s j (Fields.source(L.operation f)))
          (coord e s j (Fields.rhs(L.operation f))) (Both j) (X j) (Const j) i N) as Eq.
       destruct f;exact Eq.
     * intros j i N;rewrite (Result j),K,L.saved_after by (destruct f;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity).
       change (vectors t j (L.save_register f+i)%nat=vectors s j i);rewrite Higher by (destruct f;cbn [L.save_register];lia);
       apply L.keep_values,N.
     * intros j r R Away;rewrite (Result j),K,L.saved_after by exact R;change (vectors t j r=vectors s j r).
       rewrite Higher;[apply L.keep_other,Away|unfold L.reserved in R;repeat rewrite Bool.orb_true_iff in R;
         rewrite Bool.andb_true_iff in R;destruct R as [[Lower _]|Upper];apply Nat.leb_le in Lower || apply Nat.leb_le in Upper;lia].
Qed.
