From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.LinkedCalls execution.LinkedRun execution.WordBounds
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.VectorWindow execution.VectorSpills
 memory.ByteMemory memory.MemoryGeometry memory.WriteTrace execution.VectorProcedure.
From Ed25519Simd.Decode Require Decode.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition load:list line:=[(1380,10%nat,BroadcastRip 0 (0xb80-1390))].
Definition spills:=[Spill 0 10;Compute(10%nat,Xor 10 10);Spill 10 11;Spill 10 12;Spill 10 13;Spill 10 14].
Definition execute bias:=then_run (segment (base bias) text 1) (segment (base bias) text 6).
Lemma images:linked text load /\ linked text (VectorSpills.route 7 1390 spills) /\
 forallb (admissible 20) spills=true /\ VectorWindow.scan text 7 640 960 1390 6=Some 1431.
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Theorem checked sig pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=base bias+1380 -> accounted e (writable e) p -> well_formed(machine p) -> regs(machine p) 7%nat=point e sig ->
 exists q,execute bias p=Some q /\ ip q=base bias+1431 /\ accounted e (writable e) q /\ well_formed(machine q) /\
 regs(machine q)=regs(machine p) /\ preserved (fun x=>~(point e sig+640<=x<point e sig+960)) (mem(machine p)) (mem(machine q)) /\
 (forall j i,(j<8)%nat -> (i<5)%nat -> row (machine q) (point e sig+640) j i=Decode.one i) /\
 forall j r,(28<=r)%nat -> vectors(machine q) j r=vectors(machine p) j r.
Proof.
 intros P I PC Acc W DI;set (o:=base bias) in *;set (s:=machine p) in *;set (a:=point e sig) in *.
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 pose proof(read_literal bias DecoderFrame.origin text 0xb80 1 (mem s) Map
   (proj1(symbols _ _ _ _ I _ _ (decode_in pol))) ltac:(lia) ltac:(change (2952<=2984);lia) ltac:(vm_compute;reflexivity)) as Lit.
 set (v:=vector_dest s 0 (fun _=>1)).
 assert (R:run 1 (ScalarBytes.fetch o text) (State (Running 1380) s (LinkedRun.carry p))=
  Some(State (Running 1390) v (LinkedRun.carry p),[])).
 { apply (InstructionRoute.checked _ _ _ (proj1 images));cbn [load follow step loc cf cpu_state option_map].
   replace (o+(1380+Z.of_nat 10)+(0xb80-1390)) with (bias+DecoderFrame.origin+0xb80) by (unfold o,base;ring).
   rewrite Lit;reflexivity. }
 destruct(at_segment _ _ _ o text 1 1380 _ _ Acc PC Map Sep R (Forall_nil _)) as [Start Paid].
 set (mid:=LinkedRun.finish o p (State (Running 1390) v (LinkedRun.carry p),[])) in *.
 assert (WM:well_formed v) by exact (segment_wf _ _ _ _ _ W Start).
 destruct(scratch_ok _ P) as [[L H] Align];assert (Al:a mod 64=0) by (apply point_aligned,Align).
 destruct(VectorWindow.execute o text 7 640 960 a 6 1390 1431 v (LinkedRun.carry p) (proj2(proj2(proj2 images))) DI Al
  ltac:(unfold a,point,point_offset;destruct sig;lia) ltac:(unfold a,point,point_offset;destruct sig;lia))
  as [t [ws [Run [G Safe]]]].
 assert (Ok:confined (writable e) ws).
 { apply Forall_impl with (P:=permits (VectorWindow.interval a 640 960));[|exact Safe].
   intros w B x X;specialize(B x X);right;left;unfold VectorWindow.interval,span,a,point,point_offset in *;destruct sig;lia. }
 destruct(at_segment _ _ mid o text 6 1390 _ _ Paid eq_refl Map Sep Run Ok) as [Store Done].
 eexists;split;[unfold execute,then_run;fold o;rewrite Start;exact Store|].
 split;[reflexivity|split;[exact Done|split;[exact (segment_wf o text 6 mid _ WM Store)|split;[exact G|split]]]].
 - pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)) as M;change (mem t=WriteTrace.replay (mem v) ws) in M.
   intros x X;change (mem t x=mem v x);rewrite M;exact (WriteTrace.frame _ _ Safe _ x X).
 - split.
   2:{ intros j r High;change (vectors t j r=vectors s j r);
       transitivity (vectors v j r);[exact (VectorWindow.upper_registers o text 28 6 1390 v (LinkedRun.carry p) _ ws ltac:(vm_compute;reflexivity) Run j r High)|];
       unfold v,vector_dest;cbn [vectors];unfold put;now rewrite (proj2(Nat.eqb_neq 0 r) ltac:(lia)). }
   intros j i J N;set (old:=row v a j).
   destruct(VectorSpills.execute o text 7 a 20 j spills 1390 v (LinkedRun.carry p) _ ws (View (vectors v j) old)
     (proj1(proj2 images)) (proj1(proj2(proj2 images))) J WM DI Al
     ltac:(unfold fits64,a,point,point_offset;destruct sig;change (Z.of_nat 20) with 20;lia)
     ltac:(split;reflexivity) Run) as [_ Rows].
   change (row t (a+640) j i=Decode.one i);unfold row;replace (a+640+64*Z.of_nat i+8*Z.of_nat j)
       with (a+64*Z.of_nat(10+i)+8*Z.of_nat j) by lia.
   cbn [cpu_state] in Rows;rewrite (Rows (10+i)%nat ltac:(lia));destruct i as [|[|[|[|[|i]]]]];try lia;cbn [spills fold_left lane rows registers bits put Nat.eqb Decode.one Limbs.five];
    unfold Logic.vpxorq;rewrite ?Z.lxor_nilpotent;reflexivity.
Qed.
