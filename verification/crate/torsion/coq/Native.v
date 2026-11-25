From Coq Require Import ZArith List Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarWords execution.MappedFetch execution.MaskReturn memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Machine Require execution.MaskTrace execution.MaskStores.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Torsion Require Import Program Audit.
Local Open Scope Z_scope.

Definition raw pad:=MaskTrace.program_writes 1500 1032 20 code pad.
Definition point p b:=buffer_words (mem(machine p)) (regs(machine p) b).
Definition rows p:=inputs (point p 7%nat) (point p 6%nat).
Definition execute pc pad p:=MaskReturn.execute pc pad (raw pad) (rows p) p.
Definition stack p x:=regs(machine p) 4%nat-1032<=x<regs(machine p) 4%nat.
Definition operand p b x:=regs(machine p) b<=x<regs(machine p) b+1280.
Definition bases b:=b=7%nat \/ b=6%nat.
Definition reads pc (text:list Z) p x:=pc<=x<pc+Z.of_nat(length text) \/ exists b,bases b /\ operand p b x.
Record placement pc text pad p : Prop := Place {
 entry:ip p=pc; aligned:regs(machine p) 4%nat mod 64=MaskStores.origin pad;
 stack_fits:fits64 (regs(machine p) 4%nat-1032) 1040;
 operands_fit:forall b,bases b -> fits64 (regs(machine p) b) 1280;
 image:mapped (mem(machine p)) pc text; separate:forall x,reads pc text p x -> ~stack p x
}.

(* MaskTrace accepts input loads only through RDI and RSI. For every store
   prefix the bytes for both operands and the entire fetched symbol remain
   available at their original addresses. *)
Definition prefix_inputs pc text pad p:=forall pre suffix,
 MaskReturn.saved_log pc pad (raw pad) (rows p) p=pre++suffix ->
 let m:=replay (mem(machine p)) pre in mapped m pc text /\
 forall b i j,bases b -> (i<20)%nat -> (j<8)%nat ->
 rows p j b i=read_word m (word(regs(machine p) b+64*Z.of_nat i+8*Z.of_nat j)).

Lemma prefixes pc text pad p:placement pc text pad p ->
 confined (stack p) (MaskReturn.saved_log pc pad (raw pad) (rows p) p) -> prefix_inputs pc text pad p.
Proof.
 intros P All pre suffix E;rewrite E in All;apply Forall_app in All as [H _];cbv zeta.
 assert (Keep:preserved (reads pc text p) (mem(machine p)) (replay (mem(machine p)) pre)).
 { intros x X;apply (WriteTrace.frame _ _ H),(separate _ _ _ _ P x X). }
 split.
 - intros j J;rewrite Keep;[apply (image _ _ _ _ P),J|left;lia].
 - intros b i j B I J;destruct(operands_fit _ _ _ _ P b B) as [L H'].
   rewrite word_fits by (unfold word64;lia).
   assert (At:rows p j b i=read_word (mem(machine p)) (regs(machine p) b+64*Z.of_nat i+8*Z.of_nat j)).
   { destruct B as [->| ->];unfold rows,inputs,point,cell,buffer_words;cbn [Nat.eqb];
     f_equal;rewrite Nat2Z.inj_add,Nat2Z.inj_mul;ring. }
   rewrite At;symmetry;apply preserved_read with (outside:=reads pc text p);[exact Keep|].
   intros k K;right;exists b;split;[exact B|unfold operand;change (0<=k<8) in K;lia].
Qed.

Local Opaque MaskTrace.program_writes MaskTrace.result.
Lemma result_from_tree pad p initial :
 MaskTrace.result (raw pad) (rows p) initial=
 MaskTrace.result (MaskTrace.program_tree 1500 1032 20 code pad) (rows p) initial.
Proof. unfold MaskTrace.program_tree;exact (eq_sym (MaskTrace.erase_result (raw pad) (rows p) initial)). Qed.
Local Opaque code MaskTrace.program_tree MaskTrace.program_writes MaskTrace.result.
Theorem checked pc text pad p bank:torsion_contract text -> (pad<4)%nat ->
 placement pc text pad p -> well_formed(machine p) -> input_bounds (point p 7%nat) (point p 6%nat) ->
 exists q ks mask,execute pc pad p bank=Some(q,ks) /\
 MaskReturn.returned pc pad 1032 (raw pad) (rows p) p mask q /\
 prefix_inputs pc text pad p /\ 0<=mask<256 /\ regs(machine q) 0%nat=mask /\
 forall j,(j<8)%nat -> lane_result mask j (point_values (point p 7%nat) j) (point_values (point p 6%nat) j).
Proof.
 intros C Pad Place W B;pose proof(write_footprint _ C pad Pad) as Range.
 destruct(run_correct _ C pad _ _ (vectors(machine p)) Pad B) as [m [Run [Byte Bits]]].
 pose proof (eq_trans (result_from_tree pad p (vectors(machine p))) Run) as RawRun.
 destruct(MaskReturn.checked pc pad 1032 (raw pad) (rows p) p bank m Range W RawRun) as [q [ks [R Ret]]].
 exists q,ks,m;split;[exact R|split;[exact Ret|split]].
 - apply prefixes;[exact Place|exact (MaskReturn.stores _ _ _ _ _ _ _ _ Ret)].
 - split;[exact Byte|split;[rewrite (MaskReturn.eax _ _ _ _ _ _ _ _ Ret);apply word_fits;unfold word64;lia|exact Bits]].
Qed.
