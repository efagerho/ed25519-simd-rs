From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds
 execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.MappedFetch
 execution.InstructionRoute execution.AlignedRows execution.RipBroadcasts memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.Decode Require HelperBytes.
From Ed25519Simd.KeyTable Require Fields.
From Ed25519Simd.KeyTable Require TableKernels.
From Ed25519Simd.KeyTable Require Import CallLayout.
From Ed25519Simd.Decode Require FieldLiterals.
Import ListNotations. Local Open Scope Z_scope.

Definition constants:=HelperBytes.address+0xde0-CallLayout.origin.
Definition factor:=0x8c0.
Lemma sites:linked CallLayout.text (RipBroadcasts.route 4 124 28 constants) /\
 linked CallLayout.text (AlignedRows.route false 164 0 12 960 5) /\
 linked CallLayout.text (RipBroadcasts.route 5 204 5 factor).
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma literal i : (i<5)%nat ->
 read_word (fun x=>nth (Z.to_nat x) CallLayout.text 0) (factor+8*Z.of_nat i)=Fields.two_d i.
Proof. intros N;destruct i as [|[|[|[|[|i]]]]];[vm_compute;reflexivity..|lia]. Qed.

Definition setup bias:=segment (CallLayout.base bias) CallLayout.text 14.
Definition inputs pt s j i:=read_word (mem s) (pt+960+64*Z.of_nat i+8*Z.of_nat j).
Record ready (root:cpu) e p q:Prop:=Ready {
 regs_after:regs(machine q)=regs(machine p);
 memory_after:mem(machine q)=mem(machine p);
 flags_after:flag(machine q)=flag(machine p);
 coordinates:forall j i,(i<5)%nat -> vectors(machine q) j i=inputs (CallLayout.point_ptr e) (machine p) j i;
 coefficient:forall j i,(i<5)%nat -> vectors(machine q) j (5+i)%nat=Fields.two_d i;
 field_constants:forall j i,(i<4)%nat -> vectors(machine q) j (28+i)%nat=FieldLiterals.constant i
}.

Theorem checked (root:cpu) bias e p : placement e -> loaded root bias e ->
 ip p=CallLayout.base bias+124 -> accounted root (writable e) p -> well_formed(machine p) ->
 regs(machine p) 12%nat=CallLayout.point_ptr e ->
 exists q,setup bias p=Some q /\ ip q=CallLayout.base bias+TableKernels.site Fields.TwoDT /\
 accounted root (writable e) q /\ well_formed(machine q) /\ ready root e p q.
Proof.
 intros P I PC Acc W R12;set (s:=machine p) in *;set (o:=CallLayout.base bias) in *;set (pt:=CallLayout.point_ptr e) in *.
 destruct(mapped_now _ _ _ I _ _ _ Acc builder_in) as [Map Sep].
 destruct(RipBroadcasts.load o _ _ _ _ _ s (LinkedRun.carry p) (proj1 sites)) as [a [A [GA [MA [FA [C _]]]]]].
 destruct(point_fit _ P) as [L H];pose proof(point_alignment _ P) as Align.
 assert (Aligned:(pt+960) mod 64=0).
 { replace (pt+960) with (CallLayout.point_ptr e+15*64) by (unfold pt;ring);now rewrite Z.mod_add by lia. }
 destruct(AlignedRows.loads o _ 5 164 0 12 960 (pt+960) a (LinkedRun.carry p) (proj1(proj2 sites))
  ltac:(now rewrite GA,R12) Aligned ltac:(unfold fits64,pt;change (Z.of_nat 5) with 5;lia))
  as [b [B [GB [MB [FB [Rows Held]]]]]].
 destruct(RipBroadcasts.load o _ _ _ _ _ b (LinkedRun.carry p) (proj2(proj2 sites))) as [t [T [GT [MT [FT [Factor Keep]]]]]].
 change (124+10*Z.of_nat 4) with 164 in A.
 change (AlignedRows.after false 164 0 12 960 5) with 204 in B.
 pose proof(run_append _ _ _ _ _ (run_append _ _ _ _ _ A _ _ _ B) _ _ _ T) as Run.
 destruct(at_segment _ _ p o CallLayout.text 14 124 _ _ Acc PC Map Sep Run (Forall_nil _)) as [Step Paid].
 eexists;split;[exact Step|split;[reflexivity|split;[exact Paid|split;[exact (segment_wf _ _ _ _ _ W Step)|constructor]]]].
 - exact (eq_trans GT (eq_trans GB GA)).
 - exact (eq_trans MT (eq_trans MB MA)).
 - exact (eq_trans FT (eq_trans FB FA)).
 - intros j i N;change (vectors t j i=inputs pt s j i);rewrite Keep by lia;exact (eq_trans (Rows j i N) (f_equal (fun m=>read_word m (pt+960+64*Z.of_nat i+8*Z.of_nat j)) MA)).
 - intros j i N;change (vectors t j (5+i)%nat=Fields.two_d i);rewrite Factor,MB,MA by exact N.
   replace (o+factor+8*Z.of_nat i) with (bias+CallLayout.origin+(factor+8*Z.of_nat i)) by (unfold o,CallLayout.base;ring).
   eapply FieldLiterals.read_literal;[exact Map|exact (proj1(symbols _ _ _ I _ _ builder_in))|
     unfold factor;lia|change (factor+8*Z.of_nat i+8<=2280);unfold factor;lia|apply literal,N].
 - intros j i N;change (vectors t j (28+i)%nat=FieldLiterals.constant i);rewrite Keep,Held,C by lia.
   destruct(mapped_now _ _ _ I _ _ _ Acc helper_in) as [Helper _].
   replace (o+constants+8*Z.of_nat i) with (bias+HelperBytes.address+FieldLiterals.field_offset i) by
      (unfold o,CallLayout.base,constants,FieldLiterals.field_offset;ring).
   eapply FieldLiterals.read_literal;[exact Helper|exact (proj1(symbols _ _ _ I _ _ helper_in))|
    apply FieldLiterals.offsets,N|apply FieldLiterals.offsets,N|apply FieldLiterals.literal_value,N].
Qed.
