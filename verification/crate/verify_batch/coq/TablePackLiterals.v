From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions isa.QwordRegister execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory.
From Machine Require execution.MaskTransfer execution.MaskedResult.
From Ed25519Simd.KeyTable Require Pack.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableEntry TableFrame DecoderFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition offset i:=0x800+64*Z.of_nat i.
Definition words i:=match i with O=>Pack.index0 | S O=>Pack.index8 | _=>Pack.biases end.
Definition code:list line:=[(1168,10%nat,QwordOp(AlignedRip 28 (0x800-1178)));
 (1178,10%nat,QwordOp(AlignedRip 29 (0x840-1188)));(1188,10%nat,QwordOp(AlignedRip 30 (0x880-1198)));(1198,5%nat,Imm32 0 124)].
Definition move:=[MaskedResult.FromGpr 1 0].
Definition bytes:list Z:=[0xc5;0xf8;0x92;0xc8].
Lemma image:linked TableFrame.text code /\ MaskedResult.assemble 1203 move=Some bytes /\
 firstn 4 (skipn 1203 TableFrame.text)=bytes.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma encoded i j : (i<3)%nat -> (j<8)%nat ->
 read_word (fun x=>nth (Z.to_nat x) TableFrame.text 0) (offset i+8*Z.of_nat j)=nth j (words i) 0.
Proof.
 intros N J;destruct i as [|[|[|i]]];try lia;destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];try lia;vm_compute;reflexivity.
Qed.

Definition execute bias p ks:=bind (segment (TableFrame.base bias) TableFrame.text 4 p)
 (fun q=>MaskedResult.execute (TableFrame.base bias) move q ks).
Record result bias e p q ks:Prop:=Result {
 address:ip q=TableFrame.base bias+1207;
 writes:accounted e (writable e) q;
 machine_words:well_formed(machine q);
 registers:regs(machine q)=put (regs(machine p)) 0 124;
 memory_after:mem(machine q)=mem(machine p);
 literals:forall i j,(i<3)%nat -> (j<8)%nat -> vectors(machine q) j (28+i)%nat=nth j (words i) 0;
 prior:forall r j,(r<28)%nat -> vectors(machine q) j r=vectors(machine p) j r;
 enabled:forall j,(j<8)%nat -> ks 1%nat j=Z.testbit Pack.mask (Z.of_nat j)
}.

Theorem checked pol bias e p ks : loaded pol bias (mem e) (writable e) -> TableFrame.base bias mod 64=0 ->
 ip p=TableFrame.base bias+1168 -> accounted e (writable e) p -> well_formed(machine p) ->
 exists q bank,execute bias p ks=Some(q,bank) /\ result bias e p q bank.
Proof.
 intros I Align PC Acc W;set (o:=TableFrame.base bias) in *;set (s:=machine p) in *.
 destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 destruct(proj1(symbols _ _ _ _ I _ _ (TableEntry.image pol))) as [L H];change (0<=o) in L;change (o+2280<=2^64) in H.
 assert (Fit:forall k,0<=k<2280 -> word64(o+k)) by (intros k K;unfold word64;lia).
 assert (Al:forall i,(i<3)%nat -> word(o+offset i) mod 64=0).
 { intros i N;rewrite word_fits by (apply Fit;unfold offset;lia);replace (o+offset i) with (o+(32+Z.of_nat i)*64) by (unfold offset;ring);now rewrite Z.mod_add by lia. }
 set (load:=fun i j=>read_word (mem s) (word(o+offset i)+8*Z.of_nat j)).
 set (v:=set (vector_dest (vector_dest (vector_dest s 28 (load 0%nat)) 29 (load 1%nat)) 30 (load 2%nat)) 0 124).
 assert (Run:run 4 (ScalarBytes.fetch o TableFrame.text) (State(Running 1168) s (LinkedRun.carry p))=
   Some(State(Running 1203) v (LinkedRun.carry p),[])).
 { apply (InstructionRoute.checked _ _ _ (proj1 image));cbn [code follow loc cpu_state cf step qword_op vector_dest option_map mem].
   replace (o+(1168+Z.of_nat 10)+(0x800-1178)) with (o+offset 0) by (unfold offset;ring);
   replace (o+(1178+Z.of_nat 10)+(0x840-1188)) with (o+offset 1) by (unfold offset;ring);
   replace (o+(1188+Z.of_nat 10)+(0x880-1198)) with (o+offset 2) by (unfold offset;ring).
   rewrite (Al 0%nat ltac:(lia)),(Al 1%nat ltac:(lia)),(Al 2%nat ltac:(lia));reflexivity. }
 destruct(at_segment _ _ p o TableFrame.text 4 1168 _ _ Acc PC Map Sep Run (Forall_nil _)) as [Next Paid].
 set (mid:=LinkedRun.finish o p (State(Running 1203) v (LinkedRun.carry p),[])) in *.
 set (bank:=MaskedResult.set_mask ks 1 16 (fun j=>Z.testbit 124 (Z.of_nat j))).
 assert (Slice:mapped (mem v) (ip mid) bytes).
 { change (mapped (mem s) (o+Z.of_nat 1203) bytes);apply MaskTransfer.subimage with (text:=TableFrame.text);[exact Map|
   change (1203+4<=2280)%nat;lia|exact (proj2(proj2 image))]. }
 pose proof(MaskedResult.mapped_block o 1203 move mid ks bytes v bank eq_refl (proj1(proj2 image)) Slice eq_refl) as Mask.
 eexists;exists bank;split;[unfold execute;fold o;rewrite Next;exact Mask|constructor].
 - change (word(o+1203+Z.of_nat 4)=o+1207);replace (o+1203+Z.of_nat 4) with (o+1207) by ring;apply word_fits,Fit;lia.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ W Next).
 - reflexivity.
 - reflexivity.
 - intros i j N J;change (vectors v j (28+i)%nat=nth j (words i) 0).
   assert (Val:load i j=nth j (words i) 0).
   { unfold load;rewrite word_fits by (apply Fit;unfold offset;lia);replace (o+offset i+8*Z.of_nat j) with (o+(offset i+8*Z.of_nat j)) by ring.
     rewrite <-(encoded i j N J);apply DecoderFrame.literal_read;[exact Map|unfold offset;lia|change (offset i+8*Z.of_nat j+8<=2280);unfold offset;lia]. }
   destruct i as [|[|[|i]]];try lia;exact Val.
 - intros r j Small;change (vectors v j r=vectors s j r);unfold v;cbn [set set_regs vector_dest vectors];
   unfold put;repeat match goal with |-context[(?n=?r)%nat]=>rewrite (proj2(Nat.eqb_neq n r) ltac:(lia)) end;reflexivity.
 - intros j J;unfold bank,MaskedResult.set_mask,put;cbn [Nat.eqb];rewrite (proj2(Nat.ltb_lt j 16) ltac:(lia));reflexivity.
Qed.
