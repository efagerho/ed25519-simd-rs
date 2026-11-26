From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.LinkedCalls execution.LinkedRun execution.WordBounds
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.QwordBlock
 memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Machine Require execution.PredicateBlock execution.MaskedWords execution.MaskTransfer.
From Curve25519 Require Import Radix51 Radix51Digits.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderProduct DecoderKernel NativeScale.
Import ListNotations. Local Open Scope Z_scope.
Module MB:=MaskedWords.
Definition start (first:bool):=if first then 952 else 1030.
Definition compares (first:bool):=if first then 970 else 1048.
Definition stop (first:bool):=if first then 996 else 1072.
Definition conjunction:=map Arithmetic [(10%nat,And 1 2);(11%nat,And 3 4);(10%nat,And 10 11)].
Definition mask1:=MB.Compare MB.EqualQ 1 0 10 (MB.Reg 29).
Definition low k off:=MB.Compare MB.EqualQ k 1 0 (MB.Rip off).
Definition ops (first:bool):=mask1::(if first then [low 3 0xb90;low 4 0xb98] else
 [low 2 0xb88;MB.Union 3 3 2;MB.Union 2 3 4]).
Definition fragment first:=firstn (Z.to_nat(stop first-compares first)) (skipn (Z.to_nat(compares first)) text).
Lemma images first: linked text (route (start first) conjunction) /\
 MB.assemble (compares first) (ops first)=Some(fragment first) /\
 length(fragment first)=Z.to_nat(stop first-compares first).
Proof. destruct first;repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute first bias p bank:=bind (segment (base bias) text 3 p) (fun v=>
 PredicateBlock.execute (base bias) (ops first) v bank).
Definition high h:=Z.land (Z.land (h 1%nat) (h 2%nat)) (Z.land (h 3%nat) (h 4%nat)).
Definition passed j (h:nat->Z) d:=((j<?8)%nat && high_test h d)%bool.
Definition result (first:bool) s (bank out:MaskTransfer.bank):=forall j,
 if first then out 3%nat j=passed j (vectors s j) 1 /\ out 4%nat j=passed j (vectors s j) (-1)
 else out 2%nat j=((j<?16)%nat && (bank 3%nat j || passed j (vectors s j) 0 || bank 4%nat j))%bool /\
   out 4%nat j=bank 4%nat j.

Definition gate origin v bank:=PredicateBlock.update origin v bank 1 mask1.
Definition cmp origin v bank k addr:=PredicateBlock.update origin v bank k (low k addr).
Definition union origin v bank d a b:=PredicateBlock.update origin v bank d (MB.Union d a b).
Definition next (first:bool) origin v bank:=let g:=gate origin v bank in
 if first then cmp origin v (cmp origin v g 3 0xb90) 4 0xb98
 else let test:=cmp origin v g 2 0xb88 in let yes:=union origin v test 3 3 2 in union origin v yes 2 3 4.
Lemma eval (first:bool) origin v bank : PredicateBlock.evaluate origin v bank (ops first)=Some(next first origin v bank).
Proof. destruct first;reflexivity. Qed.

Definition literal off:=if off=?0xb90 then radix-19+1 else if off=?0xb98 then radix-19-1 else radix-19.
Lemma compared origin s v bank :
 (forall j,vectors v j 10%nat=high(vectors s j)) ->
 (forall j,vectors v j 29%nat=radix-1) ->
 (forall j,vectors v j 0%nat=vectors s j 0%nat) ->
 (forall off,In off [0xb90;0xb98;0xb88] -> read_word (mem v) (word(origin+off))=literal off) ->
 forall bank' k addr j, bank' 1%nat j=gate origin v bank 1%nat j -> In addr [0xb90;0xb98;0xb88] ->
 cmp origin v bank' k addr k j=passed j (vectors s j) (literal addr-(radix-19)).
Proof.
 intros H M Zero Lit bank' k addr j G A;unfold cmp,low;rewrite PredicateBlock.compare.
 cbn [MB.holds PredicateBlock.operand Nat.eqb];rewrite Lit by exact A;rewrite Zero;change ((1=?0)%nat) with false.
 cbn [orb];rewrite G;unfold gate,mask1;rewrite PredicateBlock.compare;cbn [MB.holds PredicateBlock.operand Nat.eqb];rewrite H,M.
 unfold passed,high_test,high;replace (radix-19+(literal addr-(radix-19))) with (literal addr) by ring.
 destruct (j<?8)%nat;cbn;repeat match goal with |- context[Z.eqb ?a ?b]=>destruct (a=?b) end;reflexivity.
Qed.

Lemma masks first origin s v bank :
 (forall j,vectors v j 10%nat=high(vectors s j)) -> (forall j,vectors v j 29%nat=radix-1) ->
 (forall j,vectors v j 0%nat=vectors s j 0%nat) ->
 (forall off,In off [0xb90;0xb98;0xb88] -> read_word (mem v) (word(origin+off))=literal off) ->
 result first s bank (next first origin v bank).
Proof.
 intros H M Zero Lit;pose proof(compared _ _ _ bank H M Zero Lit) as C.
 set (g:=gate origin v bank) in *;destruct first;intro j;unfold next;fold g.
 - set (pos:=cmp origin v g 3 0xb90).
   assert (Plus:pos 3%nat j=passed j (vectors s j) 1) by (apply (C g 3%nat 0xb90);[reflexivity|cbn;tauto]).
   split;[unfold cmp;rewrite PredicateBlock.other by discriminate;exact Plus|].
   apply (C pos 4%nat 0xb98);[unfold pos,cmp;apply (f_equal (fun f=>f j)),PredicateBlock.other;discriminate|cbn;tauto].
 - set (primary:=cmp origin v g 2 0xb88);set (both:=union origin v primary 3 3 2).
   assert (ZeroRoot:primary 2%nat j=passed j (vectors s j) 0) by (apply (C g 2%nat 0xb88);[reflexivity|cbn;tauto]).
   assert (Old:forall r,r<>2%nat -> r<>1%nat -> primary r j=bank r j) by
    (intros r N K;unfold primary,cmp,g,gate;rewrite !PredicateBlock.other by assumption;reflexivity).
   split.
   + unfold union;rewrite PredicateBlock.union;unfold both,union;rewrite PredicateBlock.union,PredicateBlock.other by discriminate.
     rewrite ZeroRoot,!Old by discriminate;destruct (j<?16)%nat;reflexivity.
   + unfold union,both;unfold union;rewrite !PredicateBlock.other by discriminate;apply Old;discriminate.
Qed.

Theorem checked first pol bias e p bank : loaded pol bias (mem e) (writable e) ->
 ip p=base bias+start first -> accounted e (writable e) p ->
 (forall j,vectors(machine p) j 29%nat=radix-1) ->
 exists q out, execute first bias p bank=Some(q,out) /\ ip q=base bias+stop first /\
 log q=log p /\ mem(machine q)=mem(machine p) /\ regs(machine q)=regs(machine p) /\
 (forall j r,r<>10%nat -> r<>11%nat -> vectors(machine q) j r=vectors(machine p) j r) /\
 result first (machine p) bank out.
Proof.
 intros Image PC Acc Mask;set (o:=base bias) in *;set (s:=machine p) in *.
 destruct(images first) as [Q [Enc Len]].
 destruct(QwordBlock.execute o _ _ _ s (LinkedRun.carry p) Q) as [v [Run [G [M [F Vec]]]]].
 assert (End:QwordBlock.after (start first) conjunction=compares first) by (destruct first;vm_compute;reflexivity).
 rewrite End in Run;destruct(mapped_now _ _ _ Image _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text 3 _ _ _ Acc PC Map Sep Run (Forall_nil _)) as [A Paid].
 set (mid:=LinkedRun.finish o p (State (Running (compares first)) v (LinkedRun.carry p),[])) in *.
 assert (Start:ip mid=o+compares first) by reflexivity.
 assert (Slice:mapped (mem(machine mid)) (ip mid) (fragment first)).
 { rewrite Start;change (mapped (mem v) (o+compares first) (fragment first));rewrite M.
   replace (compares first) with (Z.of_nat(Z.to_nat(compares first))) at 1 by (destruct first;reflexivity).
   apply MaskTransfer.subimage with (text:=text);[exact Map|rewrite Len;change (length text) with 2984%nat;destruct first;cbn [compares stop];lia|].
   rewrite Len;reflexivity. }
 pose proof(PredicateBlock.mapped_block _ _ _ _ _ _ _ Start Enc Slice (eval first o v bank)) as K.
 assert (Last:word(ip mid+Z.of_nat(length(fragment first)))=o+stop first).
 { rewrite Start,Len,Z2Nat.id by (destruct first;cbn;lia).
   replace (o+compares first+(stop first-compares first)) with (o+stop first) by ring;apply word_fits.
   exact (DecoderProduct.address_fits pol bias e Image DecoderKernel.Carry (stop first) ltac:(change (0<=stop first<2984);destruct first;cbn [stop];lia)). }
 assert (Other:forall j r,r<>10%nat -> r<>11%nat -> vectors v j r=vectors s j r).
 { intros j r A10 A11;rewrite Vec;cbn [conjunction map lane lane_step bits];unfold put;
   repeat rewrite (proj2(Nat.eqb_neq 10 r) ltac:(lia));now rewrite (proj2(Nat.eqb_neq 11 r) ltac:(lia)). }
 do 2 eexists;split;[unfold execute;fold o;rewrite A;exact K|].
 split;[exact Last|split;[apply app_nil_r|split;[exact M|split;[exact G|split;[exact Other|]]]]].
 apply masks.
 - intro j;rewrite Vec;reflexivity.
 - intro j;rewrite Other by discriminate;apply Mask.
 - intro j;apply Other;discriminate.
 - intros addr H;rewrite M;pose proof(proj1(symbols _ _ _ _ Image _ _ (decode_in pol))) as Fit.
   assert (In:In addr [0xb90;0xb98;0xb88]) by exact H.
   change (read_word (mem s) (word(bias+DecoderFrame.origin+addr))=literal addr).
   apply NativeScale.read_literal with (bs:=text);[exact Map|exact Fit| | |];
   cbn [List.In] in In;destruct In as [<-|[<-|[<-|[]]]];vm_compute;discriminate || reflexivity.
Qed.

Lemma words first bias p bank q out :
 well_formed(machine p) -> execute first bias p bank=Some(q,out) -> well_formed(machine q).
Proof.
 intros W;unfold execute;destruct(segment _ _ _ p) as [mid|] eqn:S;[|discriminate].
 intro K;rewrite (PredicateBlock.unchanged _ _ _ _ _ _ K);exact (segment_wf _ _ _ _ _ W S).
Qed.
