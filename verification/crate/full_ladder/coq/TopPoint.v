From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.WordSemantics execution.WordBounds
 memory.FlatMemory memory.ByteMemory memory.MemoryGeometry memory.WriteTrace abi.SysV abi.CallFrame.
From Machine Require execution.StoreHistory.
From Ed25519Simd Require Import Wide51 PointResults.
From Ed25519Simd.LadderStep Require Import Callees.
From Ed25519Simd.LadderStep Require PointTrace Calls.
From Ed25519Simd.FullLadder Require Import LinkedBytes Program Native Audit.
From Ed25519Simd.FullLadder Require TopCall.
Import ListNotations. Local Open Scope Z_scope.
Local Notation Four:=TopCall.Four. Local Notation Affine:=TopCall.Affine. Local Notation Even:=TopCall.Even.

Definition event k:=match k with Four=>DoubleFour | Affine=>Cached true true 20 | Even=>Cached false false 35 end.
Definition kernel k:=match k with Four=>Calls.Double | Affine=>Calls.Plus true true 1280 | Even=>Calls.Plus false false 2240 end.
Definition bytes k:=match k with Four=>doubling_bytes | _=>addition_bytes end.
Definition region pt base x:=pt<=x<pt+1280 \/ base-1360<=x<base.
Definition leaf slide base k:=let pc:=slide+TopCall.target k in let sc:=base-1344 in
 match k with Four=>PointTrace.double pc sc 48 | Affine=>PointTrace.add pc sc 48 true true | Even=>PointTrace.add pc sc 48 false false end.
Definition execute slide base k p:=bind (TopCall.enter slide k p) (leaf slide base k).

Record result slide k pt base p q:Prop:=Result {
 at_next:ip q=slide+entry_pc+TopCall.next k;
 words:well_formed(machine q); stack:regs(machine q) 4%nat=base;
 saved:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 writes:StoreHistory.extends (region pt base) p q;
 point:Calls.operation_spec (kernel k) (mem(machine p)) (mem(machine q)) pt base
}.

Lemma child slide k pt base p call : arena slide pt base -> TopCall.entry slide k pt base p call ->
 mapped (mem(machine call)) (slide+TopCall.target k) (bytes k) ->
 exists q,leaf slide base k call=Some q /\ PointTrace.result (base-1344) call q /\
 Calls.operation_spec (kernel k) (mem(machine call)) (mem(machine q)) pt base.
Proof.
 intros A E M;set (s:=machine call) in *.
 destruct(TopCall.arguments _ _ _ _ _ _ E) as [SP [Pt Args]].
 pose proof(TopCall.ready _ _ _ _ _ _ E) as W;pose proof(TopCall.at_child _ _ _ _ _ _ E) as PC.
 pose proof(TopCall.return_word _ _ _ _ _ _ E) as Ret;fold s in W,SP,Pt,Args,Ret.
 pose proof(LA.cache_fits _ _ _ _ _ (ladder_placement _ _ _ A)) as [BL BH].
 assert (End:word64(regs s 4%nat+8)) by (rewrite SP;unfold word64;lia).
 assert (Stack:regs s 4%nat=base-1344+1288+48) by lia.
 assert (Back:read_word (mem s) (base-8)=slide+continuation (event k)).
 { rewrite Ret;destruct k;unfold continuation;cbn [event return_offset TopCall.next setup_length defer_double];ring. }
 destruct k;cbn [bytes TopCall.target] in M,PC.
 - rewrite <-double_binding in M.
   destruct(PointTrace.double_checked _ _ _ _ PC M W Stack End (direct_double_layout _ _ _ _ A Pt SP Back))
     as [q [Run [F Spec]]];exists q;split;[exact Run|split;[exact F|]].
   unfold point_words in Spec;fold s in Spec;rewrite Pt in Spec;exact Spec.
 - destruct Args as [Ptr [F G]];rewrite <-add_binding in M.
   destruct(PointTrace.add_checked _ _ _ true true call PC M W Stack End F G
      (direct_add_layout _ _ _ _ true true 20 A Pt SP Ptr Back ltac:(cbv;discriminate))) as [q [Run [R Spec]]].
   exists q;split;[exact Run|split;[exact R|]];unfold point_words in Spec;fold s in Spec;rewrite Pt,Ptr in Spec;exact Spec.
 - destruct Args as [Ptr [F G]];rewrite <-add_binding in M.
   destruct(PointTrace.add_checked _ _ _ false false call PC M W Stack End F G
      (direct_add_layout _ _ _ _ false false 35 A Pt SP Ptr Back ltac:(cbv;discriminate))) as [q [Run [R Spec]]].
   exists q;split;[exact Run|split;[exact R|]];unfold point_words in Spec;fold s in Spec;rewrite Pt,Ptr in Spec;exact Spec.
Qed.

Theorem checked slide k s p : let pt:=regs s 7%nat in let base:=base_of s in
 placement slide s -> ip p=slide+entry_pc+TopCall.start k -> well_formed(machine p) ->
 regs(machine p) 4%nat=base -> regs(machine p) 3%nat=pt ->
 mapped (mem(machine p)) (slide+entry_pc) symbol_bytes ->
 mapped (mem(machine p)) (slide+TopCall.target k) (bytes k) ->
 exists q,execute slide base k p=Some q /\ result slide k pt base p q.
Proof.
 intros pt base P PC W SP BX Map Code;pose proof(child_layout _ _ P) as A;fold pt base in A.
 pose proof(ladder_placement _ _ _ A) as Layout;destruct Layout as [Pad SA PA CA SF PF CF PS CS CP Images].
 destruct(loaded_images _ _ P _ _ (or_introl eq_refl)) as [Text [TextP TextS]].
 assert (Slot:disjoint (slide+entry_pc) (Z.of_nat(length symbol_bytes)) (base-8) 8).
 { unfold base,base_of,staging,pad_of,disjoint in *;pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));lia. }
 assert (Member:In (TopCall.target k,Z.of_nat(length(bytes k))) images).
 { destruct k;[do 3 right;left|do 4 right;left|do 4 right;left];reflexivity. }
 destruct(loaded_images _ _ P _ _ Member) as [Fit [CodeP CodeS]].
 assert (Size:0<Z.of_nat(length(bytes k))) by (destruct k;vm_compute;reflexivity).
 assert (Inside:0<=TopCall.next k<Z.of_nat(length symbol_bytes)) by (destruct k;vm_compute;split;discriminate || reflexivity).
 destruct(TopCall.checked slide k pt base p PC W SP BX ltac:(unfold fits64 in *;lia) (proj2 CF)
   ltac:(unfold fits64,word64 in *;lia) ltac:(unfold fits64,word64 in *;lia) Map Slot) as [call [Call E]].
 pose proof(TopCall.pushed _ _ _ _ _ _ E) as Push.
 assert (LeafMap:mapped (mem(machine call)) (slide+TopCall.target k) (bytes k)).
 { intros i I;rewrite Push;unfold store_word;rewrite write_outside;[apply Code,I|].
   unfold base,base_of,staging,pad_of,disjoint in *;pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));lia. }
 destruct(child _ _ _ _ _ _ A E LeafMap) as [q [Run [F Value]]].
 destruct(TopCall.arguments _ _ _ _ _ _ E) as [S [D _]].
 destruct(PointTrace.frame _ _ _ F) as [WF [RS [G Preserve]]].
 destruct(PointTrace.writes _ _ _ F) as [ws [Log [Safe Replay]]].
 exists q;split;[unfold execute;rewrite Call;exact Run|constructor].
 - rewrite (PointTrace.back _ _ _ F),S;apply (TopCall.return_word _ _ _ _ _ _ E).
 - exact WF.
 - lia.
 - intros r R;rewrite G by exact R;apply (TopCall.saved _ _ _ _ _ _ E),R.
 - exists (TopCall.push_store slide k base::ws);split;[rewrite Log,(TopCall.stores _ _ _ _ _ _ E),<-app_assoc;reflexivity|split].
   + constructor;[intros x X;right;change (base-8<=x<base-8+8) in X;lia|].
     eapply Forall_impl;[|exact Safe];intros w H x X;specialize(H x X);unfold callee_writable in H;rewrite S,D in H;unfold region;lia.
   + intro x;rewrite Replay,Push;reflexivity.
 - assert (Point:forall i,(i<160)%nat -> buffer_words (mem(machine p)) pt i=buffer_words (mem(machine call)) pt i).
   { intros i I;rewrite Push;symmetry;apply read_store_away;unfold disjoint in *;lia. }
   assert (Cache:forall d i,0<=d -> d+8*Z.of_nat i+8<=3520 ->
     buffer_words (mem(machine p)) (base+d) i=buffer_words (mem(machine call)) (base+d) i).
   { intros;rewrite Push;symmetry;apply read_store_away;unfold disjoint;lia. }
   destruct k.
   + eapply double_spec_ext;unfold agrees_words;[exact Point|intros;reflexivity|exact Value].
   + eapply addition_spec_ext;unfold agrees_words;[exact Point|intros;apply Cache;lia|intros;reflexivity|exact Value].
   + eapply addition_spec_ext;unfold agrees_words;[exact Point|intros;apply Cache;lia|intros;reflexivity|exact Value].
Qed.
