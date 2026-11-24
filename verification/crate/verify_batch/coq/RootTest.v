From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.LocatedReturn memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Pow2 Require Pow2Spec Pow2Memory.
From Ed25519Simd.Decode Require Kernels Power.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode KeySquare NativeScale SetupValues.
From Ed25519Simd.VerifyBatch Require DecoderPower PowerInputs PowerWrites DecoderResume DecoderFinish FinishSquare FinishProduct NativeWords DecoderFrame DecoderProduct.
Local Open Scope Z_scope.
Local Opaque DecoderProduct.kernel.

Lemma square_verified : Kernels.verified DecoderProduct.kernel Kernels.Square=true.
Proof. vm_compute;reflexivity. Qed.
Lemma result x v exponent_value input :
 Radix51.squared x -> split_field v -> represents (limbs x) exponent_value -> represents (limbs v) input ->
 let q:=FinishProduct.candidate x v in
 field_bound (fun _=>radix+2^16) q /\ 2<=q 0%nat /\ represents (limbs q) (exponent_value*exponent_value*input).
Proof.
 intros X V RX RV;set (sq:=Power.apply_kernel DecoderProduct.kernel Kernels.Square x x).
 destruct(Power.apply_ok _ Kernels.Square _ _ square_verified X X) as [S [SS _]].
 destruct(Power.apply_ok _ Kernels.Multiply sq v (proj1 DecoderProduct.multiplication) (squared_split _ S) V) as [B [M L]].
 split;[exact B|split;[apply L;reflexivity|]];eapply ctrans;[exact M|apply ctimes;[eapply ctrans;[exact SS|apply ctimes];exact RX|exact RV]].
Qed.

Definition math e q:=forall j,(j<8)%nat ->
 let v:=vectors(machine q) j in let y:=original_encoding false e j mod 2^255 in
 let uv:=PowerInputs.uv y in let power:=uv^Pow2Spec.exponent in
 field_bound (fun _=>radix+2^16) v /\ 2<=v 0%nat /\ represents (limbs v) (power*power*uv).

Lemma from_bytes pol bias e t returned start q :
 placement e -> DecoderPower.post pol bias e t -> PowerInputs.inputs e t -> PowerWrites.powers pol e returned ->
 preserved (fun x=>~Pow2Memory.writable_byte (DecoderPower.locations pol bias e) x)
    (mem(machine(DecoderPower.exponent_entry t))) (mem(machine returned)) ->
 preserved (fun x=>~span (link_slot pol e) 8 x) (mem(machine returned)) (mem(machine start)) ->
 FinishProduct.post false pol bias e start q -> math e q.
Proof.
 intros P D Inputs Powers After Enter [_ [_ [_ [_ [_ [_ Out]]]]]] j J.
 set (st:=link_slot pol e) in *;set (w:=DecoderPower.exponent_entry t) in *.
 set (uv:=PowerInputs.uv(original_encoding false e j mod 2^255)).
 set (x:=FinishSquare.operand false pol e (machine start) j);set (v:=row (machine start) (point e false+960) j).
 set (out:=buffer_words (mem(machine returned)) (st+8));set (input:=PowerInputs.argument e (machine w) false).
 destruct(Powers false j J) as [B E];fold st out uv in B,E.
 pose proof(PowerInputs.certified _ _ _ _ D Inputs false j J) as [V Rep];fold w input uv in V,Rep.
 assert (X:forall i,(i<5)%nat -> x i=cell out i j).
 { intros i I;unfold out;rewrite PowerInputs.limb_word;unfold x,FinishSquare.operand;cbn [DecoderFinish.power_offset];rewrite Z.add_0_r;fold st.
   apply (keep_row _ _ (st+8) _ Enter);[unfold span;lia|exact J|exact I]. }
 assert (Y:forall i,(i<5)%nat -> v i=cell input i j).
 { intros i I;unfold v,input,PowerInputs.argument;rewrite PowerInputs.limb_word.
   apply keep_row with (protect:=span (point e false) 1280);[|unfold span;lia|exact J|exact I].
   intros a A;pose proof(depth pol e) as Depth;fold st in Depth;destruct(scratch_stack _ P) as [Dis|Dis];
   unfold span,disjoint,point,point_offset in *;rewrite Enter by (unfold span;lia);apply After;
   change (~(st+8<=a<st+8+640 \/ st-1928+1928-1936<=a<st-1928+1928-8));lia. }
 assert (InX:Radix51.squared x).
 { intros i I;rewrite X by exact I;specialize(B i I);change (0<=cell out i j<=Pow2Spec.public_bound i) in B.
   split;[exact (proj1 B)|eapply Z.le_trans;[exact (proj2 B)|]].
   destruct i as [|[|[|[|[|i]]]]];try lia;vm_compute;discriminate || reflexivity. }
 assert (InY:split_field v) by (intros i I;rewrite Y by exact I;specialize(V i I);lia).
 assert (RX:represents (limbs x) (uv^Pow2Spec.exponent)).
 { assert (F:limbs x=field_at out 0 j) by (apply limbs_ext,X).
   change (field_at out 0 j mod prime=uv^Pow2Spec.exponent mod prime) in E.
   rewrite F;eapply ctrans with (y:=field_at out 0 j mod prime);[apply csym,cut_p|];rewrite E;apply cut_p. }
 assert (RY:represents (limbs v) uv) by (erewrite limbs_ext;[exact Rep|exact Y]).
 destruct(result x v (uv^Pow2Spec.exponent) uv InX InY RX RY) as [Bounds [Low Value]].
 split;[intros i I;rewrite Out by assumption;apply Bounds,I|split;[rewrite Out by lia;exact Low|]].
 erewrite limbs_ext;[exact Value|intros i I;apply Out;assumption].
Qed.

Record trace:=Trace { power:PowerWrites.checkpoints; finish_entry:cursor; at_test:cursor }.
Definition observe pol bias e p bank:=bind (PowerWrites.observe pol bias e p bank) (fun r=>
 bind (DecoderFinish.enter bias (resumed(PowerWrites.after_power r))) (fun begin=>
 option_map (Trace r begin) (FinishProduct.finish bias begin))).
Record post pol bias e t : Prop:=Post {
 power_result:PowerWrites.post pol bias e (power t);
 finish_arguments:DecoderFinish.entry false pol bias e (finish_entry t);
 root_product:FinishProduct.post false pol bias e (finish_entry t) (at_test t);
 root_test:math e (at_test t);
 signature_signs:forall j,(j<8)%nat -> Z.testbit (regs(machine(finish_entry t)) 14%nat) (Z.of_nat j)=Z.testbit (original_encoding true e j) 255;
 setup_fields_live:forall sig,fields sig e
   (SetupTail.after_square(PowerInputs.half (PowerWrites.before_power(power t)) sig)) (at_test t)
}.

Theorem from_decoder pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 exists t,observe pol bias e p bank=Some t /\ post pol bias e t.
Proof.
 intros P I Al E W;destruct(PowerWrites.from_decoder _ _ _ _ bank P I Al E W) as [r [Run Out]].
 assert (Link:DecoderPower.observe bias p bank=Some(PowerWrites.before_power r)).
 { unfold PowerWrites.observe in Run;destruct(DecoderPower.observe bias p bank) as [args|] eqn:A;[|discriminate].
   cbn [bind] in Run;destruct(PowerWrites.execute _ _ _ _) as [last|];[|discriminate];injection Run as <-;reflexivity. }
 destruct Out as [D [R Powers]].
 destruct(DecoderResume.after_return _ _ _ _ _ P (proj1(proj2 D)) (NativeWords.pow2_entry_words _ _ _ _ W Link) R) as [Ready After].
 destruct(DecoderFinish.from_power _ _ _ _ P I Ready) as [a [Start [Arguments [Enter Signs]]]].
 destruct(FinishProduct.from_entry false _ _ _ _ P I Arguments) as [q [Body Post]].
 exists (Trace r a q);split;[unfold observe;rewrite Run;cbn [bind];rewrite Start;cbn [bind];now rewrite Body|].
 pose proof(PowerInputs.from_decoder _ _ _ _ _ _ P I Al E W Link) as Inputs.
 constructor;[exact (conj D (conj R Powers))|exact Arguments|exact Post| |exact Signs|].
 - eapply from_bytes;[exact P|exact D|exact Inputs|exact Powers|exact After|exact Enter|exact Post].
 - intro sig;destruct(Inputs sig) as [Fields Keep].
   set (s:=machine(SetupTail.in_decoder(PowerInputs.half (PowerWrites.before_power r) sig))).
   assert (Stayed:preserved (PowerInputs.point_bytes e sig) (mem s) (mem(machine q))).
   { destruct Post as [_ [_ [_ [_ [Held _]]]]];intros x X;pose proof(depth pol e);
     assert (Range:scratch e<=x<scratch e+25344) by (unfold PowerInputs.point_bytes,span,point,point_offset in X;destruct sig;lia).
     destruct(scratch_stack _ P) as [Sep|Sep];unfold disjoint in *;
     rewrite Held,Enter,After,Keep;try reflexivity;try exact X;try (unfold span;lia);
     change (~(link_slot pol e+8<=x<link_slot pol e+8+640 \/
       link_slot pol e-1928+1928-1936<=x<link_slot pol e-1928+1928-8));lia. }
   assert (Same:forall off j i,0<=off<=960 -> (j<8)%nat -> (i<5)%nat ->
     row (machine q) (point e sig+off) j i=row s (point e sig+off) j i).
   { intros off j i O;apply keep_row with (protect:=PowerInputs.point_bytes e sig);[exact Stayed|unfold PowerInputs.point_bytes,span;lia]. }
   intros j i J K;cbn [at_test power];destruct(Fields j i J K) as [U [V UV]];fold s in U,V,UV.
   split;[replace (point e sig) with (point e sig+0) at 1 by ring;rewrite Same by lia;now rewrite Z.add_0_r|
    split;rewrite Same by lia;assumption].
Qed.

Lemma accounted_at_test pol bias e t : post pol bias e t -> accounted e (writable e) (at_test t).
Proof. intro H;exact (proj1(proj2(root_product _ _ _ _ H))). Qed.
