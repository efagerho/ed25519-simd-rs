From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Instructions Blocks FlatMemory ByteMemory WordBounds
 MemoryGeometry ScalarRefinement SysV LinkedCalls.
From Double4 Require Double4Spec Double4ABI.
From CachedAdd Require CachedAddSpec CachedAddABI.
Require Import LinkedBytes Callees Schedule Audit Calls.
Import ListNotations. Open Scope Z_scope.

Section Execution.
Variables slide sc pad pt cache : Z.
Variable full : bool.
Variable initial : cpu.
Hypothesis place : placement_ok slide sc pad pt cache.
Hypothesis initial_wf : well_formed initial.
Let top := sc+1320+pad.
Let sp := sc+1296+pad.
Hypothesis rsp : regs initial 4%nat=top.
Hypothesis rdi : regs initial 7%nat=pt.
Hypothesis rsi : regs initial 6%nat=cache.
Hypothesis rdx : regs initial 2%nat=CachedAddABI.flag_word full.
Let caller := read_word(mem initial)top.
Let protected := Calls.protected sc pad pt.
Let outside := fun x=>~writable sc pad pt x.
Definition copies (s:cpu) := set (set (set s 3 (regs s 7%nat)) 12 (regs s 6%nat)) 13 (regs s 2%nat).
Definition spill := push (push (push initial (regs initial 3%nat)) (regs initial 12%nat)) (regs initial 13%nat).
Definition start := copies spill.
Definition slots m :=
 read_word m sp=regs initial 13%nat /\ read_word m (sp+8)=regs initial 12%nat /\
 read_word m (sp+16)=regs initial 3%nat /\ read_word m top=caller.
Record invariant s : Prop := {
 inv_wf : well_formed s;
 inv_sp : regs s 4%nat=sp;
 inv_regs : forall r,In r sysv_saved -> regs s r=regs start r;
 inv_slots : slots(mem s);
 inv_frame : preserved outside (mem initial)(mem s)
}.

Local Ltac reg_simpl := cbn [copies set set_regs push pop returning regs mem put Nat.eqb].
Local Ltac addresses :=
 pose proof(stack_fits _ _ _ _ _ place);pose proof(padding_bounds _ _ _ _ _ place);
 unfold fits64,word64,sp,top in *;lia.
Lemma top_is_sp : top=sp+24. Proof. unfold top,sp;ring. Qed.
Lemma spill_layout :
 regs spill 4%nat=sp /\
 mem spill=store_word(store_word(store_word(mem initial)(sp+16)(regs initial 3%nat))
 (sp+8)(regs initial 12%nat)) sp (regs initial 13%nat).
Proof.
 unfold spill;reg_simpl;rewrite rsp,top_is_sp;
 replace(sp+24-8)with(sp+16)by ring;
 rewrite (word_fits (sp+16)) by addresses;replace(sp+16-8)with(sp+8)by ring;
 rewrite (word_fits (sp+8)) by addresses;replace(sp+8-8)with sp by ring;rewrite word_fits by addresses;auto.
Qed.
Lemma spill_preserved : preserved (fun x=>~(sp<=x<top)) (mem initial)(mem start).
Proof. change (preserved (fun x=>~(sp<=x<top)) (mem initial) (mem spill));rewrite (proj2 spill_layout);
 intros x H;unfold store_word;repeat rewrite write_outside by (unfold sp,top in *;lia);reflexivity.
Qed.
Lemma start_ok : invariant start.
Proof.
 constructor.
 - assert (W:well_formed spill) by (unfold spill;repeat apply push_wf;exact initial_wf).
   unfold start,copies;apply set_wf;[apply set_wf;[apply wf_copy;exact W|apply W]|apply W].
 - exact(proj1 spill_layout).
 - intros;reflexivity.
 - change(slots(mem spill));rewrite (proj2 spill_layout);unfold slots,caller.
   rewrite top_is_sp;repeat split;repeat rewrite read_other_word by (unfold disjoint;lia);
   auto;apply write_read_word;apply initial_wf.
 - intros x H;apply spill_preserved;pose proof(padding_bounds _ _ _ _ _ place);unfold outside,writable,sp,top in *;lia.
Qed.
Lemma spill_point i : (i<160)%nat -> buffer_words(mem start)pt i=buffer_words(mem initial)pt i.
Proof.
 intro I;apply preserved_read with (outside:=fun x=>~(sp<=x<top));[apply spill_preserved|].
 pose proof(point_stack _ _ _ _ _ place);pose proof(padding_bounds _ _ _ _ _ place);intros;unfold disjoint,sp,top in *;cbn [Z.of_nat] in *;lia.
Qed.
Lemma slot_frame m m' : slots m -> preserved protected m m' -> slots m'.
Proof.
 intros S F;unfold slots in *.
 assert(R:forall a,sp<=a<=top ->read_word m' a=read_word m a).
 { intros a A;apply preserved_read with (outside:=protected);[exact F|].
   pose proof(point_stack _ _ _ _ _ place);pose proof(padding_bounds _ _ _ _ _ place);intros k K;
   unfold protected,Calls.protected,sp,top,disjoint in *;cbn [Z.of_nat] in K;lia. }
 repeat rewrite R by (unfold sp,top;lia);exact S.
Qed.
Lemma cache_word s d n i : invariant s -> 0<=d -> d+n<=3520 ->
 0<=8*Z.of_nat i -> 8*Z.of_nat i+8<=n ->
 buffer_words(mem s)(cache+d)i=buffer_words(mem initial)(cache+d)i.
Proof.
 intros Inv D N _ I;apply preserved_read with(outside:=outside);[exact(inv_frame _ Inv)|].
 pose proof(cache_stack _ _ _ _ _ place);pose proof(cache_point _ _ _ _ _ place).
 intros k K;unfold outside,writable,disjoint in *;cbn [Z.of_nat] in K;lia.
Qed.
Lemma invoke_ok k pc s : invariant s -> wrapper_pc<=pc -> pc+5<wrapper_pc+wrapper_size ->
 parameters k s pt cache ->
 exists out,dispatch (slide+double4_pc)(slide+cached_pc) sc pad (slide+target k)
 (push s (slide+(pc+5))) (slide+(pc+5)) out /\ invariant out /\
 operation_spec k (mem s)(mem out) pt cache.
Proof.
 intros Inv L H P;destruct(call_once _ _ _ _ _ place k pc s L H
   (inv_wf _ Inv)(inv_sp _ Inv) P) as [out[R[W[S[G[F Spec]]]]]].
 exists out;split;[exact R|];split;[|exact Spec];constructor;auto.
 - intros;rewrite G by assumption;apply(inv_regs _ Inv);assumption.
 - eapply slot_frame;[apply(inv_slots _ Inv)|exact F].
 - intros x X;rewrite F;[now apply(inv_frame _ Inv)|unfold outside,writable,protected,Calls.protected,sp in *;lia].
Qed.

Lemma set_temp s r v : invariant s -> word64 v -> r<>4%nat -> ~In r sysv_saved ->
 invariant(set s r v).
Proof.
 intros I W SP G;constructor;[apply set_wf;[apply I|exact W]| | |apply I|apply I].
 - unfold set,set_regs;cbn [regs];unfold put;rewrite (proj2(Nat.eqb_neq _ _) SP);apply I.
 - intros i H;unfold set,set_regs;cbn [regs];unfold put;destruct(Nat.eqb_spec r i);
   [subst;contradiction|apply(inv_regs _ I);exact H].
Qed.

Definition point_arg s := set s 7 (regs s 3%nat).
Definition odd_args s := set (set (set (point_arg s) 6 (regs s 12%nat)) 2 0) 1 0.
Definition base_args s := set (set (set (point_arg s) 6 (word(regs s 12%nat+1280))) 2 1) 1 1.
Definition even_args s := set (set (set (point_arg s) 6 (word(regs s 12%nat+2240))) 2 (regs s 13%nat)) 1 0.

Local Ltac temps I :=
 unfold odd_args,base_args,even_args,point_arg;
 repeat first [apply set_temp |exact I|apply mod64_word|apply (proj1(inv_wf _ I))|
 discriminate|solve[unfold sysv_saved;cbn;intuition discriminate]|solve[unfold word64;lia]].

Local Ltac inputs I :=
 unfold odd_args,base_args,even_args,point_arg,parameters;
 reg_simpl;
 repeat rewrite (inv_regs _ I) by (cbn;tauto);
 unfold start,copies,spill;reg_simpl;rewrite ?rdi,?rsi,?rdx;
 repeat rewrite word_fits by (pose proof(cache_fits _ _ _ _ _ place);unfold fits64,word64 in *;lia);
 cbn [CachedAddABI.flag_word CachedAddABI.cache_length];repeat split;try reflexivity;lia.

Definition restored s := pop (pop (pop s 13) 12) 3.
Lemma finish pc s : invariant s ->
 runs (dispatch (slide+double4_pc)(slide+cached_pc) sc pad) slide pc epilogue s caller
  (returning(restored s)) /\ regs(returning(restored s))4%nat=top+8 /\
 (forall r,In r sysv_saved -> regs(returning(restored s))r=regs initial r).
Proof.
 intros I;destruct(inv_slots _ I) as[R13[R12[R3 Ret]]].
 assert(E1:word(sp+8)=sp+8)by(apply word_fits;addresses).
 assert(E2:word(sp+8+8)=sp+16)by(replace(sp+8+8)with(sp+16)by ring;apply word_fits;addresses).
 assert(E3:word(sp+16+8)=top)by(replace(sp+16+8)with top by(unfold sp,top;ring);apply word_fits;addresses).
 unfold epilogue,restored;cbn [runs];reg_simpl;rewrite (inv_sp _ I),E1,E2,E3,Ret;
 repeat split;try reflexivity;try(apply word_fits;addresses).
 intros r G;destruct G as[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reg_simpl;
 rewrite ?(inv_sp _ I),?E1,?E2,?E3,?R13,?R12,?R3;
 try reflexivity;rewrite (inv_regs _ I) by (cbn;tauto);reflexivity.
Qed.

(* A staged operand is read from the entry memory, even after earlier
   calls have overwritten the point and reused the private stack. *)
Lemma staged_add s after f a d : invariant s -> 0<=d -> d+CachedAddABI.cache_length a<=3520 ->
 operation_spec (Plus f a d) (mem s) after pt cache ->
 CachedAddSpec.cached_add_spec f a (buffer_words(mem s)pt)
   (buffer_words(mem initial)(cache+d)) (buffer_words after pt).
Proof.
 intros Inv D N Spec;eapply CachedAddSpec.spec_ext;[intros;reflexivity| |intros;reflexivity|exact Spec].
 intros i I;symmetry;eapply cache_word with (n:=CachedAddABI.cache_length a);
 try eassumption;destruct a;cbn [CachedAddABI.cache_length] in *;lia.
Qed.

Lemma execute :
 Double4Spec.input_bounds(buffer_words(mem initial)pt) ->
 cache_bounds false (buffer_words(mem initial)cache) ->
 cache_bounds true (buffer_words(mem initial)(cache+1280)) ->
 cache_bounds false (buffer_words(mem initial)(cache+2240)) ->
 exists out,
 runs (dispatch (slide+double4_pc)(slide+cached_pc) sc pad)
   slide wrapper_pc program initial caller out /\
 regs out 4%nat=top+8 /\
 (forall r,In r sysv_saved -> regs out r=regs initial r) /\
 preserved outside (mem initial)(mem out) /\ strict(buffer_words(mem out)pt) /\
 has_value(buffer_words(mem out)pt)(result_value full (mem initial) pt cache) /\
 (full=false ->forall i j,(i<5)%nat ->(j<8)%nat ->
 Double4.FieldSpec.cell(buffer_words(mem out)pt)(15+i)%nat j=0).
Proof.
 intros B Odd Base Even.
 assert (98 < wrapper_size) by (vm_compute;reflexivity).
 destruct(invoke_ok Double (wrapper_pc+14) start start_ok ltac:(lia) ltac:(lia)
   (conj rdi I)) as [s1 [R1 [I1 S1]]].
 assert (D:Double4Spec.double4_spec(buffer_words(mem initial)pt)(buffer_words(mem s1)pt)).
 { eapply Double4Spec.spec_ext;[|intros;reflexivity|exact S1];intros;symmetry;now apply spill_point. }
 assert (V:has_value (buffer_words(mem initial)pt) (fun j=>Double4Spec.point_values(buffer_words(mem initial)pt)j)).
 { intros j J c C;reflexivity. }
 destruct(double_result _ _ _ V B D)as[B1 V1].
 assert (O:invariant(odd_args s1)) by (temps I1).
 destruct(invoke_ok (Plus false false 0) (wrapper_pc+35) _ O ltac:(lia) ltac:(lia)
    ltac:(inputs I1))as[s2[R2[I2 S2]]].
 pose proof(staged_add _ _ false false 0 O ltac:(lia) ltac:(cbn;lia) S2)as A2.
 rewrite Z.add_0_r in A2.
 destruct(add_result false false _ _ _ _ (cached_at (mem initial)cache)
   V1 B1 Odd ltac:(intros;reflexivity) A2)as[B2 V2].
 assert (P:invariant(point_arg s2)) by (temps I2).
 destruct(invoke_ok Double (wrapper_pc+43) _ P ltac:(lia) ltac:(lia)
   ltac:(inputs I2))as[s3[R3[I3 S3]]].
 destruct(double_result _ _ _ V2 (strict_loose _ B2) S3)as[B3 V3].
 assert (A:invariant(base_args s3)) by (temps I3).
 destruct(invoke_ok (Plus true true 1280) (wrapper_pc+69) _ A ltac:(lia) ltac:(lia)
   ltac:(inputs I3))as[s4[R4[I4 S4]]].
 pose proof(staged_add _ _ true true 1280 A ltac:(lia) ltac:(cbn;lia) S4)as A4.
 destruct(add_result true true _ _ _ _ (cached_at (mem initial)(cache+1280))
   V3 B3 Base ltac:(intros;reflexivity) A4)as[B4 V4].
 assert (E:invariant(even_args s4)) by (temps I4).
 destruct(invoke_ok (Plus full false 2240) (wrapper_pc+93) _ E ltac:(lia) ltac:(lia)
   ltac:(inputs I4))as[s5[R5[I5 S5]]].
 pose proof(staged_add _ _ full false 2240 E ltac:(lia) ltac:(cbn;lia) S5)as A5.
 destruct(add_result full false _ _ _ _ (cached_at (mem initial)(cache+2240))
   V4 B4 Even ltac:(intros;reflexivity) A5)as[B5 V5].
 destruct(finish (wrapper_pc+98) s5 I5)as[Ret [Stack Saved]].
 exists(returning(restored s5));split.
 - exists s1;split;[exact R1|];exists s2;split;[exact R2|];exists s3;split;[exact R3|];
   exists s4;split;[exact R4|];exists s5;split;[exact R5|exact Ret].
 - exact(conj Stack (conj Saved (conj (inv_frame _ I5) (conj B5 (conj V5 (proj1 A5)))))).
Qed.
End Execution.
