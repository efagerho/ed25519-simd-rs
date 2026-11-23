From Coq Require Import List Bool ZArith Lia.
From Machine Require Import execution.Blocks execution.ExecutionProperties execution.WordBounds execution.ScalarRefinement execution.LinkedCalls
 memory.MemoryTrace memory.VectorBuffer memory.ByteMemory memory.ByteExecution memory.FlatMemory abi.SysV.
From Ed25519Simd Require Import Wide51 PointFrame.
From Curve25519 Require Import Radix51.
From Ed25519Simd.CachedAdd Require CachedAddABI CachedAddBytes CachedAddSpec.
From Ed25519Simd.Double4 Require Double4Bytes.
From Ed25519Simd.Point Require Import DoublePath AddPath Frame Arithmetic.
Import ListNotations. Local Open Scope Z_scope.

Definition buffers_spec k w t out := match k with
 | Doubling b=>double_spec b w out | Addition m=>add_spec m w t out end.
Definition destination k := match k with Doubling b=>if b then DoubleBytes.private_pc else DoubleBytes.public_pc
 | Addition PrivateAffine=>AddBytes.private_pc | Addition _=>AddBytes.public_pc end.
Definition base_pc k := match k with Doubling _=>DoubleBytes.private_pc | Addition _=>AddBytes.private_pc end.
Definition from_cpu k loc pad s : state :=
 (entry k (Control Caller (fun r=>Int(regs s r)) (flag s) (fun _=>None)) pad (regs s 5%nat),
  data_from_bytes loc (vectors s) (mem s)).
Definition arguments k loc pad (s:cpu) := regs s 4%nat=entry_rsp loc pad /\ regs s 7%nat=origin loc point /\
  match k with Doubling _=>True | Addition m=>regs s 6%nat=origin loc CachedAddABI.cached /\
    match m with Public f a=>regs s 2%nat=CachedAddABI.flag_word f /\ regs s 1%nat=CachedAddABI.flag_word a
               | PrivateAffine=>True end end.
Lemma entry_registers k loc pad s : arguments k loc pad s ->
 forall r,scalar_value loc (gpr(fst(from_cpu k loc pad s))r)=Some(regs s r).
Proof.
 intros [SP [PT Args]] r. destruct k as [b|[f a|]];cbn in Args;
 [|destruct Args as [CA [F A]]|destruct Args as [CA _]];
 destruct r as [|[|[|[|[|[|[|[|r]]]]]]]];
 cbn [from_cpu fst entry double_entry enter add_entry Double4ABI.initial_control CachedAddABI.initial_control
 gpr Instructions.put Nat.eqb scalar_value address_of snd];
 rewrite ?Z.add_0_r,?SP,?PT,?CA,?F,?A;try reflexivity;unfold entry_rsp,address_of;cbn [fst snd];f_equal;lia.
Qed.
Lemma entry_state k loc pad s : well_formed s -> placement_ok k loc pad ->arguments k loc pad s ->
 read_word(mem s)(regs s 4%nat)=caller_pc loc ->
 let i:=from_cpu k loc pad s in state_words i /\ agrees loc(tracked k pad)(snd i)(return_memory(fst i))(mem s).
Proof.
 intros [W [V B]] Place Args Ret i. split.
 - split;[|apply data_from_bytes_words;assumption]. intro r.
   pose proof(entry_registers _ _ _ _ Args r) as E.
   destruct(gpr(fst i)r)as[n|p|]eqn:G;try exact I.
   change (scalar_value loc (gpr(fst i)r)=Some(regs s r)) in E;rewrite G in E;injection E as ->;apply W.
 - apply data_from_bytes_agrees;[exact B|]. intros a t M.
   assert (S:return_memory(fst i)a=(if ptr_eq a(caller_slot pad) then Some Caller else None))
     by (destruct k as [[]|[f aff|]];reflexivity).
   rewrite S.
   destruct(ptr_eq a(caller_slot pad))eqn:E;try discriminate;intros[= <-].
   apply ptr_eq_true in E;subst a. pose proof(place_point _ _ _ Place) as P.
   destruct P as (_&_&_&_&_&_&Bound&_);split;[exact Bound|].
   rewrite (proj1 Args) in Ret. change (read_word (mem s) (origin loc scratch+(1288+pad))=caller_pc loc).
   unfold entry_rsp in Ret;now rewrite Z.add_assoc.
Qed.

Definition agrees_words n (a b:nat->Z) := forall i,(i<n)%nat ->a i=b i.
Lemma math_ext k w t o w' t' o' :
 agrees_words 160 w' w -> agrees_words 160 t' t -> agrees_words 160 o' o ->
 buffers_spec k w t o ->buffers_spec k w' t' o'.
Proof.
 intros W T O; destruct k as [b|m].
 - intros S B j c J C.
   assert (L:loose_xyz w) by (intros h l H L;eapply loose_ext;[|apply (B h l H L)];
     intros i I;unfold cell;apply W;lia).
   destruct(S L j c J C)as[R V];split.
   + unfold bounds_for in *;destruct (_ && _)%bool;intros i I;unfold cell;rewrite O by lia;apply R,I.
   + unfold word_coordinate;rewrite (field_at_ext o' o) by (auto;lia).
     rewrite (point_values_ext w' w) by assumption;exact V.
 - intros [Zero S];split.
   + intros F i j I J;unfold cell;rewrite O by lia;apply Zero;assumption.
   + intros [P K] j c J C.
     assert (B:CachedAddSpec.input_bounds (affine m) w t).
     { split;intros i l I L;unfold cell;
       [rewrite <-W by lia;apply P;assumption|rewrite <-T by (destruct (affine m);lia);apply K;assumption]. }
     destruct(S B j c J C)as[R V];split.
     * unfold bounds_for in *;destruct (_ && _)%bool;intros i I;unfold cell;rewrite O by lia;apply R,I.
     * unfold word_coordinate;rewrite (field_at_ext o' o) by (auto;lia).
       rewrite (point_values_ext w' w) by assumption.
       rewrite (cache_values_ext _ t' t) by (auto;intros;apply T;destruct (affine m);lia);exact V.
Qed.

Definition concrete_contract k := forall loc pad s,
 placement_ok k loc pad -> well_formed s -> arguments k loc pad s ->
 read_word(mem s)(regs s 4%nat)=caller_pc loc ->
 let i:=from_cpu k loc pad s in
 rip(fst i)=At (destination k-base_pc k) /\
 (forall r,scalar_value loc(gpr(fst i)r)=Some(regs s r)) /\
 exists final after es, record_path (fuel k) (body k)(layout_for k)(fst i)=Some(fst final,es) /\
 call_result (body k)(layout_for k)i final (footprint k loc es)
  (byte_execution (body k)(layout_for k)loc (tracked k pad)(writable_byte loc pad)i final(mem s)after)
  (buffers_spec k (buffer_words(mem s)(origin loc point)) (buffer_words(mem s)(origin loc CachedAddABI.cached))
                  (buffer_words after(origin loc point))).
Theorem concrete_correct k : concrete_contract k.
Proof.
 intros loc pad s Place W Args Ret i. split.
 { destruct k as [[]|[f a|]];cbn [destination base_pc];try reflexivity;rewrite Z.sub_diag;reflexivity. }
 split;[apply entry_registers,Args|]. destruct(entry_state _ _ _ _ W Place Args Ret)as[State Agree].
 destruct(point_frame k _ pad (regs s 5%nat) (snd i) loc (mem s) Place (proj1 W _) State (proj2(proj2 W)) Agree)
   as[last[es[R Result]]].
 destruct Result as [Returns SP Saved Access Bytes _]. exists (last,effects (body k) (events k) (snd i)), (replay (body k) loc es (snd i) (mem s)), es;split;[exact R|].
 constructor;[exact Returns|exact SP|exact Saved|exact Access|exact Bytes|].
 eapply math_ext with (w:=words_at(memory(snd i))point) (t:=words_at(memory(snd i))CachedAddABI.cached)
   (o:=output (body k) (events k) (snd i)).
 - intros n N;symmetry;apply decoded_buffer.
 - intros n N;symmetry;apply decoded_buffer.
 - intros n N;destruct k as [b|m];[apply (Double4Bytes.output_bytes loc pad)|apply (CachedAddBytes.output_bytes (affine m) loc pad)];
     [apply (proj1(proj2(proj2 Bytes)))|exact N|apply (proj1(proj2(proj2 Bytes)))|exact N].
 - destruct k;[apply doubling_correct|apply addition_correct];apply State.
Qed.
