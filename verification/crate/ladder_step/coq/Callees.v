From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.Blocks memory.MemoryTrace memory.FlatMemory memory.ByteMemory
 memory.ByteExecution execution.WordBounds memory.MemoryGeometry execution.ScalarRefinement execution.KnownRegisters abi.SysV execution.LinkedCalls abi.CallFrame.
From Ed25519Simd.Double4 Require Double4Bytes Double4ABI Double4Memory Double4Spec Object.
From Ed25519Simd.CachedAdd Require CachedAddBytes CachedAddABI CachedAddMemory CachedAddSpec Object.
Import ListNotations. Open Scope Z_scope.
Module D := Ed25519Simd.Double4.Double4Bytes.
Module A := Ed25519Simd.CachedAdd.CachedAddBytes.

Notation saved := sysv_saved.
Definition layout_at scratch point cache pc ret :=
 Placement (fun r => match r with 0%nat=>scratch | 1%nat=>point | _=>cache end) pc ret.
Definition call_loc scratch pc s := layout_at scratch (regs s 7%nat) (regs s 6%nat)
 pc (read_word (mem s) (regs s 4%nat)).

(* The dispatch relation has only the two linked symbol entry points. Its
   witnesses contain actual machine executions and their replayed writes. *)
Inductive dispatch dp ap scratch pad : Z -> cpu -> Z -> cpu -> Prop :=
| run_double s ret out :
 let loc := call_loc scratch dp s in
 let entry := D.entry_from_bytes loc pad (regs s) (vectors s) (flag s) (mem s) in
 callee_returns Ed25519Simd.Double4.Program.double4_program Double4ABI.abi_layout loc entry (mem s) ret out ->
 dispatch dp ap scratch pad dp s ret out
| run_add s full affine ret out :
 regs s 2%nat=CachedAddABI.flag_word full -> regs s 1%nat=CachedAddABI.flag_word affine ->
 let loc := call_loc scratch ap s in
 let entry := A.entry_from_bytes full affine loc pad (regs s) (vectors s) (flag s) (mem s) in
 callee_returns Ed25519Simd.CachedAdd.Program.add_cached_program (CachedAddABI.abi_layout affine) loc entry (mem s) ret out ->
 dispatch dp ap scratch pad ap s ret out.

Definition callee_writable scratch s x :=
 regs s 7%nat <= x < regs s 7%nat + 1280 \/ scratch - 16 <= x < regs s 4%nat.
Definition call_post scratch s := sysv_return (callee_writable scratch s) s.

Definition point_words s := buffer_words (mem s) (regs s 7%nat).
Definition dsize := Z.of_nat(length Ed25519Simd.Double4.Object.object_bytes).
Definition asize := Z.of_nat(length Ed25519Simd.CachedAdd.Object.object_bytes).

(* Project the common byte-level ABI facts once for both callees. The
   only routine-specific inputs are the entry adapter and arithmetic spec. *)
Lemma project_return scratch pad pc s entry final after :
 let loc:=call_loc scratch pc s in
 (forall r,scalar_value loc (gpr(fst entry)r)=Some(regs s r)) ->
 (forall r,word64(regs s r)) -> regs s 4%nat=scratch+1288+pad ->
 word64(regs s 4%nat+8) -> pointer_at(fst entry)4 8=Some(0%nat,1288+pad+8) ->
 restores_rsp entry final -> preserves_sysv entry final ->
 well_formed(export_state loc final after) ->
 preserved (fun x=>~(regs s 7%nat<=x<regs s 7%nat+1280 \/
                    scratch-16<=x<scratch+1288+pad)) (mem s) after ->
 call_post scratch s (export_state loc final after).
Proof.
 intros loc Entry Words SP End Addr Stack Saved W Frame.
 eapply project_sysv_return; try eassumption.
 - change (scratch+(1288+pad+8)=regs s 4%nat+8); lia.
 - unfold callee_writable; now rewrite SP.
Qed.

Ltac use_return R Bytes Entry :=
 let K := fresh "EntryKnown" in
 lazymatch type of R with returns _ _ ?entry _ =>
   assert (K:known_registers(fst entry)) by
    (intros r U;specialize(Entry r);rewrite U in Entry;discriminate) end;
 let H := fresh in pose proof(lift_return _ _ _ _ _ _ _ _ _ K R Bytes) as H;
 cbn zeta in H;destruct H as [Hrun [Hwords Hframe]].

Lemma double_call dp ap scratch pad s :
 well_formed s -> regs s 4%nat=scratch+1288+pad ->
 word64(regs s 4%nat+8) ->
 Double4Memory.valid_placement (call_loc scratch dp s) dsize pad ->
 exists out,dispatch dp ap scratch pad dp s (caller_pc(call_loc scratch dp s)) out /\
 call_post scratch s out /\ Double4Spec.double4_spec(point_words s)
 (buffer_words(mem out)(regs s 7%nat)).
Proof.
 intros [W [V B]] SP End Place.
 set(loc:=call_loc scratch dp s).
 assert(E:D.concrete_entry loc dsize pad (regs s)(vectors s)(mem s)) by
  (constructor;try assumption;try reflexivity;change(read_word(mem s)(scratch+1288+pad)=read_word(mem s)(regs s 4%nat));now rewrite SP).
 destruct Ed25519Simd.Double4.Object.assembled_double4_correct as [_ [_ [_ [_ [_ Cert]]]]].
 destruct(Cert loc pad _ _ (flag s) _ E)as[_[fin[after[R[Stack[Pres[_[Bytes Spec]]]]]]]].
 destruct(D.concrete_entry_representable _ _ _ _ _ (flag s) _ E)as[_[_[_ Entry]]].
 use_return R Bytes Entry.
 exists(export_state loc fin after);split;[constructor;exact Hrun|].
 split;[|exact Spec];eapply project_return;try eassumption;reflexivity.
Qed.

Lemma add_call dp ap scratch pad s full affine :
 well_formed s -> regs s 4%nat=scratch+1288+pad ->
 word64(regs s 4%nat+8) ->
 regs s 2%nat=CachedAddABI.flag_word full -> regs s 1%nat=CachedAddABI.flag_word affine ->
 CachedAddMemory.valid_placement affine (call_loc scratch ap s) asize pad ->
 exists out,dispatch dp ap scratch pad ap s (caller_pc(call_loc scratch ap s)) out /\
 call_post scratch s out /\ CachedAddSpec.cached_add_spec full affine (point_words s)
 (buffer_words(mem s)(regs s 6%nat)) (buffer_words(mem out)(regs s 7%nat)).
Proof.
 intros [W [V B]] SP End F M Place.
 set(loc:=call_loc scratch ap s).
 assert(E:A.concrete_entry full affine loc asize pad (regs s)(vectors s)(mem s)) by
  (constructor;try assumption;try reflexivity;change(read_word(mem s)(scratch+1288+pad)=read_word(mem s)(regs s 4%nat));now rewrite SP).
 destruct Ed25519Simd.CachedAdd.Object.assembled_cached_add_correct as [_ [_ [_ [_ [_ Cert]]]]].
 destruct(Cert full affine loc pad _ _ (flag s) _ E)as[_[fin[after[R[Stack[Pres[_[Bytes Spec]]]]]]]].
 destruct(A.concrete_entry_representable full affine _ _ _ _ _ (flag s) _ E)as[_[_[_ Entry]]].
 use_return R Bytes Entry.
 exists(export_state loc fin after);split;[eapply run_add;eassumption|].
 split;[|exact Spec];eapply project_return;try eassumption;reflexivity.
Qed.

Lemma flag_unique f g : CachedAddABI.flag_word f=CachedAddABI.flag_word g -> f=g.
Proof. destruct f,g;cbv [CachedAddABI.flag_word];congruence. Qed.
Lemma dispatch_unique dp ap sc pad : dp<>ap -> functional(dispatch dp ap sc pad).
Proof.
 intros Apart t s i a j b First Second;destruct First;inversion Second;subst;
 try contradiction;try solve [eapply callee_unique;eassumption].
 assert (full=full0) by (apply flag_unique;congruence).
 assert (affine=affine0) by (apply flag_unique;congruence).
 subst;eapply callee_unique;eassumption.
Qed.
