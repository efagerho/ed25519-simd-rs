From Coq Require Import ZArith Bool Lia.
From Machine Require Import execution.Blocks execution.LinkedCalls execution.ScalarRefinement execution.KnownRegisters execution.WordBounds
 memory.FlatMemory memory.ByteMemory abi.SysV abi.CallFrame.
From Ed25519Simd Require Import PointFrame PointResults.
From Ed25519Simd.Double4 Require Double4Memory.
From Ed25519Simd.CachedAdd Require CachedAddMemory CachedAddABI.
From Ed25519Simd.Point Require Import Double DoubleBytes Add AddBytes DoublePath AddPath Frame Concrete.
From Ed25519Simd.LadderStep Require Export Modes.
Local Open Scope Z_scope.
Definition layout_at scratch point cache pc ret :=
 Placement (fun r=>match r with 0%nat=>scratch | 1%nat=>point | _=>cache end) pc ret.
Definition call_loc scratch pc s := layout_at scratch (regs s 7%nat) (regs s 6%nat) pc (read_word(mem s)(regs s 4%nat)).
Definition callee_writable scratch s x :=
 regs s 7%nat<=x<regs s 7%nat+1280 \/ scratch-16<=x<regs s 4%nat.
Definition call_post scratch s := sysv_return (callee_writable scratch s) s.
Definition point_words s := buffer_words (mem s)(regs s 7%nat).
Definition dsize := size (Doubling true).
Definition asize := size (Addition PrivateAffine).
Definition doubling_image := image Double.program.
Definition doubling_bytes := DoubleBytes.symbol_bytes.
Definition addition_image := image Add.program.
Definition addition_bytes := AddBytes.symbol_bytes.
Lemma double_binding : doubling_image=doubling_bytes. Proof. apply double_image. Qed.
Lemma add_binding : addition_image=addition_bytes. Proof. apply add_image. Qed.

Definition flag_mode n := if n=?0 then Some false else if n=?1 then Some true else None.
Definition selected dp ap ip (s:cpu) := if ip=?dp then Some (Doubling true)
 else if ip=?ap then Some (Addition PrivateAffine)
 else if ip=?ap+public_add_offset then
   match flag_mode (regs s 2%nat),flag_mode (regs s 1%nat) with
   | Some f,Some a=>Some(Addition(Public f a)) | _,_=>None end
 else None.
Definition dispatch dp ap sc pad ip s ret out :=
 match selected dp ap ip s with None=>False | Some k=>
 let loc:=call_loc sc (match k with Doubling _=>dp|Addition _=>ap end) s in
 callee_returns (body k)(layout_for k)loc(from_cpu k loc pad s)(mem s)ret out end.
Lemma dispatch_unique dp ap sc pad : dp<>ap ->functional(dispatch dp ap sc pad).
Proof. intros _ ip s r u r' u';unfold dispatch;destruct(selected dp ap ip s);[apply callee_unique|contradiction]. Qed.

Lemma concrete_call k sc pc pad s :
 let loc:=call_loc sc pc s in
 well_formed s ->regs s 4%nat=sc+1288+pad ->word64(regs s 4%nat+8) ->
 arguments k loc pad s ->placement_ok k loc pad ->
 exists out,callee_returns (body k)(layout_for k)loc(from_cpu k loc pad s)(mem s)(caller_pc loc)out /\
 call_post sc s out /\ buffers_spec k (point_words s)(buffer_words(mem s)(regs s 6%nat))(buffer_words(mem out)(regs s 7%nat)).
Proof.
 intros loc W SP End Args Place. destruct(concrete_correct k loc pad s Place W Args eq_refl)as[_ [Entry [fin [after [es [_ Result]]]]]].
 destruct Result as [R Stack Saved _ Bytes Math].
 assert(K:known_registers(fst(from_cpu k loc pad s))) by (intros r U;specialize(Entry r);rewrite U in Entry;discriminate).
 destruct(lift_return _ _ _ _ _ _ _ _ _ K R Bytes)as[Run [WF Frame]].
 exists(export_state loc fin after);split;[exact Run|];split;[|exact Math].
 eapply project_sysv_return;[exact Entry|apply W|exact End| | |exact Stack|exact Saved|exact WF|].
 - destruct k as [[]|[f a|]];reflexivity.
 - change(sc+(1288+pad+8)=regs s 4%nat+8);lia.
 - intros x Outside;apply Frame;unfold callee_writable,writable_byte,entry_rsp in *.
   change (~(regs s 7%nat<=x<regs s 7%nat+1280 \/ sc-16<=x<sc+1288+pad));now rewrite <-SP.
Qed.
Lemma mode_double_call dp ap sc pad s :
 well_formed s ->regs s 4%nat=sc+1288+pad ->word64(regs s 4%nat+8) ->
 Double4Memory.valid_placement(call_loc sc dp s)dsize pad ->
 exists out,dispatch dp ap sc pad dp s (caller_pc(call_loc sc dp s))out /\ call_post sc s out /\
 double_spec defer_double (point_words s)(buffer_words(mem out)(regs s 7%nat)).
Proof.
 intros W SP End Place;unfold dispatch,selected;rewrite Z.eqb_refl.
 apply (concrete_call (Doubling true));auto;repeat split;auto.
Qed.
Lemma mode_add_call dp ap sc pad s f a :
 dp<>add_target ap f a ->well_formed s ->regs s 4%nat=sc+1288+pad ->word64(regs s 4%nat+8) ->mode_args f a s ->
 CachedAddMemory.valid_placement a (call_loc sc ap s) asize pad ->
 exists out,dispatch dp ap sc pad (add_target ap f a) s (caller_pc(call_loc sc ap s)) out /\
 call_post sc s out /\ addition_spec (defer_add f a) f a (point_words s)(buffer_words(mem s)(regs s 6%nat))
  (buffer_words(mem out)(regs s 7%nat)).
Proof.
 intros Dist W SP End Modes Place;unfold dispatch,selected;rewrite (proj2 (Z.eqb_neq (add_target ap f a) dp) ltac:(congruence)).
 assert(D:0<public_add_offset) by (vm_compute;reflexivity).
 destruct f,a;cbn [add_target add_offset defer_add defer_double mode_args] in *.
 all: unfold add_target,add_offset;cbn [defer_add defer_double].
 2-4: rewrite (proj2 (Z.eqb_neq (ap+public_add_offset) ap) ltac:(lia)),Z.eqb_refl; destruct Modes as [F A];rewrite F,A;cbn [flag_mode CachedAddABI.flag_word Z.eqb];apply (concrete_call (Addition (Public _ _)));auto;repeat split;auto.
 - rewrite Z.add_0_r,Z.eqb_refl;apply (concrete_call (Addition PrivateAffine));auto;repeat split;auto.
Qed.
