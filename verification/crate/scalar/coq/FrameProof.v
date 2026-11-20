From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory ExecutionProperties WordBounds.
From Ed25519Simd.Scalar Require Import Program ScalarABI ScalarMemory Control.
From Machine Require Import MemoryCoverage ByteExecution.
Import ListNotations. Open Scope Z_scope.
Lemma placement_separates loc size : valid_placement loc size ->separated loc allowed_write mapped.
Proof.
 intros[O[I[S[A[C[P[N[OI[OS[OC Rest]]]]]]]]]]w s W T.
 destruct w as[[r d]|w];[|contradiction].
 unfold allowed_write,vector_in in W;cbn [fst snd]in W;destruct W as[-> [Lo[Hi Al]]].
 destruct s as[s|s].
 - destruct T as[T|T].
   + apply(same_region_vectors loc output 320 320);[unfold vector_in;cbn;auto|exact T].
   + right;destruct s as[r e];unfold vector_in in T;cbn [fst snd]in T;destruct T as[-> [L[H _]]].
     unfold cell_address,address_of,disjoint in *;cbn [fst snd width];lia.
 - unfold mapped in T;subst s;right;unfold caller_slot,cell_address,address_of,disjoint in *;cbn [fst snd width];lia.
Qed.
Lemma permitted_bytes loc es x : writes_only allowed_write es ->writes_at loc es x ->writable_byte loc x.
Proof.
 intros W[e[s[I[E K]]]];apply Forall_forall with(x:=e)in W;[|exact I];rewrite E in W.
 destruct s as[[r d]|a];[|contradiction].
 unfold allowed_write,vector_in in W;cbn [fst snd]in W;destruct W as[-> [L[U _]]].
 unfold inside,cell_address,address_of in K;cbn [width fst snd]in K;unfold writable_byte;lia.
Qed.
Definition write_ok e := match destination e with Some(VectorCell a)=>cell_inb output 320 a |Some(ReturnSlot _)=>false|None=>true end.
Lemma write_ok_sound es : forallb write_ok es=true ->writes_only allowed_write es.
Proof.
 rewrite forallb_forall;unfold writes_only;rewrite Forall_forall;intros H e I;specialize(H e I).
 unfold write_ok in H;destruct(destination e)as[[a|a]|];cbn [allowed_write];[now apply cell_inb_spec|discriminate|exact Logic.I].
Qed.
Lemma caller_protected loc size k : valid_placement loc size ->0<=k<8 ->~writable_byte loc(origin loc stack+k).
Proof. intros[_[_[_[_[_[_[_[_[OS _]]]]]]]]]K;unfold disjoint in OS;unfold writable_byte;lia. Qed.
Lemma trace_safe : forallb write_ok expected_events=true /\check_stack[(caller_slot,Caller)]expected_events=true.
Proof. vm_compute;split;reflexivity. Qed.
Lemma trace_frame size c d last es : record_path 100 scalar_program abi_layout c=Some(last,es) ->
 writes_only allowed_write es ->balanced[(caller_slot,Caller)]es ->
 flat_frame scalar_program size es(c,d)(last,effects scalar_program(data_effects es)d).
Proof.
 intros R W B loc Place; cbn [fst snd].
 split; [intros; eapply permitted_bytes; eassumption|].
 intros before M.
 eapply recorded_frame with (live:=[(caller_slot,Caller)]); try eassumption.
 - eapply placement_separates; exact Place.
 - intros; eapply permitted_bytes; eassumption.
 - intros; eapply caller_protected; eassumption.
 - intros a [<-|[]]; reflexivity.
 - intros a H; contradiction.
Qed.
Lemma output_vector_coverage : forallb(fun i=>existsb(ptr_eq(output,64*Z.of_nat i))
 (written_vectors (expected_path)))(seq 0 5)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma output_trace_covered es : data_effects es=(expected_path) ->
 forall loc k,0<=k<320 ->writes_at loc es(origin loc output+k).
Proof.
 intros E; apply (MemoryCoverage.output_trace_covered output 5 es).
 rewrite E; exact output_vector_coverage.
Qed.
Theorem scalar_frame_correct size initial final :
 valid_scalar_entry initial ->returns scalar_program abi_layout initial final ->
 registers_preserved initial final /\memory_safe scalar_program size initial final /\
 output_initialized scalar_program initial final.
Proof.
 destruct initial as[c d];intros[[incoming Init]_]Returns;cbn [fst]in Init;subst c.
 pose proof(trace_checked incoming)as Check.
 destruct(record_path 100 scalar_program abi_layout(initial_control incoming))as[[last es]|]eqn:R;[|discriminate].
 change(Some es=Some expected_events)in Check;injection Check as Check.
 pose proof trace_safe as[W B];rewrite <-Check in W,B;apply write_ok_sound in W;apply check_stack_sound in B.
 destruct(record_path_sound _ _ _ _ _ _ R)as[P _].
 pose proof(path_returns _ _ _ _ _ _ P d)as Ends.
 pose proof(return_unique _ _ _ _ _ Returns Ends)as ->.
 pose proof(control_checked incoming)as Control;rewrite P in Control;cbn [observe]in Control.
 injection Control as PC SP R3 R5 R12 R13 R14 R15 Ops.
 split.
 - unfold registers_preserved;cbn [fst];apply ext_in_map.
   change(map(gpr last)saved_registers=map(gpr incoming)saved_registers);cbn;congruence.
 - split.
   + exists 100%nat,es;split;[exact R|];split;[exact W|];split;[exact B|];now apply trace_frame.
   + exists 100%nat,es;split;[exact R|];apply output_trace_covered;exact Ops.
Qed.
