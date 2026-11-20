From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks memory.MemoryTrace memory.FlatMemory execution.ExecutionProperties execution.WordBounds memory.Alignment.
From Ed25519Simd.CachedAdd Require Import Program CachedAddABI CachedAddMemory Control.
From Machine Require Import memory.MemoryCoverage memory.ByteExecution.
Import ListNotations. Open Scope Z_scope.
Section Mode.
Variable full affine:bool.
Lemma mapped_vector pad a : mapped affine pad(VectorCell a) -> vector_in scratch 1280 a \/ vector_in point 1280 a \/ vector_in cached(cache_length affine)a.
Proof.
 destruct a as[r n];unfold mapped,vector_ok,access,abi_layout,point_layout,vector_in;cbn [fst snd].
 rewrite andb_true_iff;intros[A P];apply Z.eqb_eq in A.
 pose proof(Z.div_mod n 64 ltac:(lia)).
 destruct(Nat.eqb r scratch)eqn:S.
 - apply Nat.eqb_eq in S;subst;left.
   destruct((0<=?n/64)&&(n/64<?20))eqn:B.
   + apply andb_true_iff in B as[L U];apply Z.leb_le in L;apply Z.ltb_lt in U;intuition lia.
   + destruct(n/64=? -1),(n/64=?20);discriminate.
 - right;destruct(Nat.eqb r point && (0<=?n/64) && (n/64<?20))eqn:B.
   + repeat rewrite andb_true_iff in B;destruct B as[[R L]U];apply Nat.eqb_eq in R;subst.
     apply Z.leb_le in L;apply Z.ltb_lt in U;left;intuition lia.
   + destruct(Nat.eqb r cached && (0<=?n/64) && (n/64<?cache_length affine/64))eqn:C;[|discriminate].
     repeat rewrite andb_true_iff in C;destruct C as[[R L]U];apply Nat.eqb_eq in R;subst.
     apply Z.leb_le in L;apply Z.ltb_lt in U;right;destruct affine;cbn [cache_length] in *;
     [change(n/64<15)in U|change(n/64<20)in U];intuition lia.
Qed.
Lemma placement_separates loc size pad : valid_placement affine loc size pad -> separated loc(allowed_write pad)(mapped affine pad).
Proof.
 intros [[Pad[OP[OA[SB[SA[CB[CP[NC[OS[OC SC]]]]]]]]]] [Cached[CA[CO[CS CC]]]]] w s W S.
 pose proof(padding_range _ Pad)as PB.
 destruct w as[w|w],s as[s|s];cbn [allowed_write] in W.
 - apply mapped_vector in S;destruct W as[O|A];destruct S as[T|[U|V]];
   try(eapply same_region_vectors;eassumption);right;eapply different_regions;try eassumption;unfold disjoint in *;lia.
 - cbn [mapped private_slots] in S.
   destruct S as[[<- | [<- | [<- | []]]]| ->];destruct W as[A|A];right;destruct w as[r d];
   unfold vector_in in A;cbn [fst snd] in A;destruct A as[-> [L[U _]]];
   unfold cell_address,address_of,saved_slot,caller_slot,disjoint in *;cbn [fst snd width] in *;lia.
 - apply mapped_vector in S;cbn [private_slots] in W.
   destruct W as[<- | [<- | [<- | []]]];destruct S as[A|[A|A]];right;destruct s as[r d];
   unfold vector_in in A;cbn [fst snd] in A;destruct A as[-> [L[U _]]];
   unfold cell_address,address_of,saved_slot,caller_slot,disjoint in *;cbn [fst snd width] in *;lia.
 - cbn [mapped private_slots] in S;cbn [private_slots] in W.
   destruct W as[<- | [<- | [<- | []]]];destruct S as[[<- | [<- | [<- | []]]]| ->];
   first[left;reflexivity|right;unfold cell_address,address_of,saved_slot,caller_slot,disjoint;cbn [fst snd width];lia].
Qed.
Definition observe_frame pad(result:control*list event) := let '(c,es):=result in
 (map(Blocks.gpr c)saved_registers,forallb(write_ok pad)es && check_stack[(caller_slot pad,Caller)]es).
Lemma frame_checked incoming pad bp : permitted_padding pad ->word64 bp ->
 option_map(observe_frame pad)(record_path 200 add_cached_program (abi_layout affine)(initial_control incoming pad bp full affine))=
 Some(map(Blocks.gpr(initial_control incoming pad bp full affine))saved_registers,true).
Proof.
 intros Pad BP;destruct full,affine;destruct Pad as[<- | [<- | [<- | [<- | []]]]];
 lazy -[stack_word];
 change (Some([Blocks.gpr incoming 3%nat;Int(stack_word(stack_word bp));
 Blocks.gpr incoming 12%nat;Blocks.gpr incoming 13%nat;Blocks.gpr incoming 14%nat;Blocks.gpr incoming 15%nat],
 if Z.eqb(stack_word bp)(stack_word bp)then true else false)=
 Some([Blocks.gpr incoming 3%nat;Int bp;Blocks.gpr incoming 12%nat;Blocks.gpr incoming 13%nat;
 Blocks.gpr incoming 14%nat;Blocks.gpr incoming 15%nat],true));
 rewrite Z.eqb_refl;unfold stack_word;rewrite Z.mod_mod by lia;rewrite Z.mod_small by exact BP;reflexivity.
Qed.
Lemma trace_frame size pad c d last es :
 permitted_padding pad -> record_path 200 add_cached_program (abi_layout affine) c=Some(last,es) ->
 writes_only(allowed_write pad)es ->balanced[(caller_slot pad,Caller)]es ->
 flat_frame affine add_cached_program size pad es(c,d)(last,effects add_cached_program(data_effects es)d).
Proof.
 intros Pad R W B loc Place; cbn [fst snd].
 split; [intros; eapply permitted_bytes; eassumption|].
 intros before M.
 eapply recorded_frame with (live:=[(caller_slot pad,Caller)]); try eassumption.
 - eapply placement_separates; exact Place.
 - intros; eapply permitted_bytes; eassumption.
 - intros; eapply caller_byte_protected; [exact (proj1 Place)|eassumption].
 - intros a [<-|[]]; now right.
 - intros a H; now left.
Qed.
Lemma output_vector_coverage : forallb(fun i=>existsb(ptr_eq(point,64*Z.of_nat i))
 (written_vectors (expected_path full affine)))(seq 0 20)=true.
Proof. destruct full,affine;vm_compute;reflexivity. Qed.
Lemma output_trace_covered es : data_effects es=(expected_path full affine) ->
 forall loc k,0<=k<1280 ->writes_at loc es(origin loc point+k).
Proof.
 intros E; apply (MemoryCoverage.output_trace_covered point 20 es).
 rewrite E; exact output_vector_coverage.
Qed.
Theorem cached_add_frame_correct size initial pad final :
 valid_cached_add_entry initial pad full affine ->returns add_cached_program (abi_layout affine) initial final ->
 registers_preserved initial final /\ memory_safe affine add_cached_program size pad initial final /\
 output_initialized affine add_cached_program initial final.
Proof.
 destruct initial as[c d];intros[Pad[[incoming[bp[BP Init]]]_]]Returns;cbn [fst] in Init;subst c.
 pose proof(frame_checked incoming pad bp Pad BP)as Check.
 destruct(record_path 200 add_cached_program (abi_layout affine)(initial_control incoming pad bp full affine))as[[last es]|]eqn:R;[|discriminate].
 apply(f_equal(fun result=>match result with Some obs=>fst obs | None=>[] end))in Check as Regs.
 apply(f_equal(fun result=>match result with Some obs=>snd obs | None=>false end))in Check as Safe.
 change(forallb(write_ok pad)es && check_stack[(caller_slot pad,Caller)]es=true)in Safe.
 apply andb_true_iff in Safe as[W B];apply write_ok_sound in W;apply check_stack_sound in B.
 destruct(record_path_sound _ _ _ _ _ _ R)as[P _].
 pose proof(path_returns _ _ _ _ _ _ P d)as Ends.
 pose proof(return_unique _ _ _ _ _ Returns Ends)as ->.
 split;[unfold registers_preserved,SysV.preserves_sysv;cbn [fst];apply ext_in_map;exact Regs|]. split.
 - exists 200%nat,es;split;[exact R|];split;[exact W|];split;[exact B|];now apply trace_frame.
 - exists 200%nat,es;split;[exact R|].
   pose proof(control_path_checked incoming pad bp full affine Pad)as Path;rewrite P in Path.
   cbn [observe_path] in Path;injection Path as _ _ Ops.
   apply output_trace_covered;exact Ops.
Qed.
End Mode.
