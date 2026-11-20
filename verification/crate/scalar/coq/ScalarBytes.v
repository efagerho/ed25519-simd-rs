From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks memory.MemoryTrace memory.FlatMemory execution.WordBounds memory.ByteMemory execution.ExecutionProperties.
From Ed25519Simd.Scalar Require Import ScalarABI ScalarMemory ScalarSpec FrameProof.
From Machine Require Import memory.ByteExecution.
Import ListNotations. Open Scope Z_scope.
Record concrete_entry loc size(regs:nat->Z)(vectors:nat->nat->Z)before : Prop := {
 entry_placement:valid_placement loc size;
 entry_bytes:byte_memory before;
 entry_register_words:forall r,word64(regs r);
 entry_vector_words:forall j r,(j<8)%nat->word64(vectors j r);
 entry_stack_pointer:regs 4%nat=origin loc stack;
 entry_output_pointer:regs 7%nat=origin loc output;
 entry_input_pointer:regs 6%nat=origin loc input;
 entry_return_word:read_word before(origin loc stack)=caller_pc loc
}.
Definition buffer_words := ByteMemory.buffer_words.
Definition entry_from_bytes loc regs vectors flag before : state :=
 (initial_control(Control Caller(fun r=>Int(regs r))flag(fun _=>None)),data_from_bytes loc vectors before).
Definition scalar_value loc v := match v with Int n=>Some n | Ptr a=>Some(address_of loc a) | Unknown=>None end.
Lemma decoded_buffer loc vectors flat region k :
 words_at(memory(data_from_bytes loc vectors flat))region k=buffer_words flat(origin loc region)k.
Proof. apply ByteMemory.decoded_buffer. Qed.
Theorem concrete_entry_representable loc size regs vectors flag before :
 concrete_entry loc size regs vectors before ->
 let initial:=entry_from_bytes loc regs vectors flag before in
 valid_scalar_entry initial /\state_words initial /\
 agrees loc mapped(snd initial)(return_memory(fst initial))before /\
 (forall r,scalar_value loc(gpr(fst initial)r)=Some(regs r)).
Proof.
 intros[Place Bytes Regs Vec SP Out Inp Ret]initial.
 assert(Entry:valid_scalar_entry initial).
 { split;[eexists;reflexivity|now apply data_from_bytes_words]. }
 assert(Words:state_words initial).
 { split.
   - intro r;unfold initial,entry_from_bytes,initial_control;cbn [fst gpr].
     do 8(destruct r as[|r];[cbn [scalar_words];try apply Regs;exact I|]);apply Regs.
   - now apply data_from_bytes_words. }
 split;[exact Entry|];split;[exact Words|];split.
 - apply data_from_bytes_agrees;[exact Bytes|];intros a t Map S.
   change((if ptr_eq a caller_slot then Some Caller else None)=Some t)in S.
   destruct(ptr_eq a caller_slot)eqn:E;[|discriminate];apply ptr_eq_true in E;subst a;inversion S;subst t.
   split.
   + destruct Place as(_&_&_&_&_&Bound&_);exact Bound.
   + change(read_word before(origin loc stack+0)=caller_pc loc);now rewrite Z.add_0_r.
 - intro r;unfold initial,entry_from_bytes,initial_control;cbn [fst gpr].
   destruct r as[|[|[|[|[|[|[|[|r]]]]]]]];
   cbv beta iota zeta delta[scalar_value address_of fst snd];try rewrite Z.add_0_r;try reflexivity;
   f_equal;symmetry;assumption.
Qed.
Definition vector_reads loc := ByteExecution.vector_reads loc mapped.
Definition byte_result p loc :=
 ByteExecution.byte_execution p abi_layout loc mapped (writable_byte loc).

Lemma memory_safe_bytes p size loc initial final before :
 valid_placement loc size ->state_words initial ->byte_memory before ->
 agrees loc mapped(snd initial)(return_memory(fst initial))before ->
 returns p abi_layout initial final ->memory_safe p size initial final ->
 exists after,byte_result p loc initial final before after.
Proof.
 intros Place W Bytes Agree [R End] [fuel [es [Trace [_ [_ Frame]]]]].
 destruct(Frame loc Place)as[_ F];destruct(F before Agree)as[A[Outside[Prefixes Pops]]].
 exists(replay p loc es(snd initial)before).
 eapply recorded_bytes; try eassumption.
 intros pre tail E; exact(proj1(Prefixes _ _ E)).
Qed.
Lemma output_bytes loc d after : vector_reads loc d after ->forall k,(k<40)%nat ->
 buffer_words after(origin loc output)k=words_at(memory d)output k.
Proof.
 intros Reads k K;unfold words_at;eapply read_buffer_vector;[exact Reads|].
 left;unfold vector_in;cbn [fst snd];split;[reflexivity|];split;[lia|];split.
   + pose proof(Nat.div_mod k 8 ltac:(lia));lia.
   + rewrite Z.mul_comm;apply Z.mod_mul;lia.
Qed.
Definition concrete_scalar_contract p size :=
 forall loc regs vectors flag before,concrete_entry loc size regs vectors before ->
 let initial:=entry_from_bytes loc regs vectors flag before in
 exists final after,returns p abi_layout initial final /\stack_restored initial final /\
 registers_preserved initial final /\output_initialized p initial final /\
 byte_result p loc initial final before after /\
 scalar_spec(buffer_words before(origin loc input))(buffer_words after(origin loc output)).
Theorem concrete_contract_from_logical p size :
 (forall initial,valid_scalar_entry initial ->exists final,
 returns p abi_layout initial final /\stack_restored initial final /\
 registers_preserved initial final /\memory_safe p size initial final /\
 output_initialized p initial final /\
 scalar_spec(words_at(memory(snd initial))input)(words_at(memory(snd final))output)) ->
 concrete_scalar_contract p size.
Proof.
 intros Logical loc regs vectors flag before Entry initial.
 destruct(concrete_entry_representable _ _ _ _ flag _ Entry)as[E[W[A _]]].
 destruct(Logical _ E)as[final[R[SP[Regs[Mem[Init Spec]]]]]].
 destruct(memory_safe_bytes _ _ _ _ _ _(entry_placement _ _ _ _ _ Entry)
 W(entry_bytes _ _ _ _ _ Entry)A R Mem)as[after Result].
 exists final,after;split;[exact R|];split;[exact SP|];split;[exact Regs|];split;[exact Init|];split;[exact Result|].
 intros j J;specialize(Spec j J);unfold lane_input,lane_output in *.
 assert(Out:forall i,(i<5)%nat ->buffer_words after(origin loc output)(8*i+j)%nat=
 words_at(memory(snd final))output(8*i+j)%nat).
 { intros;apply(output_bytes loc);[exact(proj1(proj2(proj2 Result)))|lia]. }
 destruct Spec as[Value Bounds];split.
 - transitivity(number B(map(fun i=>words_at(memory(snd final))output(8*i+j)%nat)(seq 0 5))).
   + f_equal;apply map_ext_in;intros i I;apply in_seq in I;apply Out;lia.
   + rewrite Value;f_equal;f_equal;apply map_ext;intro i;apply decoded_buffer.
 - intros i I;rewrite Out by exact I;apply Bounds,I.
Qed.
