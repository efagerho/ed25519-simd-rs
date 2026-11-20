From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory WordBounds ByteMemory ExecutionProperties.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.CachedAdd Require Import CachedAddABI CachedAddMemory CachedAddSpec FrameProof.
From Machine Require Import ByteExecution.
Import ListNotations. Open Scope Z_scope.
Section Mode.
Variable full affine:bool.
Record concrete_entry loc size pad(regs:nat->Z)(vectors:nat->nat->Z)before : Prop := {
 entry_placement:valid_placement affine loc size pad;
 entry_bytes:byte_memory before;
 entry_register_words:forall r,word64(regs r);
 entry_vector_words:forall j r,(j<8)%nat ->word64(vectors j r);
 entry_stack_pointer:regs 4%nat=entry_rsp loc pad;
 entry_point_pointer:regs 7%nat=origin loc point;
 entry_cached_pointer:regs 6%nat=origin loc cached;
 entry_compute_t:regs 2%nat=flag_word full;
 entry_affine:regs 1%nat=flag_word affine;
 entry_return_word:read_word before(entry_rsp loc pad)=caller_pc loc
}.
Definition buffer_words := ByteMemory.buffer_words.
Definition entry_from_bytes loc pad regs vectors flag before : state :=
 (initial_control(Control Caller(fun r=>Int(regs r))flag(fun _=>None))pad(regs 5%nat)full affine,
 data_from_bytes loc vectors before).
Definition scalar_value loc v := match v with Int n=>Some n | Ptr a=>Some(address_of loc a) | Unknown=>None end.
Lemma decoded_buffer loc vectors flat region k :
 words_at(memory(data_from_bytes loc vectors flat))region k=buffer_words flat(origin loc region)k.
Proof. apply ByteMemory.decoded_buffer. Qed.
Theorem concrete_entry_representable loc size pad regs vectors flag before :
 concrete_entry loc size pad regs vectors before ->
 let initial:=entry_from_bytes loc pad regs vectors flag before in
 valid_cached_add_entry initial pad full affine /\ state_words initial /\
 agrees loc(mapped affine pad)(snd initial)(return_memory(fst initial))before /\
 (forall r,scalar_value loc(Blocks.gpr(fst initial)r)=Some(regs r)).
Proof.
 intros[Place Bytes Regs Vec SP Point Cached Full Affine Ret]initial.
 assert(Entry:valid_cached_add_entry initial pad full affine).
 { split;[exact(proj1 Place)|];split;[eexists;exists(regs 5%nat);split;[apply Regs|reflexivity]|now apply data_from_bytes_words]. }
 assert(Words:state_words initial).
 { split.
   - intro r;unfold initial,entry_from_bytes,initial_control;cbn [fst Blocks.gpr].
     do 8(destruct r as[|r];[cbn [scalar_words];try apply Regs;try exact I;
     destruct full,affine;unfold flag_word,word64;lia|]);apply Regs.
   - now apply data_from_bytes_words. }
 split;[exact Entry|];split;[exact Words|];split.
 - apply data_from_bytes_agrees;[exact Bytes|];intros a t Map S.
   change((if ptr_eq a(caller_slot pad)then Some Caller else None)=Some t)in S.
   destruct(ptr_eq a(caller_slot pad))eqn:E;[|discriminate];apply ptr_eq_true in E;subst a;inversion S;subst t.
   split.
   + destruct Place as(_&_&_&_&_&_&Bound&_);exact Bound.
   + change(read_word before(origin loc scratch+(1288+pad))=caller_pc loc).
     replace(origin loc scratch+(1288+pad))with(entry_rsp loc pad)by(unfold entry_rsp;ring);exact Ret.
 - intro r;unfold initial,entry_from_bytes,initial_control;cbn [fst Blocks.gpr].
   destruct r as[|[|[|[|[|[|[|[|r]]]]]]]];
   cbv beta iota zeta delta[scalar_value address_of fst snd];try rewrite Z.add_0_r;try reflexivity.
   + f_equal;symmetry;exact Affine.
   + f_equal;symmetry;exact Full.
   + f_equal;unfold entry_rsp in SP;lia.
   + f_equal;symmetry;exact Cached.
   + f_equal;symmetry;exact Point.
Qed.
Definition vector_reads loc pad := ByteExecution.vector_reads loc (mapped affine pad).
Definition byte_result p loc pad :=
 ByteExecution.byte_execution p (abi_layout affine) loc (mapped affine pad) (writable_byte loc pad).
Lemma memory_safe_bytes p size loc pad initial final before :
 valid_placement affine loc size pad ->state_words initial ->byte_memory before ->
 agrees loc(mapped affine pad)(snd initial)(return_memory(fst initial))before ->
 returns p (abi_layout affine) initial final ->memory_safe affine p size pad initial final ->
 exists after,byte_result p loc pad initial final before after.
Proof.
 intros Place W Bytes Agree [R End] [fuel [es [Trace [_ [_ Frame]]]]].
 destruct(Frame loc Place)as[_ F];destruct(F before Agree)as[A[Outside[Prefixes Pops]]].
 exists(replay p loc es(snd initial)before).
 eapply recorded_bytes; try eassumption.
 intros pre tail E; exact(proj1(Prefixes _ _ E)).
Qed.
Lemma output_bytes loc pad d after : vector_reads loc pad d after ->forall k,(k<160)%nat ->
 buffer_words after(origin loc point)k=words_at(memory d)point k.
Proof.
 intros Reads k K;unfold words_at;eapply read_buffer_vector;[exact Reads|].
 unfold mapped,vector_ok,access,limb_address,abi_layout,point,scratch;cbn [fst snd].
   replace(64*Z.of_nat(k/8))with(Z.of_nat(k/8)*64)by ring.
   rewrite Z.mod_mul,Z.div_mul by lia;cbn [Z.eqb Nat.eqb andb].
   assert(C:((0<=?Z.of_nat(k/8))&&(Z.of_nat(k/8)<?20))=true).
   { apply Bool.andb_true_iff;split;[apply Z.leb_le;lia|apply Z.ltb_lt].
     pose proof(Nat.div_mod k 8 ltac:(lia));lia. }
   rewrite C;reflexivity.
Qed.
Definition concrete_cached_add_contract p size :=
 forall loc pad regs vectors flag before,concrete_entry loc size pad regs vectors before ->
 let initial:=entry_from_bytes loc pad regs vectors flag before in
 Z.land(regs 4%nat-8)(-64)-1280=origin loc scratch /\
 exists final after,returns p (abi_layout affine) initial final /\stack_restored initial final /\
 registers_preserved initial final /\output_initialized affine p initial final /\
 byte_result p loc pad initial final before after /\
 cached_add_spec full affine(buffer_words before(origin loc point))(buffer_words before(origin loc cached))(buffer_words after(origin loc point)).
Theorem concrete_contract_from_logical p size :
 (forall initial pad,valid_cached_add_entry initial pad full affine ->exists final,
 returns p (abi_layout affine) initial final /\ stack_restored initial final /\
 registers_preserved initial final /\memory_safe affine p size pad initial final /\
 output_initialized affine p initial final /\
 cached_add_spec full affine(words_at(memory(snd initial))point)(words_at(memory(snd initial))cached)(words_at(memory(snd final))point)) ->
 concrete_cached_add_contract p size.
Proof.
 intros Logical loc pad regs vectors flag before Entry initial.
 destruct(concrete_entry_representable _ _ _ _ _ flag _ Entry)as[E[W[A _]]].
 split.
 - rewrite(entry_stack_pointer _ _ _ _ _ _ Entry);apply(placement_alignment affine _ size);apply Entry.
 - destruct(Logical _ _ E)as[final[R[SP[Regs[Mem[Init Spec]]]]]].
   destruct(memory_safe_bytes _ _ _ _ _ _ _(entry_placement _ _ _ _ _ _ Entry)
    W(entry_bytes _ _ _ _ _ _ Entry)A R Mem)as[after Result].
   exists final,after;split;[exact R|];split;[exact SP|];split;[exact Regs|];split;[exact Init|];split;[exact Result|].
   eapply spec_ext;[| | |exact Spec].
   + intros k K;symmetry;apply decoded_buffer.
   + intros k K;symmetry;apply decoded_buffer.
   + apply(output_bytes loc pad);exact(proj1(proj2(proj2 Result))).
Qed.
End Mode.
