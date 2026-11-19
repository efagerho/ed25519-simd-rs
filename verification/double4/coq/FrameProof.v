From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory ExecutionProperties WordBounds Alignment.
Require Import Program Double4ABI Double4Memory Round Logical.
Import ListNotations. Open Scope Z_scope.
Lemma padding_range pad : permitted_padding pad -> 0<=pad<=48.
Proof. intros[<- | [<- | [<- | [<- | []]]]];lia. Qed.
Lemma mapped_vector pad a : mapped pad(VectorCell a) -> vector_in scratch 1280 a \/ vector_in point 1280 a.
Proof.
 destruct a as[r n];unfold mapped,vector_ok,access,abi_layout,vector_in;cbn [fst snd].
 rewrite andb_true_iff;intros[A P];apply Z.eqb_eq in A.
 pose proof(Z.div_mod n 64 ltac:(lia)).
 destruct(Nat.eqb r scratch)eqn:S.
 - apply Nat.eqb_eq in S;subst;left.
   destruct((0<=?n/64)&&(n/64<?20))eqn:B.
   + apply andb_true_iff in B as[L U];apply Z.leb_le in L;apply Z.ltb_lt in U;intuition lia.
   + destruct(n/64=? -1),(n/64=?20);discriminate.
 - destruct(Nat.eqb r point && (0<=?n/64) && (n/64<?20))eqn:B;[|discriminate].
   repeat rewrite andb_true_iff in B;destruct B as[[R L]U];apply Nat.eqb_eq in R;subst.
   apply Z.leb_le in L;apply Z.ltb_lt in U;right;intuition lia.
Qed.
Lemma same_region_vectors loc r n q a b : vector_in r n a -> vector_in r q b ->
 VectorCell a=VectorCell b \/ disjoint(cell_address loc(VectorCell a))64(cell_address loc(VectorCell b))64.
Proof.
 destruct a as[ra x],b as[rb y];unfold vector_in,cell_address,address_of,disjoint;cbn [fst snd].
 intros[->[_[_ A]]][->[_[_ B]]];destruct(Z.eq_dec x y);[subst;auto|right].
 pose proof(Z.div_mod x 64 ltac:(lia));pose proof(Z.div_mod y 64 ltac:(lia));lia.
Qed.
Lemma different_regions loc r n q m a b : vector_in r n a -> vector_in q m b ->
 disjoint(origin loc r)n(origin loc q)m -> disjoint(cell_address loc(VectorCell a))64(cell_address loc(VectorCell b))64.
Proof. destruct a,b;unfold vector_in,cell_address,address_of,disjoint;cbn [fst snd];intros[->[? [? _]]][->[? [? _]]];lia. Qed.
Lemma placement_separates loc size pad : valid_placement loc size pad -> separated loc(allowed_write pad)(mapped pad).
Proof.
 intros[Pad[_[_[_[_[_[_[_[OS _]]]]]]]]] w s W S.
 pose proof(padding_range _ Pad)as PB.
 destruct w as[w|w],s as[s|s];cbn [allowed_write] in W.
 - apply mapped_vector in S;destruct W as[O|A];destruct S as[T|U];
   try(eapply same_region_vectors;eassumption);right;eapply different_regions;try eassumption;unfold disjoint in *;lia.
 - cbn [mapped private_slots] in S.
   destruct S as[[<- | [<- | [<- | []]]]| ->];destruct W as[A|A];right;destruct w as[r d];
   unfold vector_in in A;cbn [fst snd] in A;destruct A as[-> [L[U _]]];
   unfold cell_address,address_of,saved_slot,caller_slot,disjoint in *;cbn [fst snd width] in *;lia.
 - apply mapped_vector in S;cbn [private_slots] in W.
   destruct W as[<- | [<- | [<- | []]]];destruct S as[A|A];right;destruct s as[r d];
   unfold vector_in in A;cbn [fst snd] in A;destruct A as[-> [L[U _]]];
   unfold cell_address,address_of,saved_slot,caller_slot,disjoint in *;cbn [fst snd width] in *;lia.
 - cbn [mapped private_slots] in S;cbn [private_slots] in W.
   destruct W as[<- | [<- | [<- | []]]];destruct S as[[<- | [<- | [<- | []]]]| ->];
   first[left;reflexivity|right;unfold cell_address,address_of,saved_slot,caller_slot,disjoint;cbn [fst snd width];lia].
Qed.
Lemma permitted_bytes loc pad es x : permitted_padding pad -> writes_only(allowed_write pad)es ->
 writes_at loc es x -> writable_byte loc pad x.
Proof.
 intros Pad W[e[s[I[E K]]]];pose proof(padding_range _ Pad)as PB.
 apply Forall_forall with(x:=e)in W;[|exact I];rewrite E in W;destruct s as[[r d]|a].
 - destruct W as[A|A];unfold vector_in in A;cbn [fst snd] in A;destruct A as[-> [L[U _]]];
   unfold inside,cell_address,address_of in K;cbn [width fst snd] in K;unfold writable_byte,entry_rsp;lia.
 - cbn [allowed_write private_slots] in W;destruct W as[<- | [<- | [<- | []]]];
   unfold inside,cell_address,address_of,saved_slot in K;cbn [width fst snd] in K;unfold writable_byte,entry_rsp;lia.
Qed.
Definition cell_inb r n(a:pointer) := Nat.eqb(fst a)r && (0<=?snd a) && (snd a+64<=?n) && (snd a mod 64=?0).
Lemma cell_inb_spec r n a : cell_inb r n a=true <-> vector_in r n a.
Proof. unfold cell_inb,vector_in;rewrite !andb_true_iff,Nat.eqb_eq,!Z.leb_le,Z.eqb_eq;tauto. Qed.
Definition write_ok pad e := match destination e with
 | Some(VectorCell a)=>cell_inb point 1280 a || cell_inb scratch 1280 a
 | Some(ReturnSlot a)=>existsb(ptr_eq a)(private_slots pad) | None=>true end.
Lemma write_ok_sound pad es : forallb(write_ok pad)es=true -> writes_only(allowed_write pad)es.
Proof.
 rewrite forallb_forall;unfold writes_only;rewrite Forall_forall;intros H e I;specialize(H e I).
 unfold write_ok in H;destruct(destination e)as[[a|a]|];cbn [allowed_write];[| |exact Logic.I].
 - rewrite orb_true_iff,!cell_inb_spec in H;exact H.
 - apply existsb_exists in H as[b[B E]];apply ptr_eq_true in E;now subst.
Qed.
Lemma caller_byte_protected loc size pad k : valid_placement loc size pad ->0<=k<8 ->
 ~writable_byte loc pad(entry_rsp loc pad+k).
Proof. intros[Pad[_[_[_[_[_[_[_[OS _]]]]]]]]]K;pose proof(padding_range _ Pad);unfold disjoint in OS;unfold writable_byte,entry_rsp in *;lia. Qed.
Lemma stack_limit loc pad x : permitted_padding pad -> origin loc scratch-16<=x<entry_rsp loc pad ->
 entry_rsp loc pad-1352<=x<entry_rsp loc pad.
Proof. intros P R;pose proof(padding_range _ P);unfold entry_rsp in *;lia. Qed.
Lemma placement_alignment loc size pad : valid_placement loc size pad ->
 Z.land(entry_rsp loc pad-8)(-64)-1280=origin loc scratch.
Proof.
 intros[Pad[_[_[_[Aligned _]]]]].
 unfold entry_rsp;replace(origin loc scratch+1288+pad-8)with(origin loc scratch+(1280+pad))by ring.
 rewrite aligned_region_and by exact Aligned.
 destruct Pad as[<- | [<- | [<- | [<- | []]]]];change(origin loc scratch+1280-1280=origin loc scratch);ring.
Qed.
Definition observe_frame pad(result:control*list event) := let '(c,es):=result in
 (map(Blocks.gpr c)saved_registers,forallb(write_ok pad)es && check_stack[(caller_slot pad,Caller)]es).
Lemma frame_checked incoming pad bp : permitted_padding pad ->word64 bp ->
 option_map(observe_frame pad)(record_path 200 double4_program abi_layout(initial_control incoming pad bp))=
 Some(map(Blocks.gpr(initial_control incoming pad bp))saved_registers,true).
Proof.
 intros Pad BP;destruct Pad as[<- | [<- | [<- | [<- | []]]]];
 lazy -[stack_word];
 change (Some([Blocks.gpr incoming 3%nat;Int(stack_word(stack_word bp));
 Blocks.gpr incoming 12%nat;Blocks.gpr incoming 13%nat;Blocks.gpr incoming 14%nat;Blocks.gpr incoming 15%nat],
 if Z.eqb(stack_word bp)(stack_word bp)then true else false)=
 Some([Blocks.gpr incoming 3%nat;Int bp;Blocks.gpr incoming 12%nat;Blocks.gpr incoming 13%nat;
 Blocks.gpr incoming 14%nat;Blocks.gpr incoming 15%nat],true));
 rewrite Z.eqb_refl;unfold stack_word;rewrite Z.mod_mod by lia;rewrite Z.mod_small by exact BP;reflexivity.
Qed.
Lemma map_values {A B}(f g:A->B)xs : map f xs=map g xs ->forall x,In x xs ->f x=g x.
Proof. induction xs;cbn;intros H x I;[contradiction|]. injection H as F G;destruct I as[<- | I];auto. Qed.
Lemma trace_frame size pad c d last es :
 permitted_padding pad -> record_path 200 double4_program abi_layout c=Some(last,es) ->
 writes_only(allowed_write pad)es ->balanced[(caller_slot pad,Caller)]es ->
 flat_frame double4_program size pad es(c,d)(last,effects double4_program(data_effects es)d).
Proof.
 intros Pad R W B loc Place;cbn [fst snd];split;[intros;eapply permitted_bytes;eassumption|].
 intros before M;pose proof(placement_separates _ _ _ Place)as Sep.
 destruct(record_path_sound _ _ _ _ _ _ R)as[_[Slots Reads]].
 assert(Prefix:forall pre tail,es=pre++tail ->
 agrees loc(mapped pad)(effects double4_program(data_effects pre)d)
 (fold_left update_slots pre(return_memory c))(replay double4_program loc pre d before)).
 { intros pre tail ->;apply Forall_app in W as[W _];eapply replay_agrees;eassumption. }
 split;[rewrite <-Slots;eapply replay_agrees;eassumption|].
 split;[intros x Outside;apply replay_frame;intro I;apply Outside;eapply permitted_bytes;eassumption|].
 split.
 { intros pre tail E;split;[exact(Prefix _ _ E)|]. intros k K;apply replay_frame;intro I.
   apply(caller_byte_protected _ _ _ _ Place K);rewrite E in W;apply Forall_app in W as[W _];eapply permitted_bytes;eassumption. }
 intros pre a t tail k E K;specialize(Prefix _ _ E).
 assert(I:In(Pop a t)es)by(rewrite E;apply in_or_app;right;now left).
 assert(Map:mapped pad(ReturnSlot a)).
 { destruct(balanced_pop_location _ _ _ _ B I)as[[A|F]|[u P]].
   - right;symmetry;exact A.
   - contradiction.
   - left;apply Forall_forall with(x:=Push a u)in W;assumption. }
 rewrite E,reads_app in Reads;destruct Reads as[_[Read _]].
 apply(Prefix(ReturnSlot a)k _ Map K);unfold cell_byte;now rewrite Read.
Qed.
Definition written_vectors es := flat_map(fun e=>match e with Write _ a=>[a] | _=>[] end)es.
Lemma output_vector_coverage : forallb(fun i=>existsb(ptr_eq(point,64*Z.of_nat i))
 (written_vectors expected_path))(seq 0 20)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma output_trace_covered es : data_effects es=expected_path ->
 forall loc k,0<=k<1280 ->writes_at loc es(origin loc point+k).
Proof.
 intros E loc k K;set(i:=Z.to_nat(k/64)).
 assert(Q:0<=k/64<20)by(split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 assert(I:(i<20)%nat)by(unfold i;lia).
 assert(Index:Z.of_nat i=k/64)by(unfold i;rewrite Z2Nat.id;lia).
 pose proof output_vector_coverage as W;rewrite forallb_forall in W;specialize(W i ltac:(apply in_seq;lia)).
 apply existsb_exists in W as[a[Member A]];apply ptr_eq_true in A;subst a.
 unfold written_vectors in Member;apply in_flat_map in Member as[op[Op M]].
 destruct op;try contradiction;destruct M as[Eq|[]];subst a.
 rewrite <-E in Op;unfold data_effects in Op;apply in_flat_map in Op as[e[Member Op]].
 destruct e as[op|a t|a t];try contradiction;destruct Op as[Eq|[]];subst op.
 exists(DataOp(Write src(point,64*Z.of_nat i))),(VectorCell(point,64*Z.of_nat i));split;[exact Member|].
 split;[reflexivity|]. unfold inside,cell_address,address_of;cbn [fst snd width].
 pose proof(Z.div_mod k 64 ltac:(lia));pose proof(Z.mod_pos_bound k 64 ltac:(lia));lia.
Qed.
Theorem double4_frame_correct size initial pad final :
 valid_double4_entry initial pad ->returns double4_program abi_layout initial final ->
 registers_preserved initial final /\ memory_safe double4_program size pad initial final /\
 output_initialized double4_program initial final.
Proof.
 destruct initial as[c d];intros[Pad[[incoming[bp[BP Init]]]_]]Returns;cbn [fst] in Init;subst c.
 pose proof(frame_checked incoming pad bp Pad BP)as Check.
 destruct(record_path 200 double4_program abi_layout(initial_control incoming pad bp))as[[last es]|]eqn:R;[|discriminate].
 apply(f_equal(fun result=>match result with Some obs=>fst obs | None=>[] end))in Check as Regs.
 apply(f_equal(fun result=>match result with Some obs=>snd obs | None=>false end))in Check as Safe.
 change(forallb(write_ok pad)es && check_stack[(caller_slot pad,Caller)]es=true)in Safe.
 apply andb_true_iff in Safe as[W B];apply write_ok_sound in W;apply check_stack_sound in B.
 destruct(record_path_sound _ _ _ _ _ _ R)as[P _].
 pose proof(path_returns _ _ _ _ _ _ P d)as Ends.
 pose proof(return_unique _ _ _ _ _ Returns Ends)as ->.
 split;[unfold registers_preserved;cbn [fst];apply map_values;exact Regs|]. split.
 - exists 200%nat,es;split;[exact R|];split;[exact W|];split;[exact B|];now apply trace_frame.
 - exists 200%nat,es;split;[exact R|].
   pose proof(control_path_checked incoming pad bp Pad)as Path;rewrite P in Path.
   cbn [observe_path] in Path;injection Path as _ _ Ops.
   apply output_trace_covered;exact Ops.
Qed.
