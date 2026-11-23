From Coq Require Import ZArith List Bool Lia Ring Znumtheory.
From Machine Require Import isa.Instructions execution.Blocks memory.FlatMemory memory.ByteMemory memory.Alignment execution.WordBounds memory.MemoryGeometry.
Import ListNotations.
Open Scope Z_scope.

From Machine Require Export execution.WordSemantics.
Lemma signed_value_id half n : 0<half -> -half<=n<half -> signed_value half n=n.
Proof.
 intros Positive Bounds;unfold signed_value;destruct(Z_le_dec 0 n).
 - rewrite Z.mod_small by lia;destruct(n<?half)eqn:E;[reflexivity|apply Z.ltb_ge in E;lia].
 - assert(E:n mod (2*half)=n+2*half).
   { symmetry;apply Z.mod_unique with(q:= -1);[left;lia|ring]. }
   rewrite E;destruct(n+2*half<?half)eqn:F;[apply Z.ltb_lt in F;lia|lia].
Qed.

Lemma address_fits_word loc a width : 0<width -> fits64(address_of loc a)width ->
 word(address_of loc a)=address_of loc a.
Proof. unfold word,fits64;intros;apply Z.mod_small;lia. Qed.
Lemma signed32_id n : signed 32 n=true -> signed_value (2^31) n=n.
Proof. unfold signed;rewrite andb_true_iff,Z.leb_le,Z.ltb_lt;apply signed_value_id;reflexivity. Qed.
Lemma signed8_id n : signed 8 n=true -> signed_value (2^7) n=n.
Proof. unfold signed;rewrite andb_true_iff,Z.leb_le,Z.ltb_lt;apply signed_value_id;reflexivity. Qed.
Lemma word_idempotent n : word(word n)=word n.
Proof. unfold word;apply Z.mod_mod;lia. Qed.
Lemma word_add n d : word(word n+d)=word(n+d).
Proof. unfold word;apply Z.add_mod_idemp_l;lia. Qed.
Lemma low32_word n : word n mod 2^32=n mod 2^32.
Proof. symmetry;apply Zmod_div_mod;try lia;exists (2^32);reflexivity. Qed.
Lemma low6_word n : word n mod 64=n mod 64.
Proof. symmetry;apply Zmod_div_mod;try lia;exists (2^58);reflexivity. Qed.
Lemma decrement_word n : (word n-1) mod 2^32=(n-1) mod 2^32.
Proof. rewrite (Zminus_mod (word n)), low32_word, <-Zminus_mod;lia. Qed.
Lemma align_word n : word(Z.land (word n) (-64))=word(n-n mod 64).
Proof. rewrite and_rsp_64,low6_word;unfold word;rewrite Zminus_mod, Z.mod_mod, <-Zminus_mod;lia. Qed.

(* A concrete scalar view has qword register values and an actual ZF. Vector
   effects and byte-memory agreement are handled by the existing byte layer. *)
Record word_control := WordControl {
 word_pc : Z; word_gpr : nat -> Z; word_zf : bool
}.
Definition scalar_represents loc s n := match s with
 | Int x => n=word x | Ptr a => n=word(address_of loc a) | Unknown => True end.
Definition registers_represent loc (regs:nat -> scalar) words := forall r,scalar_represents loc(regs r)(words r).
Definition flag_represents (flag:option bool) actual := match flag with Some b=>b=actual | None=>True end.
Definition control_represents loc c w :=
 word_pc w=word(pc_word loc(rip c)) /\
 registers_represent loc(gpr c)(word_gpr w) /\ flag_represents(zf c)(word_zf w).
Definition word_set w r n := WordControl(word_pc w)(put(word_gpr w)r n)(word_zf w).
Lemma registers_put loc regs words r s n : registers_represent loc regs words ->
 scalar_represents loc s n ->registers_represent loc(put regs r s)(put words r n).
Proof. intros R Value i;unfold put;destruct(Nat.eqb r i);auto. Qed.
Lemma control_put loc c w r s n : control_represents loc c w ->scalar_represents loc s n ->
 control_represents loc(set_gpr c r s)(word_set w r n).
Proof. intros[PC[R F]]Value;split;[exact PC|];split;[now apply registers_put|exact F]. Qed.
Lemma pointer_value loc regs words base disp a : registers_represent loc regs words ->
 (match regs base with Ptr p=>Some(offset p disp) | _=>None end)=Some a ->
 word(words base+disp)=word(address_of loc a).
Proof.
 intros R;specialize(R base);destruct(regs base)as[x|[region off]|];try discriminate.
 intros[= <-];cbn [scalar_represents address_of] in R;rewrite R,word_add.
 unfold address_of,offset;cbn;f_equal;ring.
Qed.
Lemma effective_address_refines loc c w base disp a width :
 control_represents loc c w -> pointer_at c base disp=Some a ->
 0<width ->fits64(address_of loc a)width ->
 word(word_gpr w base+disp)=address_of loc a.
Proof.
 intros[_[Regs _]]Address Width Fits.
 rewrite(pointer_value _ _ _ _ _ _ Regs Address).
 now apply(address_fits_word loc a width).
Qed.

(* Only alignment needs a region-origin condition. Other pointer arithmetic
   is related modulo 2^64; accesses use explicit address-range conditions. *)
Definition operation_placement loc c op := match op with
 | AlignRsp64 => match pointer_at c 4 0 with
   | Some(region,_) => origin loc region mod 64=0 | None=>True end
 | _ => True end.
Definition word_operation op w :=
 let regs:=word_gpr w in let ip:=word_pc w in let flag:=word_zf w in
 match op with
 | Mov32 d n => WordControl ip (register_write regs d (Unsigned32 n)) flag
 | MovAbsRax n => word_set w 0 (word n)
 | MovRaxImm32 n => word_set w 0 (word(signed_value (2^31) n))
 | MovReg d s => WordControl ip (register_write regs d (FromRegister s)) flag
 | AdjustRsp sub n => let v:=word(regs 4%nat+(if sub then -signed_value (2^31) n else signed_value (2^31) n)) in
   WordControl ip (put regs 4 v) (v=?0)
 | LeaR8Rsp n => WordControl ip (register_write regs 8 (EffectiveAddress 4 n)) flag
 | LeaR8Rsi n => WordControl ip (register_write regs 8 (EffectiveAddress 6 n)) flag
 | Test32 r mask => WordControl ip regs (Z.land (regs r mod 2^32) mask =? 0)
 | Cmp32Imm8 r n => WordControl ip regs (regs r mod 2^32 =? (signed_value (2^7) n) mod 2^32)
 | DecEcx => let v:=(regs 1%nat-1) mod 2^32 in WordControl ip (put regs 1 (word v)) (v=?0)
 | AlignRsp64 => let v:=word(Z.land (regs 4%nat) (-64)) in WordControl ip (put regs 4 v) (v=?0)
 | _ => w end.

Theorem operation_refines p l loc c op mid es w :
 valid_op p op=true -> operation_placement loc c op ->
 exec_op p l c op=Some(mid,es) -> control_represents loc c w ->
 control_represents loc mid (word_operation op w).
Proof.
 intros Valid Placement Exec Rep.
 destruct Rep as[PC[Regs Flags]].
 destruct op;cbn [exec_op] in Exec;cbn [word_operation]; try unfold register_write.
 - injection Exec as <- <-;apply control_put;[repeat split;assumption|reflexivity].
 - injection Exec as <- <-;apply control_put;[repeat split;assumption|].
   cbn [scalar_represents];symmetry;apply word_idempotent.
 - destruct(gpr c 0%nat);try discriminate;injection Exec as <- <-;repeat split;assumption.
 - destruct(pointer_at c 4 (if subtract then -imm else imm))as[a|]eqn:A;[|discriminate].
   injection Exec as <- <-;cbn [valid_op] in Valid;rewrite(signed32_id _ Valid).
   split;[exact PC|];split;[|exact Logic.I];apply registers_put;[exact Regs|].
   exact(pointer_value _ _ _ _ _ _ Regs A).
 - destruct(pointer_at c 4 disp)as[a|]eqn:A;[|discriminate].
   injection Exec as <- <-;cbn [valid_op] in Valid;rewrite(signed32_id _ Valid).
   apply control_put;[repeat split;assumption|exact(pointer_value _ _ _ _ _ _ Regs A)].
 - unfold pointer_at in Exec;destruct(gpr c 1%nat)eqn:R;try discriminate.
   injection Exec as <- <-;specialize(Regs 1%nat)as Value;rewrite R in Value;cbn [scalar_represents] in Value.
   rewrite Value,decrement_word;split;[exact PC|];split;[|reflexivity].
   apply registers_put;[exact Regs|reflexivity].
 - destruct(pointer_at c base disp);[destruct(vector_ok l p0 false)|];try discriminate;
   injection Exec as <- <-;repeat split;assumption.
 - destruct(pointer_at c base disp);[destruct(vector_ok l p0 true)|];try discriminate;
   injection Exec as <- <-;repeat split;assumption.
 - destruct(lookup_fragment p fragment);[destruct(forallb _ _)|];try discriminate;
   injection Exec as <- <-;repeat split;assumption.
 - injection Exec as <- <-;repeat split;assumption.
 - injection Exec as <- <-;apply control_put;[repeat split;assumption|apply Regs].
 - unfold pointer_at in Exec,Placement;destruct(gpr c 4%nat)as[n|[region off]|]eqn:R;try discriminate.
   injection Exec as <- <-;unfold operation_placement in Placement;unfold pointer_at in Placement;rewrite R in Placement;cbn in Placement.
   specialize(Regs 4%nat)as Value;rewrite R in Value;cbn [scalar_represents address_of] in Value.
   rewrite Value,align_word;split;[exact PC|];split;[|exact Logic.I].
   apply registers_put;[exact Regs|].
   cbn [scalar_represents];unfold address_of;cbn [fst snd];rewrite Z.add_0_r.
   rewrite Z.add_mod, Placement, Z.add_0_l, Z.mod_mod by lia;f_equal;ring.
 - destruct(pointer_at c 6 disp)as[a|]eqn:A;[|discriminate].
   injection Exec as <- <-;cbn [valid_op] in Valid;rewrite(signed32_id _ Valid).
   apply control_put;[repeat split;assumption|exact(pointer_value _ _ _ _ _ _ Regs A)].
 - injection Exec as <- <-;apply control_put;[repeat split;assumption|].
   cbn [valid_op] in Valid;unfold unsigned in Valid;rewrite andb_true_iff,Z.leb_le,Z.ltb_lt in Valid.
   rewrite signed_value_id by lia;cbn [scalar_represents];symmetry;apply word_idempotent.
 - destruct(gpr c reg)eqn:R;try discriminate;injection Exec as <- <-.
   specialize(Regs reg)as Value;rewrite R in Value;cbn [scalar_represents] in Value.
   split;[exact PC|];split;[exact Regs|];cbn [flag_represents zf word_zf];now rewrite Value,low32_word.
 - destruct(gpr c reg)eqn:R;try discriminate;injection Exec as <- <-.
   specialize(Regs reg)as Value;rewrite R in Value;cbn [scalar_represents] in Value.
   apply andb_true_iff in Valid as [_ I]. rewrite(signed8_id _ I).
   split;[exact PC|];split;[exact Regs|];cbn [flag_represents zf word_zf];now rewrite Value,low32_word.
Qed.

Definition transfer_encoding e := match e with
 | CallRel32 d | JmpRel32 d => signed 32 d
 | JneRel8 d | JeRel8 d | JmpRel8 d => signed 8 d | _ => true end.
Lemma checked_transfer_encoding p b : valid_exit p b=true ->transfer_encoding(terminator b)=true.
Proof.
 unfold valid_exit,transfer_encoding;destruct(terminator b);intro H;try reflexivity;
 repeat rewrite andb_true_iff in H;tauto.
Qed.
Definition stack_access loc flat e := match e with
 | Push a _ => fits64(address_of loc a)8
 | Pop a t => fits64(address_of loc a)8 /\ read_word flat(address_of loc a)=word(pc_word loc t)
 | DataOp _ => True end.
Definition word_transfer next e w flat : word_control * bytes :=
 let regs:=word_gpr w in let flag:=word_zf w in
 let finish ip regs flat := (WordControl (word ip) regs flag,flat) in
 let stack op := let result := stack_step 0 next op regs flat in
   (WordControl (target_ip result) (result_regs result) flag, result_mem result) in
 match e with
 | Next => finish next regs flat
 | JmpRel8 d => finish (next+signed_value (2^7) d) regs flat
 | JmpRel32 d => finish (next+signed_value (2^31) d) regs flat
 | JeRel8 d => finish (if flag then next+signed_value (2^7) d else next) regs flat
 | JneRel8 d => finish (if flag then next else next+signed_value (2^7) d) regs flat
 | CallRel32 d => stack (NearCall d)
 | PushRbp => stack (PushRegister 5)
 | PopRbp => stack (PopRegister 5)
 | Ret => stack NearReturn
 end.
Lemma pointer_zero loc regs words a : registers_represent loc regs words ->
 (match regs 4%nat with Ptr p=>Some(offset p 0) | _=>None end)=Some a ->
 word(words 4%nat)=word(address_of loc a).
Proof. intros R A;pose proof(pointer_value _ _ _ _ _ _ R A)as E;now rewrite Z.add_0_r in E. Qed.
Lemma pointer_increment loc regs words a : registers_represent loc regs words ->
 (match regs 4%nat with Ptr p=>Some(offset p 0) | _=>None end)=Some a ->
 word(words 4%nat+8)=word(address_of loc(offset a 8)).
Proof.
 intros R A;pose proof(pointer_zero _ _ _ _ R A)as E.
 rewrite <-word_add,E,word_add;unfold address_of,offset;cbn;f_equal;ring.
Qed.
Theorem transfer_refines p l loc c next e last es w d flat :
 transfer_encoding e=true ->
 transfer_recorded l c next e=Some(last,es) ->
 Forall (stack_access loc flat) es -> control_represents loc c w ->
 let result:=word_transfer(code_base loc+next)e w flat in
 control_represents loc last(fst result) /\ snd result=replay p loc es d flat.
Proof.
 intros Encoding Exec Access [PC[Regs Flags]].
 destruct e;cbn [transfer_recorded] in Exec;cbn [word_transfer stack_step push_words target_ip result_regs result_mem advance_rsp stack_top Z.add].
 - injection Exec as <- <-;split;[repeat split;try assumption;reflexivity|reflexivity].
 - destruct(pointer_at c 4 (-8))as[a|]eqn:A;[destruct(return_ok l a)eqn:Permission|];try discriminate.
   injection Exec as <- <-;inversion Access as[|? ? Fits _];subst.
   cbn [transfer_encoding] in Encoding;rewrite(signed32_id _ Encoding).
   pose proof(pointer_value _ _ _ _ _ _ Regs A)as SP.
   replace(word_gpr w 4%nat-8)with(word_gpr w 4%nat+(-8))by ring;rewrite SP.
   split.
   + split.
     * cbn [word_pc pc_word rip fst]. f_equal;ring.
     * split;[|exact Flags].
     apply registers_put;[exact Regs|reflexivity].
   + cbn [replay next_data write_event pc_word];rewrite(address_fits_word loc a 8 ltac:(lia) Fits);reflexivity.
 - destruct(zf c)as[zero|]eqn:Zf;[|discriminate];injection Exec as <- <-.
   cbn [transfer_encoding] in Encoding;rewrite(signed8_id _ Encoding).
   cbn [flag_represents] in Flags;rewrite <-Flags;split;[|reflexivity].
   split;[destruct zero;cbn [word_pc pc_word rip fst];f_equal;ring|];split;[exact Regs|reflexivity].
 - destruct(pointer_at c 4 0)as[a|]eqn:A;[destruct(return_ok l a)eqn:Permission|];try discriminate.
   destruct(return_memory c a)as[t|]eqn:Saved;[|discriminate];injection Exec as <- <-.
   inversion Access as[|? ? Safe _];subst;destruct Safe as[Fits Read].
   unfold stack_top; rewrite(pointer_zero _ _ _ _ Regs A),(address_fits_word loc a 8 ltac:(lia) Fits),Read,word_idempotent.
   split;[|reflexivity];split;[reflexivity|];split;[|exact Flags].
   apply registers_put;[exact Regs|exact(pointer_increment _ _ _ _ Regs A)].
 - destruct(pointer_at c 4 (-8))as[a|]eqn:A;[|discriminate].
   destruct(gpr c 5%nat)eqn:R;try discriminate;destruct(return_ok l a)eqn:Permission;[|discriminate].
   injection Exec as <- <-;inversion Access as[|? ? Fits _];subst.
   pose proof(pointer_value _ _ _ _ _ _ Regs A)as SP.
   specialize(Regs 5%nat)as Value;rewrite R in Value;cbn [scalar_represents] in Value.
   replace(word_gpr w 4%nat-8)with(word_gpr w 4%nat+(-8))by ring;rewrite SP.
   split.
   + split;[reflexivity|];split;[|exact Flags];apply registers_put;[exact Regs|reflexivity].
   + cbn [replay next_data write_event pc_word];rewrite(address_fits_word loc a 8 ltac:(lia) Fits),Value;reflexivity.
 - destruct(pointer_at c 4 0)as[a|]eqn:A;[destruct(return_ok l a)eqn:Permission|];try discriminate.
   destruct(return_memory c a)as[t|]eqn:Saved;[destruct t|];try discriminate;injection Exec as <- <-.
   inversion Access as[|? ? Safe _];subst;destruct Safe as[Fits Read].
   unfold stack_top; rewrite(pointer_zero _ _ _ _ Regs A),(address_fits_word loc a 8 ltac:(lia) Fits),Read.
   split;[|reflexivity];split;[reflexivity|];split;[|exact Flags].
   apply registers_put;[apply registers_put;[exact Regs|exact(pointer_increment _ _ _ _ Regs A)]|].
   cbn [scalar_represents pc_word];change(word bits=word(word bits));symmetry;apply word_idempotent.
 - destruct(zf c)as[zero|];[|discriminate];injection Exec as <- <-.
   cbn [transfer_encoding] in Encoding;rewrite(signed8_id _ Encoding).
   cbn [flag_represents] in Flags;rewrite <-Flags;split;[|reflexivity].
   split;[destruct zero;cbn [word_pc pc_word rip fst];f_equal;ring|];split;[exact Regs|reflexivity].
 - injection Exec as <- <-;rewrite(signed8_id _ Encoding);split;[|reflexivity].
   split;[cbn [word_pc pc_word rip fst];f_equal;ring|];split;assumption.
 - injection Exec as <- <-;rewrite(signed32_id _ Encoding);split;[|reflexivity].
   split;[cbn [word_pc pc_word rip fst];f_equal;ring|];split;assumption.
Qed.

Lemma word_bound n : word64(word n).
Proof. apply mod64_word. Qed.
Definition word_control_well_formed w :=
 word64(word_pc w) /\ forall r,word64(word_gpr w r).
Lemma word_operation_well_formed op w : word_control_well_formed w ->
 word_control_well_formed(word_operation op w).
Proof.
 intros[PC Regs];destruct op;split;cbn [word_operation register_write word_set word_pc word_gpr];try exact PC;
 intro r;unfold register_write, advance_rsp, put;repeat destruct(Nat.eqb _ r);auto using word_bound.
Qed.
Lemma word_transfer_well_formed next e w flat :
 word_control_well_formed w -> byte_memory flat ->
 word_control_well_formed(fst(word_transfer next e w flat)).
Proof.
 intros[PC Regs]Bytes;destruct e;split;cbn [word_transfer stack_step push_words target_ip result_regs result_mem advance_rsp stack_top word_pc word_gpr fst];
 try apply word_bound;intro r;unfold register_write, advance_rsp, put;repeat destruct(Nat.eqb _ r);
 auto using word_bound,read_word_bound.
 unfold stack_top; now apply read_word_bound.
Qed.

(* No second interpreter is used to check alignment requirements. This
   predicate follows the actual successful primitive operations. *)
Inductive body_placed p l loc : control ->list operation ->Prop :=
| placed_end c : body_placed p l loc c []
| placed_next c op mid es rest : operation_placement loc c op ->
  exec_op p l c op=Some(mid,es) -> body_placed p l loc mid rest ->
  body_placed p l loc c(op::rest).
Definition word_body ops w := fold_left (fun w op=>word_operation op w) ops w.
Theorem body_refines p l loc c ops mid es w :
 Forall(fun op=>valid_op p op=true)ops ->body_placed p l loc c ops ->
 exec_body p l c ops=Some(mid,es) ->control_represents loc c w ->
 control_represents loc mid(word_body ops w).
Proof.
 intros Valid Placed;revert mid es w Valid;induction Placed as[ c |c op next head rest Place Step Tail IH];
 intros mid es w Valid Exec Rep.
 - injection Exec as <- <-;exact Rep.
 - inversion Valid as[|? ? Head Rest];subst.
   cbn [exec_body] in Exec;rewrite Step in Exec.
   destruct(exec_body p l next rest)as[[last events]|]eqn:Run;[|discriminate].
   injection Exec as <- <-;eapply IH;[exact Rest|reflexivity|].
   exact(operation_refines _ _ _ _ _ _ _ _ Head Place Step Rep).
Qed.

(* The byte memory here is the memory at the terminator, after the block's
   vector effects. ByteExecution establishes that memory's prefix reads. *)
Theorem block_scalar_refines p l loc b c mid ops last events w d flat :
 valid_exit p b=true -> Forall(fun op=>valid_op p op=true)(body b) ->
 body_placed p l loc c(body b) ->exec_body p l c(body b)=Some(mid,ops) ->
 transfer_recorded l mid(after p b)(terminator b)=Some(last,events) ->
 Forall(stack_access loc flat)events ->control_represents loc c w ->
 let result:=word_transfer(code_base loc+after p b)(terminator b)(word_body(body b)w)flat in
 control_represents loc last(fst result) /\ snd result=replay p loc events d flat.
Proof.
 intros Exit Ops Placed Body Transfer Access Rep.
 eapply transfer_refines;[exact(checked_transfer_encoding p b Exit)|exact Transfer|exact Access|].
 eapply body_refines;eassumption.
Qed.

(* This is a local refinement guarantee with explicit placement and read
   premises, not a claim of independent x86 decoding or whole-ISA refinement. *)
Definition scalar_model_refinement p :=
 (forall l loc c op mid es w,valid_op p op=true ->operation_placement loc c op ->
   exec_op p l c op=Some(mid,es) ->control_represents loc c w ->
   control_represents loc mid(word_operation op w)) /\
 (forall l loc c next e last es w d flat,transfer_encoding e=true ->
   transfer_recorded l c next e=Some(last,es) ->Forall(stack_access loc flat)es ->
   control_represents loc c w ->
   let result:=word_transfer(code_base loc+next)e w flat in
   control_represents loc last(fst result) /\ snd result=replay p loc es d flat).
Theorem scalar_model_refinement_checked p : scalar_model_refinement p.
Proof. split;[exact(operation_refines p)|exact(transfer_refines p)]. Qed.

Example alignment_requires_the_origin :
 ~operation_placement (Placement(fun _=>1)0 0)
   (Control(At 0)(fun _=>Ptr(0%nat,63))None(fun _=>None)) AlignRsp64.
Proof. vm_compute;discriminate. Qed.
Example signed_immediate_boundary : signed_value(2^31)(2^31)= -(2^31).
Proof. reflexivity. Qed.
Example stack_pointer_wraps :
 word_gpr(fst(word_transfer 7 Ret(WordControl 0(fun _=>2^64-8)false)(fun _=>0)))4%nat=0.
Proof. reflexivity. Qed.
