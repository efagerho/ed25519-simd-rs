From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.X86 isa.Instructions execution.Blocks memory.MemoryTrace memory.FlatMemory memory.ByteMemory memory.ByteExecution execution.WordBounds execution.ScalarRefinement execution.KnownRegisters.
Import ListNotations. Open Scope Z_scope.

(* Straight-line x86-64 callers. Call operands are symbol addresses in the
   ELF, with the signed rel32 range checked before encoding. A load bias
   relocates the caller and its callees together. The callee relation receives the
   concrete state AFTER the hardware call has pushed its continuation. *)
Inductive command :=
| Save (r:nat) | Restore (r:nat) | Copy (dst src:nat)
| Immediate (dst:nat) (imm:Z) | LeaSIB (dst base:nat) (disp:Z)
| Invoke (target:Z) | Return.
Definition reg_byte base (r:nat) :=
 (if (8 <=? r)%nat then [0x41] else []) ++ [base + Z.of_nat (r mod 8)].
Definition encoding pc op := match op with
 | Save r => reg_byte 0x50 r | Restore r => reg_byte 0x58 r
 | Copy d s => op_bytes (Program [] []) (MovReg d s)
 | Immediate d n => op_bytes (Program [] []) (Mov32 d n)
 | LeaSIB d b n => [0x48 + 4*Z.of_nat(d/8) + Z.of_nat(b/8);0x8d;
                     0x84 + 8*Z.of_nat(d mod 8);0x24] ++ le32 n
 | Invoke target => exit_bytes (CallRel32 (target-(pc+5)))
 | Return => exit_bytes Ret end.
Definition encodable pc op := match op with
 | Save r | Restore r => (r <? 16)%nat && negb (r =? 4)%nat
 | Copy d s => valid_op (Program [] []) (MovReg d s)
 | Immediate d n => valid_op (Program [] []) (Mov32 d n)
 | LeaSIB d b n => (d <? 16)%nat && ((b =? 4) || (b =? 12))%nat && signed 32 n
 | Invoke t => signed 32 (t-(pc+5))
 | Return => true end.
Definition next_pc pc op := pc + Z.of_nat (length (encoding pc op)).
(* Read the target back from the encoded call's four little-endian bytes.
   A proof of a linked caller must reach the callee at this address. *)
Definition displacement32 octets :=
 signed_value (2^31) (read_le 4 (fun i => nth (Z.to_nat i) octets 0) 0).
Definition call_destination pc target :=
 next_pc pc (Invoke target) + displacement32 (tl (encoding pc (Invoke target))).

Lemma displacement32_le32 d : signed 32 d=true -> displacement32 (le32 d)=d.
Proof.
 intro Fits;unfold displacement32;rewrite (read_le_encoded 4 d).
 - change (signed_value (2^31) (d mod (2*2^31))=d).
   unfold signed_value;rewrite Z.mod_mod by lia;now apply signed32_id.
 - intros k K;change (0<=k<4) in K;assert (k=0 \/ k=1 \/ k=2 \/ k=3) by lia;
   destruct H as [H|[H|[H|H]]];subst k;reflexivity.
Qed.
Lemma call_destination_correct pc target : encodable pc (Invoke target)=true ->
 call_destination pc target=target.
Proof.
 intro Fits;change (pc+5+displacement32(le32(target-(pc+5)))=target).
 rewrite displacement32_le32 by exact Fits;ring.
Qed.

Fixpoint assemble pc code : option (list Z) := match code with
 | [] => Some []
 | op::tail => if encodable pc op then
     option_map (app (encoding pc op)) (assemble (next_pc pc op) tail)
   else None end.

Record cpu := CPU { regs : nat->Z; vectors : nat->nat->Z; flag : option bool; mem : bytes }.
Definition set_regs s rs := CPU rs (vectors s) (flag s) (mem s).
Definition set s r v := set_regs s (put (regs s) r v).
Definition with_words s rs flat := CPU rs (vectors s) (flag s) flat.
Definition apply_stack s result := with_words s (result_regs result) (result_mem result).
Definition push s v := let '(rs, flat) := push_words (regs s) (mem s) v in with_words s rs flat.
Definition pop s r := apply_stack s (stack_step 0 0 (PopRegister r) (regs s) (mem s)).
Definition returning s := apply_stack s (stack_step 0 0 NearReturn (regs s) (mem s)).
Definition write_register s d src := set_regs s (register_write (regs s) d src).
Definition well_formed s := (forall r,word64(regs s r)) /\
 (forall j r,(j<8)%nat -> word64(vectors s j r)) /\ byte_memory(mem s).

Definition caller_step slide pc op s :=
 let next := next_pc pc op in
 let transfer ins := let result := stack_step slide next ins (regs s) (mem s) in
                     (target_ip result, apply_stack s result) in
 let assign dst src := (word (slide+next), write_register s dst src) in
 match op with
 | Save r => transfer (PushRegister r)
 | Restore r => transfer (PopRegister r)
 | Copy d r => assign d (FromRegister r)
 | Immediate d n => assign d (Unsigned32 n)
 | LeaSIB d b n => assign d (EffectiveAddress b n)
 | Invoke t =>
   let disp := read_le 4 (fun i => nth (Z.to_nat i) (tl (encoding pc (Invoke t))) 0) 0 in
   transfer (NearCall disp)
 | Return => transfer NearReturn
 end.

Lemma well_formed_stack_top s : well_formed s ->
 stack_top (regs s) (mem s) = read_word (mem s) (regs s 4%nat).
Proof. intros [Words _]; unfold stack_top, word; now rewrite Z.mod_small by apply Words. Qed.

(* Relate the actual caller step to the concrete step used by the leaf
   refinement. Ordinary block operations leave word_pc at the block start;
   the caller also reports its encoded fallthrough. *)
Inductive overlapping_operation : command -> operation -> Prop :=
| overlap_copy d r : overlapping_operation (Copy d r) (MovReg d r)
| overlap_immediate d n : overlapping_operation (Immediate d n) (Mov32 d n)
| overlap_lea n : overlapping_operation (LeaSIB 8 4 n) (LeaR8Rsp n).

Definition scalar_view ip s zf := WordControl ip (regs s) zf.
Theorem caller_operation_agrees slide pc cmd op s zf :
 overlapping_operation cmd op ->
 let '(ip,out) := caller_step slide pc cmd s in
 ip = word (slide+next_pc pc cmd) /\
 scalar_view pc out zf = word_operation op (scalar_view pc s zf) /\
 mem out = mem s /\ flag out = flag s /\ vectors out = vectors s.
Proof. intros H; destruct H; repeat split; reflexivity. Qed.

Inductive overlapping_exit pc : command -> exit -> Prop :=
| overlap_save : overlapping_exit pc (Save 5) PushRbp
| overlap_restore : overlapping_exit pc (Restore 5) PopRbp
| overlap_call target : overlapping_exit pc (Invoke target) (CallRel32 (target-(pc+5)))
| overlap_return : overlapping_exit pc Return Ret.

Theorem caller_transfer_agrees slide pc cmd e s zf :
 overlapping_exit pc cmd e -> encodable pc cmd = true ->
 let '(ip,out) := caller_step slide pc cmd s in
 (scalar_view ip out zf, mem out) =
 word_transfer (slide+next_pc pc cmd) e (scalar_view pc s zf) (mem s) /\
 flag out = flag s /\ vectors out = vectors s.
Proof.
 intros H Valid; destruct H; try solve [repeat split; reflexivity].
 split; [|split; reflexivity].
 change ((scalar_view (word (slide+call_destination pc target))
          (push s (slide+next_pc pc (Invoke target))) zf,
          mem (push s (slide+next_pc pc (Invoke target)))) =
         word_transfer (slide+next_pc pc (Invoke target)) (CallRel32 (target-(pc+5)))
           (scalar_view pc s zf) (mem s)).
 rewrite call_destination_correct by exact Valid.
 cbn [word_transfer stack_step push_words apply_stack with_words scalar_view
      word_pc word_zf word_gpr target_ip result_regs result_mem Z.add].
 rewrite signed32_id by exact Valid.
 replace (slide+next_pc pc (Invoke target)+(target-(pc+5))) with (slide+target)
   by (change (next_pc pc (Invoke target)) with (pc+5); ring).
 reflexivity.
Qed.

(* Invoke resumes only after its callee returns to the pushed continuation. *)
Fixpoint runs (call:Z->cpu->Z->cpu->Prop) slide pc code s exit_ip out : Prop :=
 match code with
 | [] => False
 | op::tail => let next := next_pc pc op in
   let '(ip, state) := caller_step slide pc op s in
   match op with
   | Invoke _ => exists mid, call ip state (word (slide+next)) mid /\
                             runs call slide next tail mid exit_ip out
   | Return => exit_ip=ip /\ out=state
   | _ => runs call slide next tail state exit_ip out
   end end.

Definition scalar_value loc v := match v with
 | Int n => Some n | Ptr a => Some(address_of loc a) | Unknown => None end.
Definition decode loc v := match scalar_value loc v with Some n=>word n | None=>0 end.
Definition export_state loc (s:state) m :=
 CPU (fun r=>decode loc (gpr(fst s)r)) (zmm(snd s)) (zf(fst s)) m.
(* A terminating callee is witnessed by the existing block interpreter
   and the byte replay of its own recorded events. *)
Definition callee_returns p layout loc (s:state) before exit_ip out :=
 exists final fuel events,
 returns p layout s final /\ known_registers(fst final) /\
 record_path fuel p layout (fst s)=Some(fst final,events) /\
 exit_ip=pc_word loc (rip(fst final)) /\
 out=export_state loc final (replay p loc events (snd s) before).

Definition preserved (outside:Z->Prop) (before after:bytes) := forall x, outside x -> after x=before x.
Lemma preserved_read n outside before after a :
 preserved outside before after ->
 (forall k,0<=k<Z.of_nat n -> outside(a+k)) ->
 read_le n after a=read_le n before a.
Proof.
 intros F;revert a;induction n;intros a H;[reflexivity|].
 cbn [read_le];rewrite F,IHn;try reflexivity.
 - intros k K;replace (a+1+k) with (a+(1+k)) by ring;apply H;lia.
 - replace a with (a+0) by ring;apply H;lia.
Qed.
Lemma export_words loc final m : data_words(snd final) -> byte_memory m ->
 well_formed(export_state loc final m).
Proof.
 intros [V _] M;split;[intro r;unfold export_state;cbn [regs];destruct(gpr _ r);
   cbn [decode scalar_value];try apply mod64_word;unfold word64;lia|auto].
Qed.

Lemma word_fits n : word64 n -> word n=n.
Proof. apply Z.mod_small. Qed.
Lemma put_words rs r x : (forall i,word64(rs i)) -> word64 x ->
 forall i,word64(put rs r x i).
Proof. intros W X i;unfold put;destruct Nat.eqb;auto. Qed.
Lemma set_wf s r x : well_formed s -> word64 x -> well_formed(set s r x).
Proof. intros [R [V B]] X;split;[apply put_words;assumption|auto]. Qed.
Lemma push_wf s v : well_formed s -> well_formed(push s v).
Proof.
 intros [R [V B]];split;[apply put_words;[exact R|apply mod64_word]|].
 split;[exact V|apply write_bytes_well_formed;auto using word_byte_bound].
Qed.
Lemma read_store_away m a v base k :
 disjoint a 8 base (8*Z.of_nat k+8) ->
 buffer_words(store_word m a v) base k=buffer_words m base k.
Proof.
 intros D;apply preserved_read with (outside:=fun x=>~(a<=x<a+8)).
 - intros x;apply write_outside.
 - unfold disjoint in D;cbn [Z.of_nat];lia.
Qed.

Lemma read_other_word m a v b : disjoint a 8 b 8 ->
 read_word(store_word m a v)b=read_word m b.
Proof. intro H;pose proof(read_store_away m a v b 0%nat H) as E;unfold buffer_words in E;now rewrite Z.add_0_r in E. Qed.
Lemma wf_copy s d r : well_formed s -> well_formed(set s d (regs s r)).
Proof. intro H;apply set_wf;[exact H|apply H]. Qed.

(* Shared elimination rule for the two public byte certificates. *)
Lemma lift_return p l loc tracked writable initial final before after :
 known_registers(fst initial) -> returns p l initial final ->
 byte_execution p l loc tracked writable initial final before after ->
 let out := export_state loc final after in
 callee_returns p l loc initial before (caller_pc loc) out /\
 well_formed out /\ preserved (fun x=>~writable x) before after.
Proof.
 intros K R [W [B [_ [F [fuel [es [Trace [E _]]]]]]]] out.
 split.
 - exists final,fuel,es;split;[exact R|];split;[exact(reaches_known _ _ _ _ (proj1 R) K)|].
   split;[exact Trace|].
   split;[now rewrite (proj2 R)|now rewrite <-E].
 - split;[apply export_words;[apply (W final (proj1 R))|];assumption|exact F].
Qed.

(* Fuel bounds a certificate search. Two successful searches from the same
   control state must give the same trace, even with different bounds. *)
Lemma walk_unique {A} advance n m c (x y:control*list A) :
 walk advance n c=Some x -> walk advance m c=Some y -> x=y.
Proof.
 revert m c x y;induction n;intros m c x y;destruct m;
 cbn [walk];destruct (rip c);try congruence.
 destruct (advance c) as [[next es]|];try discriminate.
 destruct (walk advance n next) as [[cx xs]|]eqn:X;try discriminate.
 destruct (walk advance m next) as [[cy ys]|]eqn:Y;try discriminate.
 specialize(IHn _ _ _ _ X Y);congruence.
Qed.
Definition functional (call:Z->cpu->Z->cpu->Prop) :=
 forall target s ip out ip' out',call target s ip out ->call target s ip' out' ->
 ip=ip' /\ out=out'.
Lemma callee_unique p l loc s before ip out ip' out' :
 callee_returns p l loc s before ip out -> callee_returns p l loc s before ip' out' ->
 ip=ip' /\ out=out'.
Proof.
 intros [f[n[es[R[_ [T[-> ->]]]]]]] [g[m[ts[S[_ [U[-> ->]]]]]]].
 pose proof(return_unique _ _ _ _ _ R S);subst g.
 pose proof(walk_unique _ _ _ _ _ _ T U);split;congruence.
Qed.
Lemma runs_unique call slide pc code s ip out ip' out' :
 functional call -> runs call slide pc code s ip out -> runs call slide pc code s ip' out' ->
 ip=ip' /\ out=out'.
Proof.
 intros F;revert pc s;induction code as [|op tail IH];[simpl;tauto|].
 intros pc s;destruct op;cbn [runs];try apply IH.
 - intros [a[A B]][b[C D]];destruct(F _ _ _ _ _ _ A C)as[_ E];subst b;eauto.
 - intros [-> ->][-> ->];auto.
Qed.
