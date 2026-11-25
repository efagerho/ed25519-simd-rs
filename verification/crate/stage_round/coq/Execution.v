From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.IndexedLoads execution.Packed
  execution.LinkedCalls execution.WordSemantics memory.ByteMemory memory.FlatMemory
  memory.PackedMemory memory.MemoryGeometry abi.SysV.
From Ed25519Simd.StageRound Require Import Program Audit Routing Selection.
From Machine Require execution.IndexedRegisterWords execution.PackedRegisterWords.
Import ListNotations. Local Open Scope Z_scope.

Section Stage.
Context {s pc n} (P:placement pc n s) (B:byte_memory (mem s)).
Lemma safe_loads st k : ready s st -> reads_safe s k st.
Proof.
 intros R a w I;apply (proj1 (in_rev _ _)) in I.
 change (In (a,w) (rev (loads (load_state k)))) in I.
 rewrite all_reads in I;apply in_flat_map in I as [l [L I]];apply in_seq in L.
 assert (L8:(l<8)%nat) by lia.
 destruct k;cbn [lane_reads In] in I;
 repeat (destruct I as [E|I];[injection E as <- <-|]);try contradiction.
 all: exists l;split;[assumption|].
 all: first [rewrite (digit_address P R) by assumption;split;first [reflexivity|discriminate]
            |rewrite (ptr_address P R) by assumption;split;first [reflexivity|discriminate]
            |rewrite (tile_value P R B) by (auto;cbn;lia);unfold within;cbn [columns];lia].
Qed.

Lemma prefix_ready : ready s (IndexedLoads.execute prefix s).
Proof.
 constructor;[|intros x X;reflexivity].
 intros r H;cbn [kept In] in H;
 repeat (destruct H as [<-|H];[try reflexivity|]);try contradiction.
 all: match goal with |- _=advanced _ ?r => change (word (regs s r+2*regs s 9%nat)=regs s r+2*regs s 9%nat);apply (unwrapped s (regs s r) 512) end;[apply (digits_range _ _ _ P);auto|pose proof (pair_range _ _ _ P);lia].
Qed.
Lemma load_reg st k r : In r kept ->
 regs (IndexedLoads.execute (load_block k) st) r=regs st r.
Proof. intros I;change (eval st (gp (load_state k) r)=regs st r).
 rewrite (proj1 (register_trace k r I));reflexivity. Qed.
Lemma phase_reg st k r : In r kept -> regs (phase st k) r=regs st r.
Proof.
 intros I;unfold phase,Packed.execute,Packed.finish;cbn [regs].
 unfold Packed.update.
 assert (N:(r=?0)%nat=false) by (apply Nat.eqb_neq;intros ->;cbv [kept In] in I;intuition discriminate).
 rewrite N;now apply load_reg.
Qed.
Lemma output_base st k (R:ready s st) :
 regs (IndexedLoads.execute (load_block k) st) 7%nat=regs s 7%nat.
Proof. rewrite load_reg, (arguments _ _ R) by (cbv [kept In];tauto);reflexivity. Qed.
Lemma phase_ready st k : ready s st -> ready s (phase st k).
Proof.
 intro R;constructor.
 - intros r I;rewrite phase_reg by assumption;apply (arguments _ _ R r I).
 - intros x X;unfold phase,Packed.execute;rewrite outside_rows.
   + apply (unchanged _ _ R);exact X.
   + rewrite (output_base _ _ R);exact X.
Qed.

Lemma phase_stores ks : forall ip st,ready s st ->
 WriteTrace.confined (destination s) (phase_writes ip st ks) /\ forall x,
 mem (fold_left phase ks st) x=WriteTrace.replay (mem st) (phase_writes ip st ks) x.
Proof.
 induction ks as [|k rest IH];intros ip st R;[split;[constructor|reflexivity]|].
 cbn [phase_writes fold_left].
 set (loaded:=IndexedLoads.execute (load_block k) st).
 set (at_store:=ip+Z.of_nat(length(flat_map IndexedLoad.encode (load_block k)))).
 assert (V:forallb (Packed.valid_with_alignment true 55) (route k)=true) by (destruct k;reflexivity).
 destruct (PackedWrites.execution true 55 at_store (route k) loaded V) as [W M].
 destruct (IH (ip+Z.of_nat(length(encode_phase k))) (phase st k) (phase_ready _ _ R)) as [T F].
 split.
 - apply Forall_app;split;[|exact T]. unfold PackedWrites.region,loaded in W;
   rewrite (output_base _ _ R) in W;exact W.
 - intro x;rewrite F,WriteTrace.replay_app;apply PackedWrites.replay_ext,M.
Qed.
Lemma stage_writes :
 WriteTrace.confined (destination s) (writes pc s) /\ forall x,
 mem (snd (run pc s)) x=WriteTrace.replay (mem s) (writes pc s) x.
Proof.
 destruct (phase_stores operands (pc+Z.of_nat(length(flat_map IndexedLoad.encode prefix)))
   (IndexedLoads.execute prefix s) prefix_ready) as [W M]. split;[exact W|intro x].
 change (mem (Packed.execute 55 [Upper] (body s)) x=WriteTrace.replay (mem s) (writes pc s) x);rewrite upper_memory;apply M.
Qed.

Definition at_byte row i := regs s 7%nat+64*Z.of_nat row+Z.of_nat i.
Lemma phase_selected st k c i : ready s st -> (c<columns k)%nat -> (i<64)%nat ->
 mem (phase st k) (at_byte (first_row k+c) i) =
 word_byte (read_word (mem s) (selected s k (i/8)%nat+8*Z.of_nat c)) (Z.of_nat (i mod 8)).
Proof.
 intros R C I;destruct (routed k c i C I) as [v [r [j [S [E T]]]]].
 unfold at_byte;rewrite <-(output_base st k R);unfold phase,Packed.execute.
 rewrite row_byte by (auto;destruct k;cbn [first_row columns] in *;lia).
 fold (route_state k);rewrite S,E.
 change (word_byte (eval st (IndexedLoads.vec (load_state k) r j)) (Z.of_nat (i mod 8)) =
         word_byte (read_word (mem s) (selected s k (i/8)%nat+8*Z.of_nat c)) (Z.of_nat (i mod 8))).
 rewrite T,(selected_word P R B) by (auto;apply Nat.div_lt_upper_bound;lia);reflexivity.
Qed.
Lemma phase_other st k row i : ready s st -> (row<55)%nat -> (i<64)%nat ->
 ~(first_row k<=row<first_row k+columns k)%nat ->
 mem (phase st k) (at_byte row i)=mem st (at_byte row i).
Proof.
 intros R U I N;unfold at_byte;rewrite <-(output_base st k R);unfold phase,Packed.execute.
 rewrite row_byte by assumption;fold (route_state k);rewrite untouched by assumption;reflexivity.
Qed.

Let entry := IndexedLoads.execute prefix s.
Let odd := phase entry Odd.
Let affine := phase odd Base.
Let even := phase affine Even.
Local Lemma entry_ok : ready s entry. Proof. apply prefix_ready. Qed.
Local Lemma odd_ok : ready s odd. Proof. apply phase_ready,entry_ok. Qed.
Local Lemma affine_ok : ready s affine. Proof. apply phase_ready,odd_ok. Qed.
Local Lemma even_ok : ready s even. Proof. apply phase_ready,affine_ok. Qed.
Lemma selected_bytes k c i : (c<columns k)%nat -> (i<64)%nat ->
 mem even (at_byte (first_row k+c) i)=
 word_byte (read_word (mem s) (selected s k (i/8)%nat+8*Z.of_nat c)) (Z.of_nat (i mod 8)).
Proof.
 intros C I;destruct k.
 - unfold even,affine;rewrite !phase_other by
    (auto using affine_ok,odd_ok;cbn [first_row columns] in *;lia).
   apply phase_selected;auto using entry_ok.
 - unfold even;rewrite phase_other by (auto using affine_ok;cbn [first_row columns] in *;lia).
   apply phase_selected;auto using odd_ok.
 - apply phase_selected;auto using affine_ok.
Qed.
Lemma final_bytes : byte_memory (mem even).
Proof.
 intro x;destruct (Z_le_dec (regs s 7%nat) x), (Z_lt_dec x (regs s 7%nat+3520));
 try (rewrite (unchanged _ _ even_ok) by (unfold destination;lia);apply B).
 set (d:=x-regs s 7%nat);set (row:=Z.to_nat (d/64));set (i:=Z.to_nat (d mod 64)).
 assert (D:0<=d<3520) by (unfold d;lia).
 pose proof (Z.mod_pos_bound d 64 ltac:(lia)).
 assert (Row:0<=d/64<55) by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 assert (E:x=at_byte row i) by (unfold at_byte,row,i;rewrite !Z2Nat.id by lia;
    pose proof (Z.div_mod d 64 ltac:(lia));unfold d in *;lia).
 rewrite E;assert (I:(i<64)%nat) by (unfold i;lia).
 assert (inside:(row<55)%nat) by (unfold row;lia).
 destruct (lt_dec row 20), (lt_dec row 35).
 - change row with (first_row Odd+row)%nat;rewrite selected_bytes by (cbn;lia);apply word_byte_bound.
 - lia.
 - replace row with (first_row Base+(row-20))%nat by (cbn;lia).
   rewrite selected_bytes by (cbn [columns];lia);apply word_byte_bound.
 - replace row with (first_row Even+(row-35))%nat by (cbn;lia).
   rewrite selected_bytes by (cbn [columns];lia);apply word_byte_bound.
Qed.

Let last := Packed.execute 55 [Upper] even.
Local Lemma stack_before : regs last 4%nat=regs s 4%nat.
Proof. unfold last;rewrite upper_registers;apply (arguments _ _ even_ok 4%nat);cbv [kept In];tauto. Qed.
Local Lemma ret_memory x : mem (returning last) x=mem even x.
Proof. apply upper_memory. Qed.
Local Lemma return_addr :
 word (stack_top (regs last) (mem last))=read_word (mem s) (regs s 4%nat).
Proof.
 destruct (return_range _ _ _ P) as [[L U] Dis];unfold stack_top;rewrite stack_before.
 rewrite (unwrapped _ _ _ (regs s 4%nat) (return_range _ _ _ P)) by lia.
 assert (F:preserved (fun x=> ~destination s x) (mem s) (mem last))
 by (intros x X;unfold last;rewrite upper_memory;apply (unchanged _ _ even_ok);assumption).
 unfold read_word;rewrite (preserved_read _ _ _ _ _ F) by
  (unfold destination,disjoint in *;intros;lia).
 unfold word;apply Z.mod_small;apply read_word_bound;exact B.
Qed.
Local Lemma output_words k c l : (c<columns k)%nat -> (l<8)%nat ->
 read_word (mem (returning last)) (regs s 7%nat+64*Z.of_nat (first_row k+c)+8*Z.of_nat l)=
 read_word (mem s) (selected s k l+8*Z.of_nat c).
Proof.
 intros C L;apply read_word_exact;[now apply read_word_bound|].
 intros j J;rewrite ret_memory.
 set (i:=(8*l+Z.to_nat j)%nat).
 assert (J8:(Z.to_nat j<8)%nat) by lia.
 assert (E:(i/8=l /\ i mod 8=Z.to_nat j)%nat).
 { unfold i;replace (8*l+Z.to_nat j)%nat with (Z.to_nat j + l*8)%nat by lia;rewrite Nat.div_add,Nat.mod_add by lia.
   rewrite Nat.div_small,Nat.mod_small by lia;lia. }
 replace (regs s 7%nat+64*Z.of_nat (first_row k+c)+8*Z.of_nat l+j)
 with (at_byte (first_row k+c) i) by (unfold at_byte,i;rewrite !Nat2Z.inj_add,Nat2Z.inj_mul,Z2Nat.id by lia;ring).
 rewrite selected_bytes by (auto;unfold i;lia).
 destruct E as [D M];rewrite D,M,Z2Nat.id by lia;reflexivity.
Qed.
Lemma stage_returns :
 reads_safe s Odd entry /\ reads_safe s Base odd /\ reads_safe s Even affine /\
 let '(ip,out):=run pc s in
 ip=read_word (mem s) (regs s 4%nat) /\ regs out 4%nat=regs s 4%nat+8 /\
 (forall r,In r sysv_saved -> regs out r=regs s r) /\
 preserved (fun x=> ~destination s x) (mem s) (mem out) /\ byte_memory (mem out) /\
 forall k c l,(c<columns k)%nat -> (l<8)%nat ->
 read_word (mem out) (regs s 7%nat+64*Z.of_nat (first_row k+c)+8*Z.of_nat l)=
 read_word (mem s) (selected s k l+8*Z.of_nat c).
Proof.
 split;[apply safe_loads,entry_ok|];split;[apply safe_loads,odd_ok|];split;[apply safe_loads,affine_ok|].
 split;[apply return_addr|].
 split.
 - change (word (regs last 4%nat+8)=regs s 4%nat+8);rewrite stack_before.
   unfold word;apply Z.mod_small;destruct (return_range _ _ _ P) as [[L _] _];pose proof (return_rsp _ _ _ P);lia.
 - split.
   + intros r H;change (advance_rsp (regs last) r=regs s r);unfold advance_rsp,put.
     destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
       match goal with |- _=regs s ?r => change (regs last r=regs s r);
       unfold last;rewrite upper_registers;apply (arguments _ _ even_ok r);cbv [kept In];tauto end.
   + split;[intros x X;change (mem (returning last) x=mem s x);rewrite ret_memory;apply (unchanged _ _ even_ok);assumption|].
     split;[intros x;change (0<=mem (returning last) x<256);rewrite ret_memory;apply final_bytes|exact output_words].
Qed.
End Stage.

Lemma return_words s : well_formed s -> well_formed (returning s).
Proof.
 intros [G V];exact (conj (put_words (regs s) 4 (word(regs s 4%nat+8)) G (WordBounds.mod64_word _)) V).
Qed.

Theorem stage_words pc s : well_formed s -> well_formed(snd(run pc s)).
Proof.
 intro W;assert (Each:forall k st,well_formed st -> well_formed(phase st k)).
 { intros k st H;apply PackedRegisterWords.execute_words;[apply IndexedRegisterWords.execute_words,H|].
   destruct k;repeat constructor. }
 pose proof(IndexedRegisterWords.execute_words prefix s W) as Start.
 pose proof(Each Even _ (Each Base _ (Each Odd _ Start))) as Body.
 set (last:=Packed.execute 55 [Upper] (body s)).
 assert (End:well_formed last) by (apply PackedRegisterWords.execute_words;[exact Body|repeat constructor]).
 exact (return_words last End).
Qed.
