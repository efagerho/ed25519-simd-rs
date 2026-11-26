From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.PackedStores execution.VectorOutputs memory.ByteMemory.
From Ed25519Simd.KeyTable Require Pack Rows.
From Ed25519Simd.KeyTable Require Import TablePackValues.
From Ed25519Simd.KeyTable Require TablePackRows.
From Ed25519Simd.KeyTable Require Import CallLayout.
Import ListNotations. Local Open Scope Z_scope.

(* Address the two signed rows in a common qword array. Even if two
   operands name the same address, the later store supplies its bytes. *)
Definition index digit (pos:bool) off:=(if pos then 20*digit else -20*digit)+Z.of_nat off.
Definition location e x:=TableIdentity.first e+8*x.
Definition table_memory:=Z->Pack.word.
Definition matches f e (m:table_memory) s:=forall x,known(m x)=true -> read_word (mem s) (location e x)=Rows.eval f (m x).
Definition out pos off src part:=Out src (if pos:bool then 13 else 14) (8*Z.of_nat off) part.
Definition overlay digit pos off w (r:register_file) (m:table_memory) x:=
 let j:=x-index digit pos off in if (0<=?j)&&(j<?Z.of_nat(lanes w)) then
 r (source w) (shift w+Z.to_nat j)%nat else m x.
Definition update digit r m op:=match op with
 | Pack.Store pos off src=>overlay digit pos off (out pos off src Full) r m
 | Pack.Extract pos off src half=>overlay digit pos off (out pos off src (Half(Nat.odd half))) r m
 | _=>m end.

Lemma destination e digit s pos off src part : placement e -> 1<=digit<=8 ->
 TableMultiple.pointers e digit s -> TablePackRows.in_row (Write (out pos off src part))=true ->
 address s (out pos off src part)=location e (index digit pos off).
Proof.
 intros P N Ptr OK;cbn [TablePackRows.in_row] in OK;apply Bool.andb_true_iff in OK as [Both Size].
 apply Bool.andb_true_iff in Both as [_ Hi];apply Z.ltb_lt in Hi;apply Z.leb_le in Size.
 set (w:=out pos off src part) in *.
 change (displacement w) with (8*Z.of_nat off) in *.
 pose proof(Z.div_mod (8*Z.of_nat off) 2720 ltac:(lia));pose proof(Z.mod_pos_bound (8*Z.of_nat off) 2720 ltac:(lia)).
 assert (Limit:8*Z.of_nat off<=7*2720+159)
   by (unfold w,out,size in Size;destruct part;cbn [piece] in Size;lia).
 destruct(table_fit _ P) as [Low Upper];unfold address,w,out;cbn [VectorOutputs.base displacement];unfold location,index.
 destruct pos;[rewrite (TableMultiple.positive _ _ _ Ptr)|rewrite (TableMultiple.negative _ _ _ Ptr)];
 unfold TableMultiple.pos,TableMultiple.neg,TableIdentity.first;rewrite word_fits;[ring|unfold word64;lia|ring|unfold word64;lia].
Qed.

Lemma store_word e digit o pc f r m s ks pos off src part :
 placement e -> 1<=digit<=8 -> TableMultiple.pointers e digit s -> well_formed s ->
 TablePackRows.in_row (Write (out pos off src part))=true -> represents f r s -> matches f e m s ->
 let w:=out pos off src part in
 matches f e (overlay digit pos off w r m) (apply_op o pc s ks (Write w)).
Proof.
 intros P N Ptr W Safe V M w x.
 change (known (overlay digit pos off w r m x)=true ->
  read_word (WriteTrace.commit (mem s) (event o (Z.of_nat pc) s w)) (TableIdentity.first e+8*x)=Rows.eval f (overlay digit pos off w r m x)).
 rewrite (word_at _ _ _ _ _ _ (index digit pos off) _ (destination _ _ _ _ _ _ _ P N Ptr Safe) W).
 unfold overlay;fold w;set (j:=x-index digit pos off).
 destruct ((0<=?j)&&(j<?Z.of_nat(lanes w))) eqn:J;[|exact (M x)].
 apply Bool.andb_true_iff in J as [L H];apply Z.leb_le in L;apply Z.ltb_lt in H.
 apply V;unfold lanes,shift in *;destruct(piece w) as [|[]];lia.
Qed.

Definition symbolic_state:=(register_file*table_memory)%type.
Definition symbolic_step digit (s:symbolic_state) op:=(advance (fst s) op,update digit (fst s) (snd s) op).
Definition represents_state f e (v:symbolic_state) s:=represents f (fst v) s /\ matches f e (snd v) s.

Lemma simulate e digit o ops : forall off p ks f st last ws,
 placement e -> 1<=digit<=8 -> TableMultiple.pointers e digit p -> well_formed p ->
 Forall (fun v=>TablePackRows.in_row (TablePackRows.lower v)=true) ops -> mask_ok ks ->
 represents_state f e st p -> PackedStores.simulate o off (map TablePackRows.lower ops) p ks=(last,ws) ->
 represents_state f e (fold_left (symbolic_step digit) ops st) last.
Proof.
 induction ops as [|v tail IH];intros off p ks f [r m] last ws P N Ptr W Safe Mask [V M] R.
 - injection R as <- <-;now split.
 - apply Forall_cons_iff in Safe as [S SS];cbn [map PackedStores.simulate] in R.
   set (u:=apply_op o off p ks (TablePackRows.lower v)) in *.
   destruct(PackedStores.simulate o _ _ u ks) as [t events] eqn:E;injection R as <- <-.
   eapply (IH _ u ks f (symbolic_step digit (r,m) v) _ _);[exact P|exact N| |apply apply_words,W|exact SS|exact Mask| |exact E].
   + destruct Ptr;constructor;change (regs u) with (regs (effect p ks (TablePackRows.lower v)));rewrite gprs;assumption.
   + split;[apply one;assumption|destruct v;try exact M;apply store_word;assumption].
Qed.
