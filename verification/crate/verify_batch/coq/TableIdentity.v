From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions isa.VectorMoves execution.WordSemantics execution.WordBounds
 execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.MappedFetch
 execution.InstructionRoute memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.KeyTable Require Image.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableEntry TableFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition initialize:list line:=[(50,6%nat,VectorMove(Output 0 0 0));(56,7%nat,VectorMove(Output 0 0 64));
 (63,8%nat,StoreY 0 (Address 0 None 128));(71,7%nat,StoreImmediate (Address 0 None 0) 1);
 (78,8%nat,StoreImmediate (Address 0 None 40) 1);(86,8%nat,StoreImmediate (Address 0 None 120) 2)].
Definition advance:list line:=[(94,6%nat,Add64 0 2720);(100,2%nat,Dec32 1);(102,2%nat,Branch Unequal (-54))].
Lemma image:linked TableFrame.text initialize /\ linked TableFrame.text advance.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition stores o a v:=[vector (word(o+50)) a v;vector (word(o+56)) (a+64) v;
 Store (word(o+63)) (a+128) 32 (vector_byte v);qword (word(o+71)) a 1;
 qword (word(o+78)) (a+40) 1;qword (word(o+86)) (a+120) 2].

Lemma store_row o s c a : 0<=a -> a+160<=2^64 -> regs s 0%nat=a ->
 let ws:=stores o a (fun j=>vectors s j 0%nat) in
 exists t,run 6 (ScalarBytes.fetch o TableFrame.text) (State(Running 50) s c)=Some(State(Running 94) t c,ws) /\
 regs t=regs s /\ vectors t=vectors s /\ mem t=WriteTrace.replay (mem s) ws.
Proof.
 intros L H AX ws;set (v:=fun j=>vectors s j 0%nat);set (t:=with_words s (regs s) (WriteTrace.replay (mem s) ws)).
 exists t;split;[|repeat split;reflexivity].
 apply (InstructionRoute.checked _ _ _ (proj1 image)).
 cbn [initialize follow step effective option_map loc cpu_state cf app regs vectors mem with_words];rewrite AX,!Z.add_0_r.
 repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64;lia)) end;reflexivity.
Qed.

Lemma contained o a v : confined (span a 160) (stores o a v).
Proof. repeat apply Forall_cons;try apply Forall_nil;intros x X;unfold touches in X;cbn [vector qword WriteTrace.address size] in X;unfold span;lia. Qed.

Lemma identity o a v m i : (forall j,v j=0) -> 0<=i<20 ->
 read_word (WriteTrace.replay m (stores o a v)) (a+8*i)=KeyTable.Image.identity_word i.
Proof.
 intros Zero I;apply read_word_exact.
 - unfold KeyTable.Image.identity_word,KeyTable.Image.identity_values;cbn [fold_left fst snd].
   repeat destruct (_=?_);unfold word64;lia.
 - intros k K;change (0<=k<8) in K;unfold WriteTrace.replay,stores;cbn [fold_left commit qword vector address size payload].
   unfold KeyTable.Image.identity_word,KeyTable.Image.identity_values;cbn [fold_left fst snd].
   destruct (Z.eqb_spec i 15) as [->|D15];[replace (a+8*15+k) with (a+120+k) by ring;apply write_at;change (0<=k<8);exact K|].
   unfold commit;cbn [vector qword WriteTrace.address size payload].
   rewrite write_outside by lia.
   destruct (Z.eqb_spec i 5) as [->|D5];[replace (a+8*5+k) with (a+40+k) by ring;apply write_at;change (0<=k<8);exact K|].
   rewrite write_outside by lia.
   destruct (Z.eqb_spec i 0) as [->|D0];[replace (a+8*0+k) with (a+k) by ring;apply write_at;change (0<=k<8);exact K|].
   rewrite write_outside by lia.
   destruct (Z_lt_ge_dec i 16), (Z_lt_ge_dec i 8);try lia;
   repeat rewrite write_outside by lia;
   match goal with |-write_bytes _ ?b _ (vector_byte _) ?x=_ =>
    replace x with (b+(x-b)) by ring;rewrite write_at by lia;unfold vector_byte;rewrite Zero end;
   unfold word_byte;rewrite !Zdiv_0_l;reflexivity.
Qed.

Lemma next o s c a n : regs s 0%nat=a -> regs s 1%nat=n -> 1<=n<=8 -> word64 a ->
 exists t f,run 3 (ScalarBytes.fetch o TableFrame.text) (State(Running 94) s c)=
 Some(State(Running(if n=?1 then 104 else 50)) t f,[]) /\
 regs t=put (put (regs s) 0 (word(a+2720))) 1 (n-1) /\ vectors t=vectors s /\ mem t=mem s.
Proof.
 intros AX CX Range A;set (f:=Some (2^64<=?a+2720)).
 set (t:=with_zf (set (with_zf (set s 0 (word(a+2720))) (word(a+2720)=?0)) 1 (n-1)) (n-1=?0)).
 exists t,f;split;[|repeat split;reflexivity].
 apply (InstructionRoute.checked _ _ _ (proj2 image));cbn [advance follow step option_map eval_condition
  flag loc cf cpu_state with_zf set set_regs regs Nat.eqb put];rewrite AX,CX.
 change (word 2720) with 2720.
 rewrite (word_fits _ A),(Z.mod_small (n-1) (2^32)) by lia.
 unfold t;destruct(Z.eqb_spec n 1) as [One|Many];[rewrite One;reflexivity|rewrite (proj2(Z.eqb_neq (n-1) 0) ltac:(lia));reflexivity].
Qed.

Fixpoint journal (n:nat) o a v:=match n with O=>[] | S k=>stores o a v++journal k o (a+2720) v end.
Definition center a j:=a+2720*Z.of_nat j.
Definition occupied a n x:=exists j,(j<n)%nat /\ span (center a j) 160 x.
Lemma shift_center a i: center (a+2720) i=center a (S i).
Proof. unfold center;lia. Qed.
Lemma footprint n o a v : confined (occupied a n) (journal n o a v).
Proof.
 revert a;induction n as [|n IH];intro a;[constructor|cbn [journal];apply Forall_app;split].
 - eapply Forall_impl;[|apply contained];intros w W x X;exists O;split;[lia|].
   replace (center a O) with a by (unfold center;ring);apply W,X.
 - eapply Forall_impl;[|apply IH];intros w W x X;destruct(W x X) as [j [J Hit]];
   exists (S j);split;[lia|now rewrite <-shift_center].
Qed.

Lemma all_rows n o a v m : (forall j,v j=0) -> forall j,(j<n)%nat -> forall i,0<=i<20 ->
 read_word (WriteTrace.replay m (journal n o a v)) (center a j+8*i)=KeyTable.Image.identity_word i.
Proof.
 intro Zero;revert a m;induction n as [|n IH];intros a m [|j] J i I;try lia;cbn [journal];rewrite WriteTrace.replay_app.
 - replace (center a O) with a by (unfold center;ring).
   rewrite <- (identity o a v m i Zero I).
   apply preserved_read with (outside:=fun x=>~occupied (a+2720) n x);[exact (WriteTrace.frame _ _ (footprint n o (a+2720) v) _)|].
   intros k K [r [_ Hit]];unfold span,center in Hit;lia.
 - rewrite <-shift_center;apply IH;lia.
Qed.

(* Both the possible wrap of the unused final pointer and the final
   fallthrough are consequences of the fetched ADD, DEC and JNE. *)
Definition loop_pc (n:nat):=match n with O=>104 | _=>50 end.
Lemma loop_run n o : forall a s c,(n<=8)%nat -> regs s 0%nat=word a -> regs s 1%nat=Z.of_nat n ->
 0<=a -> (n<>O -> center a (Nat.pred n)+160<=2^64) ->
 exists t f,run (9*n) (ScalarBytes.fetch o TableFrame.text) (State(Running(loop_pc n)) s c)=
 Some(State(Running 104) t f,journal n o a (fun j=>vectors s j 0%nat)) /\
 (forall r,r<>0%nat -> r<>1%nat -> regs t r=regs s r) /\
 regs t 0%nat=word(center a n) /\ regs t 1%nat=0 /\ vectors t=vectors s.
Proof.
 induction n as [|n IH];intros a s c N AX CX L H.
 - exists s,c;split;[reflexivity|]. replace (center a O) with a by (unfold center;ring);auto.
 - specialize (H ltac:(discriminate));change (center a n+160<=2^64) in H.
   assert (Fits:word64 a) by (unfold word64,center in *;lia).
   destruct(store_row o s c a L ltac:(unfold center in H;lia) ltac:(rewrite AX;apply word_fits,Fits))
    as [b [Stored [G [V M]]]].
   destruct(next o b c a (Z.of_nat(S n)) ltac:(rewrite G,AX;apply word_fits,Fits) ltac:(now rewrite G)
    ltac:(lia) Fits) as [d [f [Step [Reg [Vec _]]]]].
   replace (if Z.of_nat(S n)=?1 then 104 else 50) with (loop_pc n) in Step by
    (destruct n as [|k];[reflexivity|rewrite (proj2(Z.eqb_neq (Z.of_nat(S(S k))) 1) ltac:(lia));reflexivity]).
   destruct(IH (a+2720) d f ltac:(lia) ltac:(rewrite Reg;reflexivity)
    ltac:(rewrite Reg;change (Z.of_nat(S n)-1=Z.of_nat n);lia) ltac:(lia)
    ltac:(destruct n as [|n];[contradiction|cbn [Nat.pred];rewrite shift_center;lia]))
    as [u [g [Rest [Stable [Ptr [Counter Upper]]]]]].
   rewrite Vec,V in Rest;pose proof(run_append _ _ _ _ _ Stored _ _ _ Step) as Head;rewrite app_nil_r in Head.
   pose proof(run_append _ _ _ _ _ Head _ _ _ Rest) as Whole.
   exists u,g;split;[replace (9*S n)%nat with (6+3+9*n)%nat by lia;exact Whole|].
   split;[intros r A B;rewrite Stable,Reg,G by assumption;unfold put;
      rewrite (proj2(Nat.eqb_neq 1 r) ltac:(lia)),(proj2(Nat.eqb_neq 0 r) ltac:(lia));reflexivity|].
   rewrite <-shift_center,Ptr,Counter,Upper,Vec,V;auto.
Qed.

Definition fill bias:=segment (TableFrame.base bias) TableFrame.text 72.
Definition first e:=TableEntry.tables e+1280.
Record filled pol bias e p q : Prop:=Filled {
 address:ip q=TableFrame.base bias+104;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 registers:forall r,r<>0%nat -> r<>1%nat -> regs(machine q) r=regs(machine p) r;
 next_pointer:regs(machine q) 0%nat=word(center (first e) 8);
 residual:regs(machine q) 1%nat=0;
 bank:vectors(machine q)=vectors(machine p);
 finished_rows:forall j i,(j<8)%nat -> 0<=i<20 ->
   read_word (mem(machine q)) (center (first e) j+8*i)=KeyTable.Image.identity_word i;
 surrounding:preserved (fun x=>~occupied (first e) 8 x) (mem(machine p)) (mem(machine q));
 events:log q=log p++journal 8 (TableFrame.base bias) (first e) (fun j=>vectors(machine p) j 0%nat);
 stack_base:regs(machine q) 4%nat=KeyTable.Frame.staging (TableEntry.frame pol e)
}.

Theorem checked pol bias e callee p : placement e -> loaded pol bias (mem e) (writable e) ->
 TableFrame.initialized pol bias e callee p -> exists q,fill bias p=Some q /\ filled pol bias e p q.
Proof.
 intros P I E;set (a:=first e);set (o:=TableFrame.base bias);set (s:=machine p).
 pose proof(TableFrame.arguments _ _ _ _ _ E) as Args;destruct(scratch_ok _ P) as [[L H] _].
 pose proof(TableFrame.pointer _ _ _ _ Args) as AX;fold s a in AX.
 assert (Fit:word64 a) by (unfold word64,a,first,TableEntry.tables;lia).
 destruct(loop_run 8 o a s (LinkedRun.carry p) ltac:(lia)
  ltac:(rewrite word_fits by exact Fit;exact AX) (TableFrame.remaining _ _ _ _ Args) (proj1 Fit)
  ltac:(intro;unfold center,a,first,TableEntry.tables;change (Z.of_nat(Nat.pred 8)) with 7;lia))
  as [t [f [R [G [Ptr [CX V]]]]]].
 pose proof(footprint 8 o a (fun j=>vectors s j 0%nat)) as Safe.
 assert (Ok:confined (writable e) (journal 8 o a (fun j=>vectors s j 0%nat))).
 { eapply Forall_impl;[|exact Safe];intros w W x X;destruct(W x X) as [j [J Hit]];right;left;
   unfold center,span,a,first,TableEntry.tables in *;lia. }
 pose proof(TableFrame.writes _ _ _ _ _ E) as Acc;destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 destruct(at_segment _ _ p o TableFrame.text 72 50 _ _ Acc (TableFrame.address _ _ _ _ _ E) Map Sep R Ok) as [Run Paid].
 pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)) as M;
 change (mem t=WriteTrace.replay (mem s) (journal 8 o a (fun j=>vectors s j 0%nat))) in M.
 eexists;split;[exact Run|constructor].
 - reflexivity.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (TableFrame.words _ _ _ _ _ E) Run).
 - exact G.
 - exact Ptr.
 - exact CX.
 - exact V.
 - intros j i J B;change (read_word (mem t) (center a j+8*i)=KeyTable.Image.identity_word i);rewrite M;apply all_rows;[apply (TableFrame.zero _ _ _ _ Args)|exact J|exact B].
 - intros x X;change (mem t x=mem s x);rewrite M;apply (WriteTrace.frame _ _ Safe);exact X.
 - reflexivity.
 - change (regs t 4%nat=KeyTable.Frame.staging (TableEntry.frame pol e));rewrite G by discriminate;exact (TableFrame.stack _ _ _ _ Args).
Qed.
