From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics memory.ByteMemory memory.FlatMemory
  memory.WriteTrace memory.RowWrites memory.PackedWrites.
From Ed25519Simd.Sha512Challenge Require Import Image Control Block Frame Output Execution Refinement.
Import ListNotations. Local Open Scope Z_scope.

Definition row_pc origin (label:nat->Image.label) i := origin+pos (label i).
Definition stack_rows pc base count m v :=
 tiles pc base 64 count (fun _=>true) (matrix m base (Z.of_nat count) v).
Lemma rows_memory pc base count m v x :
 WriteTrace.replay m (stack_rows pc base count m v) x = matrix m base (Z.of_nat count) v x.
Proof.
 apply tiles_replay;[lia|]. intro O;unfold matrix;apply write_outside.
 intro H;apply O;split;[exact H|reflexivity].
Qed.

Definition publish origin s m t hs :=
 tiles (fun q=>row_pc origin StoreDigest (q/8)%nat) (dst s) 8 64
    (fun q=>finish_mask s m t (q mod 8)%nat) (Execution.stores s m t hs).
Lemma lane_at off : 0<=off ->
 (Z.to_nat (off/8) mod 8)%nat = Z.to_nat (off mod 64/8).
Proof.
 intro B;change 8%nat with (Z.to_nat 8);rewrite <-Z2Nat.inj_mod by (try apply Z.div_pos;lia).
 f_equal. pose proof (Z.mod_pos_bound off 64 ltac:(lia)) as R.
 rewrite (Z.div_mod off 64 ltac:(lia)) at 1.
 replace (64*(off/64)+off mod 64) with (off mod 64+(8*(off/64))*8) by ring.
 rewrite Z.div_add by lia. replace (8*(off/64)) with ((off/64)*8) by ring.
 rewrite Z.mod_add by lia;apply Z.mod_small;split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia.
Qed.
Lemma publish_memory origin s m t hs x :
 WriteTrace.replay m (publish origin s m t hs) x=Execution.stores s m t hs x.
Proof.
 apply tiles_replay;[lia|]. intro Outside;unfold Execution.stores.
 destruct (_ && _ && _)%bool eqn:E;[|reflexivity].
 apply andb_true_iff in E as [B M];apply andb_true_iff in B as [L U].
 apply Z.leb_le in L;apply Z.ltb_lt in U;exfalso;apply Outside;split.
 - change (dst s<=x<dst s+512);lia.
 - rewrite lane_at by assumption;exact M.
Qed.

Definition push_at s ip := qword (ip-5) (frame s-8) ip.
Definition enter_writes origin s :=
 let a:=sp s-8 in let saved:=store_word (mem s) a (regs s 5%nat) in
 qword origin a (regs s 5%nat) ::
 stack_rows (row_pc origin SaveLength) (frame s+512) 3 saved (length_value s).

Definition spill_writes origin s m hs :=
 stack_rows (row_pc origin SpillRow) (frame s) 8 m
    (fun r j=>Z.of_N (nth r (spill (hs j)) 0%N)).

(* Follow blocks' call checks and loop condition even on an early exit.
   A failed return check still leaves the preceding call push in the trace. *)
Fixpoint loop_writes fuel origin table s upper lower stride t cursor hs m := match fuel with
 | O=>[] | S gas=>push_at s upper ::
   match call_rows s m upper with None=>[] | Some back=>
   let saved:=spill_frame back s hs in let work:=hash_step table s saved t cursor hs in
   spill_writes origin s back hs ++ publish origin s saved t work ++
   if continuing s saved t then push_at s lower ::
     match call_rows s (Execution.stores s saved t work) lower with None=>[] | Some back'=>
     loop_writes gas origin table s upper lower stride (S t) (cursor+stride+stride)%nat work back'
     end else [] end end.

Lemma call_memory s m ip back : call_rows s m ip=Some back ->
 back=commit m (push_at s ip).
Proof. unfold call_rows;destruct (_=?_);[intros H;injection H|discriminate];auto. Qed.

Lemma replay_cons m w ws : WriteTrace.replay m (w::ws)=WriteTrace.replay (commit m w) ws.
Proof. reflexivity. Qed.
Lemma loop_memory fuel origin table s upper lower stride : forall t cur hs m after,
 blocks fuel table s upper lower stride t cur hs m=Some after ->
 forall x, after x=WriteTrace.replay m (loop_writes fuel origin table s upper lower stride t cur hs m) x.
Proof.
 induction fuel as [|gas IH];intros t cur hs m after R x;[discriminate|].
 cbn [blocks] in R;cbn [loop_writes]. destruct (call_rows s m upper) as [back|] eqn:C;[|discriminate].
 set (saved:=spill_frame back s hs) in *. set (work:=hash_step table s saved t cur hs) in *.
 set (published:=Execution.stores s saved t work) in *.
 rewrite replay_cons,!replay_app.
 rewrite <- (call_memory _ _ _ _ C).
 assert (S:forall x, WriteTrace.replay back (spill_writes origin s back hs) x=saved x)
   by (intro;apply rows_memory).
 assert (P:forall x,WriteTrace.replay (WriteTrace.replay back (spill_writes origin s back hs))
     (publish origin s saved t work) x=published x).
 { intro a;rewrite (replay_ext _ saved _ S);apply publish_memory. }
 rewrite (replay_ext _ published _ P). destruct (continuing s saved t);[|injection R as <-;reflexivity].
 destruct (call_rows s published lower) as [back'|] eqn:D;[|discriminate].
 rewrite replay_cons.
 rewrite <- (call_memory _ _ _ _ D);eapply IH;exact R.
Qed.

Lemma inside_frame s : frame s+704<=sp s-8.
Proof. unfold frame;pose proof (Z.mod_pos_bound (sp s-8) 64 ltac:(lia));lia. Qed.
Lemma enter_confined origin s : confined (writable s) (enter_writes origin s).
Proof.
 pose proof (inside_frame s) as B;constructor.
 - intros x X;left;change (sp s-8<=x<sp s-8+8) in X;lia.
 - apply tiles_confined;[lia|]. intros x X;left;change (frame s+512<=x<frame s+512+192) in X;lia.
Qed.
Lemma loop_confined fuel origin table s upper lower stride : forall t cur hs m,
 confined (writable s) (loop_writes fuel origin table s upper lower stride t cur hs m).
Proof.
 assert (P:forall ip,permits (writable s) (push_at s ip)).
 { intros ip x X;left;change (frame s-8<=x<frame s-8+8) in X;pose proof(inside_frame s);lia. }
 induction fuel as [|gas IH];intros;[constructor|]. cbn [loop_writes];constructor;[apply P|].
 destruct (call_rows _ _ _) as [back|];[|constructor]. apply Forall_app;split.
 - apply tiles_confined;[lia|]. intros x X;left;change (frame s<=x<frame s+512) in X;pose proof(inside_frame s);lia.
 - apply Forall_app;split;[apply tiles_confined;[lia|intros;right;assumption]|].
   destruct (continuing _ _ _);[|constructor]. constructor;[apply P|].
   destruct (call_rows _ _ _);[apply IH|constructor].
Qed.

Definition events origin s upper lower table hs :=
 enter_writes origin s ++ loop_writes (S (Lanes.maximum (challenge_input s)))
    origin table s upper lower 64 0 0 hs (init_frame s).
Definition writes_correct pc code ro := forall slide s,
 placement s (slide+pc) (Z.of_nat(length code)) (slide+ro) ->
 let p:=expected pc ro in
 let ws:=events (slide+pc) s (slide+upper p) (slide+lower p)
   (group_constants (mem s) slide (keys p)) (fun _=>initial_at (mem s) (slide+ro)) in
 confined (writable s) ws /\ forall result,run pc code slide ro s=Some result ->
 forall x, after result x=WriteTrace.replay (mem s) ws x.

Theorem run_writes pc code ro :
 decode pc code=Some (expected pc ro) -> loads_match pc ro code=true -> writes_correct pc code ro.
Proof.
 intros Plan Loads slide s P. cbv zeta;unfold events;split.
 - apply Forall_app;split;[apply enter_confined|apply loop_confined].
 - intros result R x. unfold run in R;rewrite Loads,Plan in R.
   change (depth (expected pc ro)) with 704 in R.
   rewrite (Refinement.enter_frame _ _ _ _ P) in R.
   destruct (blocks _ _ _ _ _ _ _ _ _ _) as [out|] eqn:E;[|discriminate].
   injection R as <-.
   rewrite replay_app. assert (Init:forall y,WriteTrace.replay (mem s) (enter_writes (slide+pc) s) y=init_frame s y)
     by (intro y;exact (rows_memory (row_pc (slide+pc) SaveLength) (frame s+512) 3 _ (length_value s) y)).
   rewrite (replay_ext _ _ _ Init). apply loop_memory;exact E.
Qed.
