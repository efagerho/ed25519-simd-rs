From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks memory.MemoryTrace execution.ExecutionProperties.
Import ListNotations.
Open Scope Z_scope.

(* One flat address space for vector data, saved PCs and all surrounding bytes. *)
Definition bytes := Z -> Z.
Record placement := Placement { origin : nat -> Z; code_base : Z; caller_pc : Z }.
Definition address_of loc (a : pointer) := origin loc (fst a) + snd a.
Definition pc_word loc t := match t with At n => code_base loc + n | Caller => caller_pc loc | SavedWord n => n end.
Definition word_byte (word index : Z) := (word / 2^(8*index)) mod 256.
Definition vector_byte (v : vector) k := word_byte (v (Z.to_nat (k/8))) (k mod 8).

Inductive cell := VectorCell (a : pointer) | ReturnSlot (a : pointer).
Definition cell_address loc s := address_of loc (match s with VectorCell a | ReturnSlot a => a end).
Definition width s : Z := match s with VectorCell _ => 64 | ReturnSlot _ => 8 end.
Definition disjoint x n y m := x+n <= y \/ y+m <= x.

Definition destination e := match e with
 | DataOp (Write _ a) => Some (VectorCell a) | Push a _ => Some (ReturnSlot a) | _ => None end.
Definition writes_only (allowed : cell -> Prop) es :=
 Forall (fun e => match destination e with Some w => allowed w | None => True end) es.
Definition inside loc s x := cell_address loc s <= x < cell_address loc s + width s.
Definition writes_at loc es x := exists e s, In e es /\ destination e = Some s /\ inside loc s x.

Definition cell_byte loc d (m : slots) s k := match s with
 | VectorCell a => Some (vector_byte (memory d a) k)
 | ReturnSlot a => option_map (fun t => word_byte (pc_word loc t) k) (m a)
 end.
Definition agrees loc (tracked : cell -> Prop) d m (flat : bytes) :=
 forall s k b, tracked s -> 0 <= k < width s ->
 cell_byte loc d m s k = Some b -> flat (cell_address loc s + k) = b.

Definition write_bytes (flat : bytes) start len (payload : Z -> Z) x :=
 if (start <=? x) && (x <? start+len) then payload (x-start) else flat x.
Definition write_event loc e d flat := match e with
 | DataOp (Write r a) => write_bytes flat (address_of loc a) 64 (vector_byte (fun j => zmm d j r))
 | Push a t => write_bytes flat (address_of loc a) 8 (word_byte (pc_word loc t))
 | _ => flat end.
Definition next_data p d e := match e with DataOp op => apply_effect p d op | _ => d end.

Fixpoint replay p loc es d (flat : bytes) := match es with
 | [] => flat
 | e::rest => replay p loc rest (next_data p d e) (write_event loc e d flat)
 end.

Lemma write_at flat start n val k : 0<=k<n ->
 write_bytes flat start n val (start+k) = val k.
Proof. intro K; unfold write_bytes.
 rewrite (proj2 (Z.leb_le start (start+k)) ltac:(lia)), (proj2 (Z.ltb_lt (start+k) (start+n)) ltac:(lia)).
 now replace (start+k-start) with k by lia. Qed.
Lemma write_outside flat start n val x : ~ (start<=x<start+n) ->
 write_bytes flat start n val x = flat x.
Proof. intro H; unfold write_bytes. destruct (_ && _)%bool eqn:B; [|reflexivity].
 apply Bool.andb_true_iff in B as [A B]; apply Z.leb_le in A; apply Z.ltb_lt in B; lia. Qed.

Definition separated loc (allowed tracked : cell -> Prop) :=
 forall w s, allowed w -> tracked s -> w=s \/
   disjoint (cell_address loc w) (width w) (cell_address loc s) (width s).

Lemma different_ptr a b : a <> b -> ptr_eq a b = false.
Proof. intro N. destruct (ptr_eq a b) eqn:E; auto. apply ptr_eq_true in E; contradiction. Qed.
Lemma same_ptr a : ptr_eq a a = true.
Proof. destruct a; unfold ptr_eq; cbn; now rewrite Nat.eqb_refl,Z.eqb_refl. Qed.

Lemma event_agrees p loc allowed tracked d m flat e :
 separated loc allowed tracked -> agrees loc tracked d m flat ->
 (match destination e with Some w => allowed w | None => True end) ->
 agrees loc tracked (next_data p d e) (update_slots m e) (write_event loc e d flat).
Proof.
 intros Sep H W s k b S K V. destruct e as [op|a t|a t]; [destruct op| |];
 try solve [apply (H s k b S K); destruct s; exact V].
 - destruct (Sep (VectorCell a) s W S) as [<-|D].
   + cbn [cell_byte next_data apply_effect memory] in V. rewrite same_ptr in V.
     inversion V; subst. apply write_at; exact K.
   + cbn [write_event]. rewrite write_outside by
       (destruct s; unfold disjoint,cell_address in *; cbn [width] in *; lia).
     apply (H s k b S K). destruct s as [q|q]; [|exact V].
     cbn [cell_byte next_data apply_effect memory] in V.
     rewrite different_ptr in V; [exact V|intros ->; cbn [cell_address width] in D; unfold disjoint in D; lia].
 - destruct (Sep (ReturnSlot a) s W S) as [<-|D].
   + cbn [cell_byte update_slots] in V. rewrite same_ptr in V. inversion V; subst.
     apply write_at; exact K.
   + cbn [write_event]. rewrite write_outside by
       (destruct s; unfold disjoint,cell_address in *; cbn [width] in *; lia).
     apply (H s k b S K). destruct s as [q|q]; [exact V|].
     cbn [cell_byte update_slots] in V.
     rewrite different_ptr in V; [exact V|intros ->; cbn [cell_address width] in D; unfold disjoint in D; lia].
Qed.

Lemma replay_agrees p loc allowed tracked es d m flat :
 separated loc allowed tracked -> writes_only allowed es -> agrees loc tracked d m flat ->
 agrees loc tracked (effects p (data_effects es) d) (fold_left update_slots es m) (replay p loc es d flat).
Proof.
 intros Sep Safe. revert d m flat. induction Safe as [|e tail W Safe IH]; intros d m flat H.
 - exact H.
 - specialize (IH (next_data p d e) (update_slots m e) (write_event loc e d flat)
                  (event_agrees _ _ _ _ _ _ _ _ Sep H W)).
   destruct e; exact IH.
Qed.

Lemma replay_frame p loc es d flat x :
 ~ writes_at loc es x -> replay p loc es d flat x = flat x.
Proof.
 revert d flat; induction es as [|e rest IH]; intros d flat N; [reflexivity|].
 cbn [replay]. rewrite IH by (intros [f [s [I H]]]; apply N; exists f,s; split; [now right|exact H]).
 assert (Outside: forall s, destination e = Some s -> ~ inside loc s x).
 { intros s E K. apply N; exists e,s; split; [now left|auto]. }
 destruct e as [op|a t|a t]; [destruct op| |]; try reflexivity; apply write_outside;
   first [exact (Outside (VectorCell a) eq_refl) | exact (Outside (ReturnSlot a) eq_refl)].
Qed.
