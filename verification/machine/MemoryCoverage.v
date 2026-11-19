From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory ExecutionProperties.
Import ListNotations. Open Scope Z_scope.

Definition written_vectors es :=
 flat_map (fun e=>match e with Write _ a=>[a] | _=>[] end) es.
Definition covers_vectors region count es :=
 forallb (fun i=>existsb (ptr_eq (region,64*Z.of_nat i))
   (written_vectors es)) (seq 0 count).

(* A checked vector footprint covers every byte, including the last byte. *)
Theorem output_trace_covered region count es :
 covers_vectors region count (data_effects es)=true ->
 forall loc k, 0<=k<64*Z.of_nat count ->
 writes_at loc es (origin loc region+k).
Proof.
 intros W loc k K; set (i:=Z.to_nat(k/64)).
 assert (Q:0<=k/64<Z.of_nat count) by
   (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
 assert (Index:Z.of_nat i=k/64) by (unfold i; rewrite Z2Nat.id; lia).
 unfold covers_vectors in W; rewrite forallb_forall in W.
 specialize (W i ltac:(apply in_seq; lia)).
 apply existsb_exists in W as [a [Member A]]; apply ptr_eq_true in A; subst a.
 unfold written_vectors in Member; apply in_flat_map in Member as [op [Op M]].
 destruct op; try contradiction; destruct M as [Eq|[]]; subst a.
 unfold data_effects in Op; apply in_flat_map in Op as [e [Member Op]].
 destruct e as [op|a t|a t]; try contradiction; destruct Op as [Eq|[]]; subst op.
 exists (DataOp(Write src(region,64*Z.of_nat i))), (VectorCell(region,64*Z.of_nat i)).
 split; [exact Member|]; split; [reflexivity|].
 unfold inside,cell_address,address_of; cbn [fst snd width].
 pose proof (Z.div_mod k 64 ltac:(lia)); pose proof (Z.mod_pos_bound k 64 ltac:(lia)); lia.
Qed.
