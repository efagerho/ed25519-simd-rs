From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks MemoryTrace.
Require Import Program Double4ABI Double4Memory Round FrameProof.
Import ListNotations. Open Scope Z_scope.
Definition point_reads_xyz a := negb(Nat.eqb(fst a)point) || ((0<=?snd a)&&(snd a+64<=?960)).
Theorem read_footprint_checked : forallb point_reads_xyz(flat_map(read_addresses double4_program)expected_path)=true.
Proof. vm_compute;reflexivity. Qed.
Theorem input_t_unread_correct initial pad final : valid_double4_entry initial pad ->
 returns double4_program abi_layout initial final ->input_t_unread double4_program initial final.
Proof.
 destruct initial as[c d];intros[Pad[[incoming[bp[BP Init]]]_]]Returns;cbn [fst] in Init;subst c.
 pose proof(frame_checked incoming pad bp Pad BP)as Frame.
 destruct(record_path 200 double4_program abi_layout(initial_control incoming pad bp))as[[last es]|]eqn:R;[|discriminate].
 destruct(record_path_sound _ _ _ _ _ _ R)as[P _].
 pose proof(path_returns _ _ _ _ _ _ P d)as Ends.
 pose proof(return_unique _ _ _ _ _ Returns Ends)as ->.
 exists 200%nat,es;split;[exact R|].
 pose proof(control_path_checked incoming pad bp Pad)as Check;rewrite P in Check.
 cbn [observe_path] in Check;injection Check as _ _ Ops.
 rewrite Ops;intros a Member Region.
 pose proof read_footprint_checked as Read;rewrite forallb_forall in Read;specialize(Read a Member).
 unfold point_reads_xyz in Read;rewrite Region,Nat.eqb_refl in Read;cbn in Read.
 apply andb_true_iff in Read as[L U];apply Z.leb_le in L;apply Z.leb_le in U;auto.
Qed.
