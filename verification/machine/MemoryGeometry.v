From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks FlatMemory.
Import ListNotations. Open Scope Z_scope.

(* Alignment is relative to a region; its base need not be vector-aligned. *)
Definition vector_in region length (a:pointer) :=
 fst a=region /\ 0<=snd a /\ snd a+64<=length /\ snd a mod 64=0.
Definition fits64 base len := 0<=base /\ base+len<=2^64.

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
Definition cell_inb r n(a:pointer) := Nat.eqb(fst a)r && (0<=?snd a) && (snd a+64<=?n) && (snd a mod 64=?0).
Lemma cell_inb_spec r n a : cell_inb r n a=true <-> vector_in r n a.
Proof. unfold cell_inb,vector_in;rewrite !andb_true_iff,Nat.eqb_eq,!Z.leb_le,Z.eqb_eq;tauto. Qed.
