From Coq Require Import ZArith Bool Lia.
From Machine Require Import execution.Blocks execution.WordBounds memory.VectorBuffer.
From Curve25519 Require Import Radix51 Edwards.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.CachedAdd Require Import CachedAddABI CachedAddSpec Logical.
Local Open Scope Z_scope.

(* The cached-add logical machine has distinct point, affine-cache and scratch
   regions. Supply words only within the two ABI inputs. *)
Definition inputs incoming w a := Data (zmm incoming) (fun p j=>
 if (snd p <? 0) || negb (snd p mod 64 =? 0) then memory incoming p j else
 let i:=Z.to_nat (snd p/64) in
 if Nat.eqb (fst p) point then if Nat.ltb i 20 then cell w i j else memory incoming p j
 else if Nat.eqb (fst p) cached && Nat.ltb i 15 then cell a i j else memory incoming p j).
Definition advance incoming w a := words_at (memory (output_data true true (inputs incoming w a))) point.
Lemma advance_spec incoming w a : data_words incoming -> cache_bounds false w -> cache_bounds true a ->
 cached_add_spec true true w a (advance incoming w a).
Proof.
 intros [Regs Mem] W A.
 assert (Words:data_words (inputs incoming w a)).
 { split;[exact Regs|]. intros [r o] j J;cbn [inputs memory fst snd].
   destruct ((o <? 0) || negb (o mod 64 =? 0));[apply Mem;exact J|].
   destruct (Nat.eqb r point).
   - destruct (Nat.ltb_spec (Z.to_nat(o/64)) 20);[specialize(W _ j H J);unfold word64;lia|apply Mem;exact J].
   - destruct (_ && _)%bool eqn:C;[apply Bool.andb_true_iff in C as [_ C];apply Nat.ltb_lt in C;
     specialize(A _ j C J);unfold word64;lia|apply Mem;exact J]. }
 pose proof(arithmetic_contract true true _ Words) as H.
 eapply (spec_ext true true) in H;[exact H| | |reflexivity].
 all: intros i I;unfold words_at,vector_address,inputs;cbn [memory fst snd];
   rewrite Z.add_0_l, (proj2 (Z.ltb_ge (64*Z.of_nat(i/8)) 0) ltac:(lia)), Z.mul_comm, Z.mod_mul, Z.div_mul by lia.
 all: rewrite Nat2Z.id;unfold point,cached;cbn [Nat.eqb];
   pose proof(Nat.div_mod i 8 ltac:(lia));pose proof(Nat.mod_upper_bound i 8 ltac:(lia));
   unfold cell;repeat match goal with |- context [Nat.ltb ?x ?y] =>
   rewrite (proj2 (Nat.ltb_lt x y) ltac:(cbn in I;lia)) end;
   cbn [orb negb andb Z.eqb Pos.eqb];f_equal;lia.
Qed.
Lemma advance_correct incoming w a : data_words incoming -> cache_bounds false w -> cache_bounds true a ->
 cache_bounds false (advance incoming w a) /\ forall j P Q,(j<8)%nat ->
 represents_point true (point_values w j) P -> represents_cache (cache_values true a j) Q ->
 represents_point true (point_values (advance incoming w a) j) (plus P Q).
Proof.
 intros Words W A;destruct(advance_spec incoming w a Words W A) as [_ H].
 specialize(H (conj (split_cached_point _ W) A));split.
 - apply strict_split;intros c j C J;apply H;assumption.
 - intros j P Q J R S;eapply represents_equivalent;[|apply add_represents;eassumption].
   intros c C;rewrite coord_value by exact C;apply H;assumption.
Qed.
