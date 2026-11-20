From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.IndexedLoads execution.Packed.
From Ed25519Simd.StageRound Require Import Program Audit.
Import ListNotations. Local Open Scope nat_scope.

Definition direct_term r n := W64 (Plus (G r) (K (Z.of_nat n))).
Definition digit_term k l := direct_term (match k with Base=>1 | _=>8 end)
  (64*l + match k with Odd=>1 | _=>0 end).
Definition ptr_term l := direct_term 6 (8*l).
Definition key_calc d := W32 (Times (W32 (Bxor (W32 (Band d (K 15))) (K 7))) (K 160)).
Definition base_calc d :=
  let hi:=W32 (Band (W32 (Right (W32 (W32 d)) 4)) (K 240)) in
  W32 (Times (W32 (Bxor (W32 (Bor (W32 (Band d (K 15))) hi)) (K 136))) (K 120)).
Definition table_term k l := match k with
| Base => Plus (G 2) (base_calc (Read 2 (digit_term k l)))
| _ => W64 (Plus (key_calc (Read 1 (digit_term k l))) (Read 8 (ptr_term l))) end.
Definition bias k := match k with Base=>0 | _=>160 end.
Definition tile_addr k l col := W64 (Plus (table_term k l) (K (Z.of_nat (bias k+8*col)))).
Definition tile_start k c := match k with
| Base => if c <? 8 then 0 else if c <? 12 then 8 else 11
| _ => if c <? 4 then 0 else if c <? 8 then 4 else if c <? 16 then 8 else 16 end.
Definition word_term k l c := let t:=tile_start k c in
  Read 8 (Plus (tile_addr k l t) (K (Z.of_nat (8*(c-t))))).

Definition load_state k := IndexedLoads.summary (load_block k).
Definition route_state k := fold_left Packed.step (route k) Packed.initial.
Definition check_byte k c i := match stores (route_state k) (first_row k+c) with
  | Some v => match byte v i with
    | Octet (Initial r j) b => (b =? i mod 8) &&
        term_beq (IndexedLoads.vec (load_state k) r j) (word_term k (i/8) c)
    | _ => false end
  | None => false end.
Definition check_route k :=
  forallb (fun c=>forallb (check_byte k c) (seq 0 64)) (seq 0 (columns k)).
Local Lemma checked k : check_route k=true.
Proof. destruct k;vm_compute;reflexivity. Qed.

Lemma routed k c i : c<columns k -> i<64 ->
  exists v r j, stores (route_state k) (first_row k+c)=Some v /\
    byte v i=Octet (Initial r j) (i mod 8) /\
    IndexedLoads.vec (load_state k) r j=word_term k (i/8) c.
Proof.
 intros C I;pose proof (checked k) as H; unfold check_route in H.
 apply (proj1 (forallb_forall _ _)) with (x:=c) in H;[|apply in_seq;lia].
 apply (proj1 (forallb_forall _ _)) with (x:=i) in H;[|apply in_seq;lia].
 unfold check_byte in H; destruct (stores _ _) as [v|] eqn:S;[|discriminate].
 destruct (byte v i) as [| | | | | | |e b| |] eqn:E;try discriminate.
 destruct e as [| |r j| | | | | | |];try discriminate.
 apply andb_true_iff in H as [B T];apply Nat.eqb_eq in B;subst.
 exists v,r,j;repeat split;auto using internal_term_dec_bl.
Qed.

Definition outside_check k row := if (first_row k <=? row) && (row <? first_row k+columns k)
  then true else match stores (route_state k) row with None=>true | _=>false end.
Lemma untouched k row : row<55 -> ~(first_row k<=row<first_row k+columns k) ->
  stores (route_state k) row=None.
Proof.
 intros R N; assert (H:forallb (outside_check k) (seq 0 55)=true)
 by (destruct k;vm_compute;reflexivity).
 apply (proj1 (forallb_forall _ _)) with (x:=row) in H;[|apply in_seq;lia].
 unfold outside_check in H. destruct (_ && _) eqn:A.
 - apply andb_true_iff in A as [F T];apply Nat.leb_le in F;apply Nat.ltb_lt in T;lia.
 - destruct (stores _ _);congruence.
Qed.

Definition lane_reads k l : list (term*nat) := match k with
| Base => [(digit_term k l,2);(tile_addr k l 0,64);(tile_addr k l 8,32);(tile_addr k l 11,32)]
| _ => [(digit_term k l,1);(ptr_term l,8);(tile_addr k l 0,32);(tile_addr k l 4,32);
        (tile_addr k l 8,64);(tile_addr k l 16,32)] end.
Lemma all_reads k : rev (loads (load_state k)) = flat_map (lane_reads k) (seq 0 8).
Proof. destruct k;vm_compute;reflexivity. Qed.

Definition kept := [1;2;3;4;5;6;7;8;12;13;14;15].
Lemma register_trace k r : In r kept ->
  gp (load_state k) r=G r /\ acc (route_state k)=Acc.
Proof.
 assert (H:forallb (fun i=>term_beq (gp (load_state k) i) (G i)) kept=true)
 by (destruct k;vm_compute;reflexivity).
 intros I;apply (proj1 (forallb_forall _ _)) with (x:=r) in H;auto.
 split;[now apply internal_term_dec_bl|destruct k;reflexivity].
Qed.
