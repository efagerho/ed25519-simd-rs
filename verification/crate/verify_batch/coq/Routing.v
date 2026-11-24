(* The descriptor transpose operates on qwords. A token (row,field) is the
   original source of a qword, independent of its memory contents. *)
From Coq Require Import List ZArith Lia.
From Machine Require Import isa.IndexedLoad isa.Move execution.IndexedLoads.
Import ListNotations. Local Open Scope nat_scope.

Definition row r := Addr 3 false (40*Z.of_nat r)%Z.
Definition transpose :=
 [LoadY 0 (row 0);LoadY 1 (row 1);LoadY 2 (row 4);LoadY 3 (row 5);
  InsertY 0 0 (row 2) true;InsertY 1 1 (row 3) true;
  InsertY 2 2 (row 6) true;InsertY 3 3 (row 7) true;
  UnpackWords false 4 0 1;UnpackWords true 5 0 1;
  UnpackWords false 6 2 3;UnpackWords true 7 2 3;
  ShuffleWords 0 4 6 0x88;ShuffleWords 1 5 7 0x88;
  ShuffleWords 2 4 6 0xdd;ShuffleWords 3 5 7 0xdd].
Definition lane_term field j := vec (summary transpose) field j.
Definition field_read j f := Read 8 (Plus (effective G (row j)) (K (8*Z.of_nat f))).
Lemma transpose_reads f j : f<4 -> j<8 -> lane_term f j=field_read j f.
Proof.
 intros F J. do 4 (destruct f as [|f]; [
   do 8 (destruct j as [|j]; [reflexivity|]);lia|]);lia.
Qed.
Definition routed f j := match lane_term f j with
 | Read 8 (Plus (W64 (Plus (G 3) (K disp))) (K off))=>(Z.to_nat(disp/40),Z.to_nat(off/8))
 | _=>(8,4) end.
Lemma transpose_fields f j : f<4 -> j<8 -> routed f j=(j,f).
Proof.
 intros F J;unfold routed;rewrite transpose_reads by assumption. unfold field_read,row,effective;cbn [indexed base displacement].
 rewrite !(Z.mul_comm _ (Z.of_nat _)), !Z.div_mul by lia;now rewrite !Nat2Z.id.
Qed.
Definition route_bytes := flat_map IndexedLoad.encode transpose ++
 flat_map (fun f=>Move.encode_store f 4 (512+64*Z.of_nat f)) (seq 0 4).

(* The scalar tail loop copies a 32-byte payload and its following index.
   The source pointer advances only while it is below the last record. *)
Fixpoint tail_sources fuel src last :=
  match fuel with 0=>[] | S n=>src::tail_sources n (if src <? last then S src else src) last end.
Definition source_lane active j :=
  if active <? 8 then nth j (tail_sources 8 0 (active-1)) 0 else j.
Lemma source_lane_live active j : 0<active<=8 -> j<active -> source_lane active j=j.
Proof.
  intros A J. do 9 (destruct active as [|active]; [
    do 8 (destruct j as [|j]; [try reflexivity;lia|]);lia|]);lia.
Qed.
Lemma source_lane_range active j : 0<active<=8 -> j<8 -> source_lane active j<active.
Proof.
  intros A J. do 9 (destruct active as [|active]; [
    do 8 (destruct j as [|j]; [cbv;lia|]);lia|]);lia.
Qed.
