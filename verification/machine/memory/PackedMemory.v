From Coq Require Import ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.Packed memory.FlatMemory.
Local Open Scope Z_scope.

Lemma row_byte rows state s row k :
 (row<rows)%nat -> (k<64)%nat ->
 let addr:=regs s 7%nat+64*Z.of_nat row+Z.of_nat k in
 mem (finish rows state s) addr =
 match stores state row with Some v=>value s (byte v k) | None=>mem s addr end.
Proof.
 intros R K addr;unfold finish;cbn [mem].
 replace (addr-regs s 7%nat) with (Z.of_nat k+Z.of_nat row*64) by (unfold addr;ring).
 set (off:=Z.of_nat k+Z.of_nat row*64).
 assert ((0<=?off) && (off<?64*Z.of_nat rows)=true)%bool as Fits by
   (apply andb_true_iff;split;[apply Z.leb_le|apply Z.ltb_lt];unfold off;lia).
 rewrite Fits;unfold off;rewrite Z.div_add,Z.mod_add,Z.div_small,Z.mod_small by lia.
 cbn [Z.add];now rewrite !Nat2Z.id.
Qed.

Lemma outside_rows rows state s x :
 ~(regs s 7%nat<=x<regs s 7%nat+64*Z.of_nat rows) ->
 mem (finish rows state s) x=mem s x.
Proof.
 intro O; unfold finish;cbn [mem];destruct (_ && _)%bool eqn:E;[|reflexivity].
 apply andb_true_iff in E as [L H];apply Z.leb_le in L;apply Z.ltb_lt in H;lia.
Qed.

(* Every in-bounds VMOVDQU64 store has exactly the effect of the common
   flat-memory write, including when it overwrites an earlier row. *)
Theorem store_writes_bytes rows state s row r x : (row<rows)%nat ->
 let base:=regs s 7%nat in
 mem (finish rows (step state (Store row r)) s) x =
 write_bytes (mem (finish rows state s)) (base+64*Z.of_nat row) 64
   (fun offset=>value s (byte (zmm state r) (Z.to_nat offset))) x.
Proof.
 intros R base.
 destruct (Z_lt_ge_dec x base), (Z_lt_ge_dec x (base+64*Z.of_nat rows));
 try (rewrite write_outside by lia;rewrite !outside_rows by (fold base;lia);reflexivity).
 set (q:=Z.to_nat ((x-base)/64));set (k:=Z.to_nat ((x-base) mod 64)).
 pose proof(Z.mod_pos_bound (x-base) 64 ltac:(lia)) as K.
 assert(Q:0<=(x-base)/64<Z.of_nat rows) by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 assert(E:x=base+64*Z.of_nat q+Z.of_nat k) by
   (unfold q,k;rewrite !Z2Nat.id by lia;pose proof(Z.div_mod (x-base) 64 ltac:(lia));lia).
 assert(Qn:(q<rows)%nat) by (unfold q;lia).
 assert(Kn:(k<64)%nat) by (unfold k;lia).
 rewrite E, row_byte by assumption;cbn [step stores];unfold update.
 destruct (Nat.eqb_spec q row) as [->|N].
 - rewrite write_at by lia;now rewrite Nat2Z.id.
 - rewrite write_outside by lia;symmetry;apply row_byte;assumption.
Qed.
