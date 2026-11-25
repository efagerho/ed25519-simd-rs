From Coq Require Import List ZArith.
From Machine Require Import execution.MaskTrace.
From Curve25519 Require Import Edwards Torsion group.Affine group.Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.SmallOrder Require Import Program.
Local Open Scope Z_scope.

Definition readable_rows (base:nat) := if Nat.eqb base 7 then 10%nat else 0%nat.
Definition inputs (p:nat->Z) (j base row:nat) := cell p row j.
Definition bounded p := forall row j, (row<10)%nat -> (j<8)%nat -> 0 <= cell p row j < 2^52.

Definition lane_result mask j q :=
  let set := Z.testbit mask (Z.of_nat j) = true in
  (set <-> torsion_roots (cx q) (cy q)) /\
  (forall P, represents_xyz q P -> (set <-> multiple 8 P = identity)).

(* Instruction budget and maximum private stack depth in bytes. *)
Definition raw entry other pad:=linked_writes 350 24 readable_rows pad entry code other helper.
Definition run_at entry other pad := erase_writes (raw entry other pad).
Lemma raw_result entry other pad input initial :
 result (raw entry other pad) input initial=result (run_at entry other pad) input initial.
Proof. unfold run_at;exact (eq_sym(erase_result _ _ _)). Qed.

(* An execution starts at the linked entry, with read-only X/Y at RDI.
   The second symbol supplies the field multiplication, root tests and
   constants reached by PC-relative instructions in that same execution. *)
Record small_order_contract (entry : Z) (entry_bytes : list Z)
                            (other : Z) (other_bytes : list Z) : Prop := {
  entry_binding : bytes code = entry_bytes /\ well_formed code = true;
  helper_binding : bytes helper = other_bytes /\ well_formed helper = true;
  linked_regions :
    0 <= entry /\ entry + Z.of_nat (length entry_bytes) < 2^64 /\
    0 <= other /\ other + Z.of_nat (length other_bytes) < 2^64 /\
    (entry + Z.of_nat (length entry_bytes) <= other \/ other + Z.of_nat (length other_bytes) <= entry);
  write_footprint : forall pad, (pad<4)%nat -> stack_writes 24 pad (raw entry other pad);
  run_correct : forall pad p initial, (pad<4)%nat -> bounded p ->
    exists mask,
      result (run_at entry other pad) (inputs p) initial = Some mask /\
      0 <= mask < 256 /\
      forall j, (j<8)%nat -> lane_result mask j (point_values p j)
}.

From Coq Require Import Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.WordSemantics execution.ScalarWords
 execution.MaskStores execution.MaskReturn memory.ByteMemory memory.WriteTrace memory.MemoryGeometry.
From Machine Require memory.FlatMemory.

Definition point_at p:=buffer_words (mem(machine p)) (LinkedCalls.regs(machine p) 7%nat).
Definition execute slide entry other pad p ks:=
 MaskReturn.execute slide pad (raw entry other pad) (inputs(point_at p)) p ks.
Definition extent base n x:=base<=x<base+n.
Definition reads slide entry (bs:list Z) other (hs:list Z) p x:=extent (slide+entry) (Z.of_nat(length bs)) x \/
 extent (slide+other) (Z.of_nat(length hs)) x \/ extent (LinkedCalls.regs(machine p) 7%nat) 640 x.
Record placement slide entry bs other hs pad p:Prop:=Placement {
 at_entry:ip p=slide+entry; aligned:LinkedCalls.regs(machine p) 4%nat mod 64=MaskStores.origin pad;
 stack_range:fits64 (LinkedCalls.regs(machine p) 4%nat-24) 32;
 point_range:fits64 (LinkedCalls.regs(machine p) 7%nat) 640;
 images:mapped (mem(machine p)) (slide+entry) bs /\ mapped (mem(machine p)) (slide+other) hs;
 separate:forall x,reads slide entry bs other hs p x -> ~(LinkedCalls.regs(machine p) 4%nat-24<=x<LinkedCalls.regs(machine p) 4%nat)
}.

(* Every prefix sees the original linked instructions, constants and X/Y.
   Input b=7 covers ten rows. The eight lane words have their actual byte
   addresses in the RDI buffer at the call site. *)
Definition prefix_inputs slide entry bs other hs pad p:=
 forall pref suffix,MaskReturn.saved_log slide pad (raw entry other pad) (inputs(point_at p)) p=pref++suffix ->
 let m:=replay (mem(machine p)) pref in
 mapped m (slide+entry) bs /\ mapped m (slide+other) hs /\
 MaskReturn.source_rows readable_rows (with_words (machine p) (LinkedCalls.regs(machine p)) m) (inputs(point_at p)).

Lemma prefixes slide entry bs other hs pad p :
 placement slide entry bs other hs pad p ->
 confined (fun x=>LinkedCalls.regs(machine p) 4%nat-24<=x<LinkedCalls.regs(machine p) 4%nat)
   (MaskReturn.saved_log slide pad (raw entry other pad) (inputs(point_at p)) p) ->
 prefix_inputs slide entry bs other hs pad p.
Proof.
 intros P W pref suffix Eq;rewrite Eq in W;apply Forall_app in W as [Pre _];cbv zeta.
 pose proof(WriteTrace.frame _ _ Pre (mem(machine p))) as M.
 destruct(images _ _ _ _ _ _ _ P) as [Main Helper].
 assert (Keep:forall x,reads slide entry bs other hs p x -> replay (mem(machine p)) pref x=mem(machine p) x).
 { intros x X;apply M,(separate _ _ _ _ _ _ _ P x X). }
 split;[intros j J;rewrite Keep;[apply Main,J|left;unfold extent;lia]|split].
 - intros j J;rewrite Keep;[apply Helper,J|right;left;unfold extent;lia].
 - intros b i j I J;unfold readable_rows in I;destruct(Nat.eqb_spec b 7) as [->|];[|lia].
   set (a:=LinkedCalls.regs(machine p) 7%nat);destruct(point_range _ _ _ _ _ _ _ P) as [L H];fold a in L,H.
   unfold inputs,cell,point_at,buffer_words;cbn [mem LinkedCalls.regs with_words];fold a.
   rewrite Nat2Z.inj_add,Nat2Z.inj_mul.
   rewrite word_fits by (unfold WordBounds.word64;lia).
   replace (a+8*(Z.of_nat i*Z.of_nat 8+Z.of_nat j)) with (a+64*Z.of_nat i+8*Z.of_nat j) by ring.
   symmetry;apply LinkedCalls.preserved_read with (outside:=reads slide entry bs other hs p);[exact Keep|].
   intros k K;right;right;unfold extent;fold a;change (0<=k<8) in K;lia.
Qed.

Theorem machine_return slide entry bs other hs pad p ks :
 small_order_contract entry bs other hs -> (pad<4)%nat -> placement slide entry bs other hs pad p ->
 LinkedCalls.well_formed(machine p) -> bounded(point_at p) ->
 exists q bank mask,execute slide entry other pad p ks=Some(q,bank) /\
 MaskReturn.returned slide pad 24 (raw entry other pad) (inputs(point_at p)) p mask q /\
 prefix_inputs slide entry bs other hs pad p /\ 0<=mask<256 /\ LinkedCalls.regs(machine q) 0%nat=mask /\
 forall j,(j<8)%nat -> lane_result mask j (point_values (point_at p) j).
Proof.
 intros C Pad P W B;pose proof(write_footprint _ _ _ _ C pad Pad) as Bound.
 destruct(run_correct _ _ _ _ C pad (point_at p) (vectors(machine p)) Pad B) as [mask [Run [Byte Bits]]].
 pose proof(eq_trans (raw_result entry other pad (inputs(point_at p)) (vectors(machine p))) Run) as RawRun.
 destruct(MaskReturn.checked slide pad 24 (raw entry other pad) (inputs(point_at p)) p ks mask Bound W RawRun)
   as [q [bank [End Ret]]];exists q,bank,mask;split;[exact End|split;[exact Ret|split]].
 - apply prefixes;[exact P|exact (MaskReturn.stores _ _ _ _ _ _ _ _ Ret)].
 - split;[exact Byte|];split;[rewrite (MaskReturn.eax _ _ _ _ _ _ _ _ Ret);apply word_fits;unfold WordBounds.word64;lia|exact Bits].
Qed.
