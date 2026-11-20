From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import Field Edwards.
From Curve25519.group Require Import PrimeField Representation.
From Curve25519.group Require Affine.
From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions memory.FlatMemory memory.ByteMemory execution.LinkedCalls memory.MemoryGeometry execution.WordBounds.
From Ed25519Simd.Double4 Require Double4ABI Double4Spec.
From Ed25519Simd.CachedAdd Require CachedAddABI.
From Ed25519Simd.LadderStep Require Import LinkedBytes Callees Schedule Audit Object.
Import ListNotations. Open Scope Z_scope.

(* Instantiate the public theorem for both T modes and every stack
   alignment. Place the linked image away from the data regardless of its
   original link address. *)
Local Definition slide := 2^36-wrapper_pc.
Local Definition scratch := 2^40.
Local Definition point := 2^41.
Local Definition cache := 2^42.
Local Definition entry pad full := CPU
 (fun r => match r with
  | 2%nat => CachedAddABI.flag_word full | 4%nat => scratch+1320+pad
  | 6%nat => cache | 7%nat => point | _ => 2^64-1 end)
 (fun _ _=>2^64-1) None (fun _=>0).

Local Lemma placed pad : Double4ABI.permitted_padding pad -> placement_ok slide scratch pad point cache.
Proof.
 intros P;constructor;try exact P;try reflexivity.
 all: try (intros pc size [E|[E|[E|[]]]];inversion E;subst;clear E).
 all: destruct P as [<-|[<-|[<-|[<-|[]]]]];vm_compute;intuition discriminate.
Qed.

Example all_entry_modes_execute pad full : Double4ABI.permitted_padding pad ->
 exists ip out, runs (dispatch (slide+double4_pc)(slide+cached_pc) scratch pad)
                     slide wrapper_pc program (entry pad full) ip out.
Proof.
 intro Pad;destruct assembled_ladder_step_correct as [_[_[_[_ Run]]]].
 assert (W:well_formed (entry pad full)).
 { assert(0<=pad<=48) by (destruct Pad as[<-|[<-|[<-|[<-|[]]]]];lia).
   split;[|split];try (intros;unfold word64,scratch;cbn [entry vectors];lia).
   - intros [|[|[|[|[|[|[|[|r]]]]]]]];destruct full;unfold word64,scratch,point,cache;
     cbn [entry regs CachedAddABI.flag_word];unfold scratch,point,cache;lia.
   - intros x;change(0<=0<256);lia. }
 assert (B:Wide51.loose_xyz(buffer_words(mem(entry pad full))point)).
 { intros c j C J;apply Radix51.ready_loose;intros i I.
   change (0<=0<=2^51+2^20);lia. }
 assert (K:forall a addr,cache_bounds a (buffer_words(mem(entry pad full))addr)).
 { intros a addr i j I J;change(0<=0<2^52);lia. }
 destruct(Run _ _ _ _ _ _ _ (placed pad Pad) W eq_refl eq_refl eq_refl eq_refl
   B (K _ _) (K _ _) (K _ _)) as [out [R _]].
 eexists;exists out;exact R.
Qed.

(* RFC 8032 section 5.1, table 1. *)
Local Definition base_x := 15112221349535400772501151409588531511454012693041857206046113283949847762202.
Local Definition base_y := 46316835694926478169428394003475163141307993866256225615783033603165251855960.
Local Definition curve_d := 37095705934669439343138083508754565189542113879843219016388785533085940283555.
Local Definition B := Affine.Point (residue base_x) (residue base_y)
  ltac:(apply GZnZ.zirr; vm_compute; reflexivity).
Local Definition cache_fixture x y z zz := CachedCoordinates
  (((y-x)*z) mod prime) (((y+x)*z) mod prime) ((2*curve_d*x*y*z) mod prime) zz.

Local Ltac check_fixture :=
 repeat apply conj; first [apply GZnZ.zirr; vm_compute; reflexivity | discriminate].

(* The initial T is discarded. Odd is B with scale 3, Base is -B in
   affine form, and Even is the identity with scale 5. *)
Example base_point_ladder full :
 represents_point full
   (ladder_formula full (Coordinates base_x base_y 1 0)
     (cache_fixture base_x base_y 3 (Some 6))
     (cache_fixture (-base_x) base_y 1 None) (cache_fixture 0 1 5 (Some 10)))
   (Affine.multiple 271 B).
Proof.
 assert (Sum : ladder_sum B B (Affine.negative B) Affine.identity = Affine.multiple 271 B).
 { unfold ladder_sum. rewrite (Affine.plus_comm _ Affine.identity), Affine.plus_identity.
   rewrite <-Affine.multiple_add.
   change (Affine.plus (Affine.plus B (Affine.multiple 271 B)) (Affine.negative B) = Affine.multiple 271 B).
   rewrite (Affine.plus_comm B (Affine.multiple 271 B)), Affine.plus_assoc, Affine.plus_negative.
   now rewrite Affine.plus_comm, Affine.plus_identity. }
 rewrite <-Sum. apply ladder_represents.
 - unfold represents_xyz. check_fixture.
 - exists (residue 3). check_fixture.
 - exists (residue 1). check_fixture.
 - exists (residue 5). check_fixture.
Qed.
