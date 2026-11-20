From Coq Require Import List ZArith Lia.
From Machine Require Import Instructions FlatMemory ByteMemory LinkedCalls MemoryGeometry WordBounds.
From Double4 Require Double4ABI Double4Spec.
From CachedAdd Require CachedAddABI.
Require Import LinkedBytes Callees Schedule Audit Object.
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
 assert (B:Double4Spec.input_bounds(buffer_words(mem(entry pad full))point)).
 { intros c j C J;apply Double4.Bounds.ready_loose;intros i I.
   change (0<=0<=2^51+2^20);lia. }
 assert (K:forall a addr,cache_bounds a (buffer_words(mem(entry pad full))addr)).
 { intros a addr i j I J;change(0<=0<2^52);lia. }
 destruct(Run _ _ _ _ _ _ _ (placed pad Pad) W eq_refl eq_refl eq_refl eq_refl
   B (K _ _) (K _ _) (K _ _)) as [out [R _]].
 eexists;exists out;exact R.
Qed.
