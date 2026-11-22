From Coq Require Import List ZArith Bool Lia.
From Ed25519Simd.CachedAdd Require Object ObjectBytes.
From Ed25519Simd.Decode Require Import Kernels Program DecoderBytes HelperBytes.
From Ed25519Simd.KeyTable Require Import Fields Frame Image Rows Audit Correct ObjectBytes CachedBytes.
Import ListNotations. Local Open Scope Z_scope.

Theorem assembled_key_table_correct : key_table_contract
 ObjectBytes.address ObjectBytes.symbol_bytes DecoderBytes.address DecoderBytes.symbol_bytes
 HelperBytes.address HelperBytes.symbol_bytes CachedBytes.address CachedBytes.symbol_bytes.
Proof.
 constructor.
 - unfold image. split;[apply blocks_checked;vm_compute;reflexivity|].
   split;[vm_compute;reflexivity|]. split;[repeat constructor;vm_compute;discriminate|].
   vm_compute;split;reflexivity.
 - vm_compute;split;reflexivity.
 - exact Object.assembled_cached_add_correct.
 - exists code;split;[vm_compute;repeat split;reflexivity|].
   split;[apply frame_ok;vm_compute;reflexivity|].
   split;[apply field_frame_ok;vm_compute;reflexivity|]. split.
   + assert (B:forallb (fun v=>(fst v<?5)%nat || ((10<=?fst v)&&(fst v<?15))%nat)
                       (Kernels.carry code)=true) by reflexivity.
     intros v H;apply forallb_forall with (x:=v) in B;auto.
     rewrite orb_true_iff,andb_true_iff,!Nat.ltb_lt,Nat.leb_le in B;exact B.
   + intros count flat sp point_ptr table_ptr incoming N Place _ Scratch W.
     destruct(frame_geometry sp (proj1 Place)) as [Align [Depth _]].
     split;[exact Align|split;[exact Depth|]]. apply result_correct;auto.
     split;[vm_compute;reflexivity|destruct op;vm_compute;reflexivity].
Qed.
