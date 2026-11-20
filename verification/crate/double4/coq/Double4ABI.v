From Coq Require Import List ZArith Bool.
From Machine Require Export memory.VectorBuffer.
From Machine Require Import execution.Blocks.
Import ListNotations. Open Scope Z_scope.
From Ed25519Simd Require Export PointFrame.
Definition abi_layout := point_layout (fun _ _ => Unmapped).
Definition initial_control incoming pad bp := Control (At 0)
 (fun r => match r with
 | 4%nat => Ptr (scratch,1288+pad) | 5%nat => Int bp
 | 7%nat => Ptr (point,0) | _ => gpr incoming r end)
 (zf incoming) (fun a=>if ptr_eq a (scratch,1288+pad) then Some Caller else return_memory incoming a).
From Machine Require Import execution.WordBounds.
Definition valid_double4_entry (initial:state) pad :=
 permitted_padding pad /\
 (exists incoming bp,word64 bp /\ fst initial=initial_control incoming pad bp) /\
 data_words(snd initial).
