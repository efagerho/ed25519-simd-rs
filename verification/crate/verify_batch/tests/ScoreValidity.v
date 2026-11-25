From Coq Require Import List ZArith Bool.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.MappedFetch.
From Ed25519Simd.VerifyBatch Require DalekBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition base:=65536.
Definition tables:=4096.
Definition image x:=if (base<=?x)&&(x<?base+Z.of_nat(length DalekBytes.symbol_bytes))
 then nth (Z.to_nat(x-base)) DalekBytes.symbol_bytes 0
 else if x=?tables+64 then 1 else if x=?tables+72 then 165 else 0.
Definition initial:=Cursor (base+478)
 (CPU (fun r=>if Nat.eqb r 7 then tables else 2^64-1) (fun _ _=>0) None image) None [].

Example damaged_scorer_reads_one_lane_as_the_validity_mask :
 match segment base DalekBytes.symbol_bytes 1 initial with
 | Some q=>ip q=base+482 /\ regs(machine q) 2%nat=1 /\ regs(machine q) 2%nat<>image(tables+72)
 | None=>False end.
Proof. vm_compute;repeat split;discriminate || reflexivity. Qed.
