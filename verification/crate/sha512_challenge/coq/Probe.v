From Coq Require Import List NArith ZArith.
From Ed25519Simd.Sha512Challenge Require Import Rounds Transpose.
Import ListNotations. Local Open Scope nat_scope.

(* Differential probe for the new round and byte-shuffle operations. The
   native harness starts with independent input words for all eight lanes. *)
Definition round_probe := [Ror 3 0 39; Tern Parity 0 1 2; Tern Choose 1 2 3; Tern Majority 2 3 0].
Definition observed_round (input:list N) r j :=
  value (fun reg=>nth (8*reg+j) input 0%N) (fun _=>0%N)
    (fold_left Rounds.step round_probe Reg r).
Definition observed_shuffle (data mask:list nat) :=
  let regs r i:=if Nat.eqb r 0 then Input 0 i else Literal (nth i mask 0) in
  map (fun i=>match Transpose.step regs (ShuffleBytes 2 0 1) 2 i with
     | Input _ k=>nth k data 0 | Literal v=>v | Unknown=>256 end) (seq 0 64).
