From Coq Require Import List NArith ZArith.
From Ed25519Simd.Sha512Challenge Require Import Rounds Compression Image.
From Mutations Require Code.
Local Open Scope nat_scope.

(* Bind the changed instruction stream as well, then execute it. An incoming
   e=1 and zero schedule, K and other state words expose the wrong Sigma1. *)
Definition damage ins := match ins with
 | Ror 25 20 14 => Ror 25 20 15 | _ => ins end.
Definition first_round := map damage (program true 0).
Definition first_bytes := flat_map Rounds.encode first_round.
Example changed_round_is_linked :
 firstn (length first_bytes) (skipn (offset Expanded listing) Code.symbol_bytes) = first_bytes.
Proof. vm_compute; reflexivity. Qed.
Definition incoming r := if Nat.eqb r 20 then 1%N else 0%N.
Example changed_round_is_wrong :
 view 1 (fun r=>value incoming (fun _=>0%N) (fold_left step first_round Reg r)) <>
 scheduled_round (view 0 incoming) (0%N,0%N).
Proof. vm_compute; discriminate. Qed.
