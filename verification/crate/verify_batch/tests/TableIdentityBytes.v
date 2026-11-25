From Coq Require Import List ZArith Bool.
From Machine Require Import execution.LinkedCalls execution.ScalarBytes execution.MappedFetch
 memory.ByteMemory memory.WriteTrace.
From Ed25519Simd.KeyTable Require ObjectBytes Image.
Import ListNotations. Local Open Scope Z_scope.

(* Start with dirty bytes on both sides of all eight zero-digit entries. *)
Definition center j:=4096+2720*Z.of_nat j.
Definition entry:=CPU (fun r=>match r with O=>center O | S O=>8 | _=>17 end)
 (fun _ _=>0) None (fun _=>165).
Definition matches text:=match run 72 (ScalarBytes.fetch 8192 text) (State(Running 50) entry (Some true)) with
 | Some(State(Running 104) out _,ws)=>
  Nat.eqb (length ws) 48 && forallb (fun j=>let a:=center j in
    (mem out (a-1)=?165) && (mem out (a+160)=?165) && forallb (fun i=>
      read_word (mem out) (a+8*Z.of_nat i)=?Image.identity_word (Z.of_nat i)) (seq 0 20)) (seq 0 8)
 | _=>false end.
Example linked_rows: matches KeyTable.ObjectBytes.symbol_bytes=true.
Proof. vm_compute;reflexivity. Qed.

(* Change MOV qword [rax+120],2 to MOV qword [rax+120],1.
   The same instructions return at the same PC and write incorrect identities. *)
Definition damaged:=firstn 90 KeyTable.ObjectBytes.symbol_bytes++[1]++skipn 91 KeyTable.ObjectBytes.symbol_bytes.
Example changed_projective_z: matches damaged=false.
Proof. vm_compute;reflexivity. Qed.
