From Coq Require Import List ZArith Strings.String.
From Machine Require Import execution.Packed execution.LinkedCalls memory.ByteMemory tests.model.Oracle.
Import ListNotations. Local Open Scope Z_scope.

Definition code := [Imm false 0; Broadcast false 0; AddRow 1 0 0; AddRow 17 0 1;
 Imm false 0x1f8; Broadcast true 3; Sub 4 1 3; And 5 17 3;
 Unpack false 18 4 5; Unpack true 19 4 5; Shuffle 2 18 19 0x1b;
 Store 2 2; AddRow 20 17 2; ShiftQ true 6 20 5; ShiftQ false 7 6 3;
 AddQ 8 20 7; Store 3 8; Upper; Store 4 2; Store 5 20].
Definition seeds := [0;1;127;128;255].
Definition run seed :=
 let s:=CPU (fun _=>0) (fun _ _=>0) None (fun i=>(7*i+seed+53*(i/16)) mod 256) in
 let out:=execute 6 code s in seed :: map (buffer_words (mem out) 0) (seq 0 48).
Definition packed_report inputs := String.concat "|"%string
 (numbers (flat_map encode code ++ [0xc3]) :: map (fun seed=>numbers (run seed)) inputs).
Example operands_checked : forallb (valid 6) code=true. Proof. reflexivity. Qed.
