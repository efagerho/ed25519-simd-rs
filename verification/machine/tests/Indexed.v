From Coq Require Import List ZArith Bool Strings.String.
From Machine Require Import isa.IndexedLoad execution.IndexedLoads execution.LinkedCalls
  execution.Packed memory.ByteMemory tests.model.Oracle.
Import ListNotations. Local Open Scope Z_scope.

Definition src disp := Addr 7 true disp.
Definition loads := [MovZX true (Addr 7 false 1); CopyEaxToR11d; ShrR11d 4;
  And32 0 15; And32 11 240; OrEaxR11d; XorEax 136; ImulEax 160; And32 0 63;
  LeaTwice 0 0; AddRax (Addr 7 false 128); LoadZ 3 (src 0); LoadY 3 (src 8);
  InsertY 18 3 (src 31) true; LoadZ 17 (src 32);
  MovZX false (Addr 7 false 4); And32 0 15; InsertY 19 17 (src 64) false].
Definition route := [UnpackQ false 20 18 17;UnpackQ true 21 18 17;
  StoreAligned 3 20;StoreAligned 4 21;StoreAligned 5 3;StoreAligned 6 19;Upper].
Definition seeds := [0;1;127;128;255].
Definition run seed :=
 let s:=CPU (fun _=>0) (fun _ _=>0) None (fun i=>
   if (128<=?i) && (i<?136) then (if i=?128 then 9 else 0)
   else (7*i+seed+53*(i/16)) mod 256) in
 let out:=Packed.execute 7 route (IndexedLoads.execute loads s) in
 seed :: map (buffer_words (mem out) 0) (seq 24 32).
Definition indexed_report inputs := String.concat "|"%string
 (numbers (flat_map IndexedLoad.encode loads ++ flat_map Packed.encode route ++ [0xc3]) ::
  map (fun seed=>numbers (run seed)) inputs).
Example encodable : forallb IndexedLoad.valid loads && forallb (Packed.valid_with_alignment true 7) route=true.
Proof. reflexivity. Qed.
Example aligned_store_requires_alignment : Packed.valid 7 (StoreAligned 3 20)=false.
Proof. reflexivity. Qed.
