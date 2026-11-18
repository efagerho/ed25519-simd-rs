From Coq Require Import List ZArith Bool Strings.String.
From Machine Require Import Instructions.
Import ListNotations.
Open Scope Z_scope.

(* R12 requires a SIB. R13 at displacement zero requires an explicit disp8.
   A one-byte offset cannot use the compressed displacement of a ZMM load. *)
Example load_encodings :
  encode (29%nat, Load 12 (-64)) = [0x62;0x41;0xfe;0x48;0x6f;0x6c;0x24;0xff] /\
  encode (30%nat, Load 13 0) = [0x62;0x41;0xfe;0x48;0x6f;0x75;0x00] /\
  encode (30%nat, Load 13 1) = [0x62;0x41;0xfe;0x48;0x6f;0xb5;1;0;0;0].
Proof. vm_compute; auto. Qed.

Example signed_disp32_text :
  address 13 (-2^31) = "[r13 - 2147483648]"%string.
Proof. reflexivity. Qed.

Example independent_operands :
  let load base disp := if Nat.eqb base 12 && Z.eqb disp (-64) then 10 else 0 in
  let code : list instruction := [(4%nat, Load 12 (-64)); (1%nat, Xor 4 3); (2%nat, And 1 4)] in
  let final := run load code (fun _ => 3) in
  final 1%nat = 9 /\ final 2%nat = 8.
Proof. vm_compute; auto. Qed.
