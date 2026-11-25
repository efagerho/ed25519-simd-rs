From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.X86 isa.Instructions isa.ProgramLayout execution.Packed execution.MaskTrace
  execution.LinkedCalls memory.ByteMemory execution.WordSemantics.
Import ListNotations. Local Open Scope Z_scope.

(* One lane of a register-only EVEX.512 qword block, with RIP-relative
   broadcast loads. Predicates above lane seven are cleared by comparisons.
   KMOVW later reads sixteen predicate bits, including those high bits. *)
Inductive operand := Reg (r:nat) | Rip (address:Z).
Inductive comparison := EqualQ | BelowU | AtLeastU.
Definition holds pred a b := match pred with
 | EqualQ=>a=?b | BelowU=>a<?b | AtLeastU=>b<=?a end.

Inductive op :=
 | Compare (pred:comparison) (dst gate a:nat) (b:operand)
 | Union (dst a b:nat) | Xor (dst a b:nat)
 | MoveImm (wide:bool) (x:Z) | Splat (dst:nat)
 | Add (dst gate a b:nat) | Blend (dst gate a b:nat).

Definition writemask (k:nat) (bs:list Z) := match bs with
 | a::b::c::d::rest => a::b::c::(d+Z.of_nat k)::rest | _=>[] end.
Definition cmp_bytes pred dst gate a b disp :=
 let '(map,opcode,imm):=match pred with EqualQ=>(2,0x29,[]) | BelowU=>(3,0x1e,[1]) | AtLeastU=>(3,0x1e,[5]) end in
 writemask gate (match b with Reg r=>rr map 1 opcode dst a r
                | Rip _=>rip_bcst map 1 opcode dst a disp end) ++
 imm.
Definition relative pc target (emit:Z->list Z) := target-(pc+Z.of_nat(length(emit 0))).
Definition encode pc i := match i with
 | Compare pred dst gate a b =>
   let emit:=cmp_bytes pred dst gate a b in
   emit (match b with Reg _=>0 | Rip t=>relative pc t emit end)
 | Union d a b=>MaskTrace.encoding (OrMask d a b)
 | Xor d a b=>Logic.encode_vpxorq d a b
 | MoveImm wide x=>Packed.encode (Imm wide x)
 | Splat d=>Packed.encode (Broadcast false d)
 | Add d k a b=>writemask k (Arithmetic.encode_vpaddq d a b)
 | Blend d k a b=>writemask k (rr 2 1 0x64 d a b)
 end.
Definition valid pc op :=
 let vr r:=(r<?32)%nat in let kr k:=(k<?8)%nat in match op with
 | Compare l d k a b=>kr d && kr k && vr a &&
   match b with Reg r=>vr r | Rip t=>signed 32 (relative pc t (cmp_bytes l d k a b)) end
 | Union d a b=>kr d && kr a && kr b
 | Xor d a b=>vr d && vr a && vr b
 | Add d k a b | Blend d k a b=>vr d && kr k && vr a && vr b
 | MoveImm w x=>Packed.valid 0 (Imm w x)
 | Splat d=>vr d end.
(* The absolute operand used by step is exactly the target obtained by
   sign-extending bytes 6..9 and adding the end of this linked instruction. *)
Lemma broadcast_target pc pred dst gate a target :
 valid pc (Compare pred dst gate a (Rip target))=true ->
 let bs:=encode pc (Compare pred dst gate a (Rip target)) in
 pc+Z.of_nat(length bs)+displacement32 (firstn 4 (skipn 6 bs))=target.
Proof.
 intro V;cbv zeta.
 apply andb_true_iff in V as [_ Range].
 set (d:=relative pc target (cmp_bytes pred dst gate a (Rip target))) in *.
 replace (firstn 4 (skipn 6 (encode pc (Compare pred dst gate a (Rip target)))))
   with (le32 d) by (destruct pred;reflexivity).
 rewrite displacement32_le32 by exact Range.
 unfold d,relative;destruct pred;
   first [change (pc+11+(target-(pc+11))=target)
         |change (pc+10+(target-(pc+10))=target)];lia.
Qed.
Fixpoint assemble pc ops := match ops with
 | []=>Some [] | i::t=>if valid pc i then let bs:=encode pc i in
   option_map (app bs) (assemble (pc+Z.of_nat(length bs)) t) else None end.

Record lane := Lane { zmm:nat->Z; mask:nat->bool; rax:Z }.
Definition step (low:bool) (read:Z->Z) s i :=
 let v:=zmm s in let k:=mask s in let enabled n:=(Nat.eqb n 0 || k n)%bool in
 let setv r x:=Lane (Packed.update v r x) k (rax s) in
 let setk r x:=Lane v (Packed.update k r x) (rax s) in
 match i with
 | Compare pred d g a b =>
   let y:=match b with Reg r=>v r | Rip t=>read t end in
   setk d (low && enabled g && (holds pred (v a) y))%bool
 | Union d a b=>setk d (k a || k b)%bool
 | Xor d a b=>setv d (Z.lxor (v a) (v b))
 | MoveImm _ x=>Lane v k x
 | Splat d=>setv d (rax s)
 | Add d g a b=>setv d (if enabled g then Arithmetic.vpaddq (v a) (v b) else v d)
 | Blend d g a b=>setv d (if enabled g then v b else v a)
 end.
Definition execute ops slide (s:cpu) (incoming:nat->nat->bool) j :=
 fold_left (step (j<?8)%nat (fun t=>read_word (mem s) (word (slide+t)))) ops
           (Lane (vectors s j) (incoming j) (regs s 0%nat)).
