From Coq Require Import ZArith List.
From Machine Require Import isa.X86 isa.Instructions execution.MaskTrace.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Import Kernels Power.
From Curve25519 Require Import Radix51Digits DecompressionRadix51.
From Ed25519Simd.Decode Require Import Image Decode Scale.
Import ListNotations. Local Open Scope Z_scope.

(* Symbol-relative labels, relocated against the two other ELF entry points.
   Assembly groups below are the instruction expansion of the lane schedule. *)
Definition fragment := Z -> list Z.
Definition fixed (bs:list Z) : fragment := fun _=>bs.
Fixpoint emit (fs:list fragment) pc := match fs with []=>[] | f::rest=>
 let bytes:=f pc in bytes++emit rest (pc+Z.of_nat(length bytes)) end.
Definition group fs : fragment := emit fs.
Definition alu d op := fixed (encode (d,op)).
Definition invoke dst : fragment := fun pc=>call pc dst.
Definition rip f dst : fragment := fun pc=>f (dst-pc-10).
Definition broadcast r := rip (fun d=>MaskTrace.encoding (RipBroadcast r d)).
Definition field_mem store b off := fixed (rows store b off).
Definition aligned (store:bool) r b d := fixed(rm_memory 1 1 (if store then 0x7f else 0x6f) r 0 b d).
Definition lea_rhs off := fixed([0x4c;0x8d;0x87]++le32 off).
Definition short op dest : fragment := fun pc=>[op;(dest-pc-2) mod 256].
Definition mask_bytes mask (bs:list Z) := firstn 3 bs ++ [nth 3 bs 0+mask] ++ skipn 4 bs.
Definition constants helper := group(map (fun i=>broadcast (28+i)%nat (helper+0xde0+8*Z.of_nat i)) (seq 0 4)).

Definition shuffle d a b imm := fixed(rr 3 1 0x43 d a b++[imm]).
Definition perm d i r := fixed(rr 2 1 0x7e d i r).
Definition indices r := rip (fun d=>prefix 1 1 (Z.of_nat r) 0 5++[0x6f;modrm 0 (Z.of_nat r) 5]++le32 d).
Definition join d b c := fixed(rr 1 1 0xeb d b c).
Definition word_loads base table := group (
 map (fun i=>alu i (Load base (64*Z.of_nat i))) (seq 0 4) ++
 [shuffle 4 0 1 136;shuffle 5 2 3 136;shuffle 6 0 1 221;shuffle 7 2 3 221;
 indices 8 table;indices 9 (table+64);alu 0 (Copy 4);perm 0 8 5;perm 4 9 5;
 alu 2 (Copy 6);perm 2 8 7;perm 6 9 7]).
Definition y_limbs := group ([alu 1 (Shr 0 51);alu 5 (Shl 4 13);join 1 1 5;
 alu 4 (Shr 4 38);alu 5 (Shl 2 26);join 4 4 5;alu 3 (Shr 2 25);alu 5 (Shl 6 39);
 join 3 3 5;alu 2 (And 4 29);alu 4 (Shr 6 12)]++
 map (fun i=>alu i (And i 29)) [0;1;3;4]%nat).
Definition unpack_code := group [word_loads 6 0xb00; fixed(rr 2 2 0x39 2 0 6);
 fixed(MaskTrace.encoding(KmovEax 2));y_limbs].
Definition scale i := let a:=if Nat.eqb i 0 then 5%nat else i in
 let hi:=(15+i)%nat in let lo:=(10+i)%nat in
 [alu hi (Xor hi hi);alu hi (Madd true a 26);alu lo (Mul a 25);alu lo (And lo 29)].
Definition save_diff i := let lo:=(10+i)%nat in
 (if Nat.eqb i 0 then [alu i (Add i 30)] else [alu lo (Add lo (14+i));alu i (Add i 31)])++
 [aligned true lo 7 (64*Z.of_nat i);alu i (Sub i lo)].
Definition scaling helper := group ([broadcast 25 (helper+0xe18);alu 26 (Add 25 25);
 rip (rip_bcst 1 1 0xfb 5 0) 0xb80]++flat_map scale (seq 0 5)++
 [alu 10 (Madd false 19 28)]++flat_map save_diff (seq 0 5)).
Definition ones := group [alu 10 (And 1 2);alu 11 (And 3 4);alu 10 (And 10 11);
 fixed(MaskTrace.encoding(CompareQ 1 10 29))].
Definition test k := rip (fun d=>mask_bytes 1 (rip_bcst 2 1 0x29 k 0 d)).
Definition parity_step i := [alu 20 (Shr 20 51);alu 20 (Add 20 i)].
Definition select_root row := group ([fixed [0xc5;0xf8;0x44;0xe4]]++
 map (fun i=>fixed(mask_bytes 4 (rm_memory 1 1 0x6f i 0 7 (row+64*Z.of_nat i)))) (seq 0 5)).
Definition sign_mask := group ([alu 20 (Add 0 28)]++flat_map parity_step (seq 1 4)++
 [alu 20 (Shr 20 51);alu 20 (Xor 0 20);rip (rip_bcst 2 1 0x27 3 20) 0xb80;
 fixed [0xc4;0xc1;0x78;0x92;0xe1;0xc5;0xe4;0x47;0xdc]]).
Definition change_sign := group ([broadcast 20 0xba0;alu 21 (Add 29 29)]++
 map (fun i=>fixed(mask_bytes 3 (encode(i,Sub (if Nat.eqb i 0 then 20 else 21) i)))) (seq 0 5)).
Definition set_one row := group ([broadcast 0 0xb80;aligned true 0 7 row;alu 10 (Xor 10 10)]++
 map (fun i=>aligned true 10 7 (row+64*Z.of_nat i)) (seq 1 4)).

(* A field slot is a column of five 64-byte rows at RDI + 320*slot.
   The encoder and evaluator consume the same list of operations, including
   field loads, stores, preservation of the mask in R10D and its return. *)
Inductive delta := PlusOne | MinusOne | Zero.
Definition displacement d := match d with PlusOne=>0xb90 | MinusOne=>0xb98 | Zero=>0xb88 end.
Definition adjustment d := match d with PlusOne=>1 | MinusOne=>(-1) | Zero=>0 end.
Inductive action := Unpack | LoadField (s:nat) | StoreField (s:nat) | FromPower
 | TimesField (s:nat) | TimesPower | TimesI | Squared | ScaleDiff
 | High | CompareLow (mask:nat) (d:delta) | Union (dst a b:nat) | SaveValidity
 | SelectRoot (s:nat) | SignMask | Negate | One (s:nat) | ReturnMask.
Definition offset (s:nat) := 320*Z.of_nat s.
Definition expansion helper cmd := match cmd with
 | Unpack=>unpack_code | LoadField s=>field_mem false 7 (offset s)
 | StoreField s=>field_mem true 7 (offset s) | FromPower=>field_mem false 6 0
 | TimesField s=>group [lea_rhs (offset s);invoke 0xa57]
 | TimesPower=>group [fixed [0x49;0x89;0xf0];invoke 0xa57] | TimesI=>invoke 0xa23
 | Squared=>invoke 0x59b | ScaleDiff=>group [scaling helper;invoke 0xa7e]
 | High=>ones | CompareLow m d=>test m (displacement d)
 | Union dst a b=>fixed(MaskTrace.encoding(OrMask dst a b))
 | SaveValidity=>fixed [0xc5;0x78;0x93;0xd2] | SelectRoot s=>select_root (offset s)
 | SignMask=>sign_mask | Negate=>change_sign | One s=>set_one (offset s)
 | ReturnMask=>fixed [0x44;0x89;0xd0] end.
Definition setup_ops := [Unpack;StoreField 1;TimesField 1;ScaleDiff;StoreField 2;
 LoadField 0;TimesField 2;StoreField 3].
Definition finish_ops := [FromPower;Squared;TimesField 3;High;CompareLow 3 PlusOne;CompareLow 4 MinusOne;
 LoadField 0;High;CompareLow 2 Zero;Union 3 3 2;Union 2 3 4;SaveValidity;TimesPower;
 StoreField 3;TimesI;SelectRoot 3;SignMask;Negate;StoreField 0;TimesField 1;StoreField 3;One 2;ReturnMask].
Definition subroutine h ops := group(map (expansion h) ops++[fixed [0xc3]]).

Record lane := Lane { reg:field; slots:nat->field; masks:nat->bool; saved:bool; eax:bool }.
Definition execute_action k y sign t st cmd :=
 let r:=reg st in let f:=slots st in let m:=masks st in
 let reg_write x:=Lane x f m (saved st) (eax st) in
 let store s x:=Lane r (put f s x) m (saved st) (eax st) in
 let mask i x:=Lane r f (put m i x) (saved st) (eax st) in
 match cmd with
 | Unpack=>Lane y f m (saved st) sign | LoadField s=>reg_write (f s) | StoreField s=>store s r
 | FromPower=>reg_write t | TimesField s=>reg_write (mul k r (f s)) | TimesPower=>reg_write (mul k r t)
 | TimesI=>reg_write (mul k r sqrt_limbs) | Squared=>reg_write (sq k r)
 | ScaleDiff=>Lane (finite(reduced(difference r))) (put f 0 (finite(scaled r))) m (saved st) (eax st)
 | High=>mask 1%nat
    (Z.land (Z.land (r 1%nat) (r 2%nat)) (Z.land (r 3%nat) (r 4%nat)) =? radix-1)
 | CompareLow dst d=>mask dst (m 1%nat && (r 0%nat =? radix-19+adjustment d))%bool
 | Union dst a b=>mask dst (m a || m b)%bool
 | SaveValidity=>Lane r f m (m 2%nat) (eax st)
 | SelectRoot s=>reg_write (if m 4%nat then r else f s)
 | SignMask=>mask 3%nat (xorb (parity_after r) sign)
 | Negate=>reg_write (if m 3%nat then native_neg r else r)
 | One s=>store s one | ReturnMask=>Lane r f m (saved st) (saved st) end.
Definition prepared_from k y sign := fold_left (execute_action k y sign (fun _=>0)) setup_ops.
Definition empty := Lane (fun _=>0) (fun _ _=>0) (fun _=>false) false false.
Definition prepared k y sign := prepared_from k y sign empty.
Definition scheduled_from k y sign t initial :=
 let st:=prepared_from k y sign initial in
 let final:=fold_left (execute_action k y (eax st) t) finish_ops st in
 Output (eax final) (slots final 0%nat) (slots final 1%nat) (slots final 2%nat) (slots final 3%nat).
Definition scheduled k y sign t := scheduled_from k y sign t empty.
Lemma incoming_words_unused k y sign t initial :
 slots(prepared_from k y sign initial) 3%nat=slots(prepared k y sign) 3%nat /\
 scheduled_from k y sign t initial=scheduled k y sign t.
Proof. split;reflexivity. Qed.

Lemma prepared_state k y sign : verified k Multiply=true -> split_field y ->
 prepared k y sign = let h:=yy k y in let u:=u_digits h in let v:=v_digits h in
 let mem:=put (put (put (put (fun _ _=>0) 1 y) 0 u) 2 v) 3 (mul k u v) in
 Lane (mul k u v) mem (fun _=>false) false sign.
Proof.
 intros M Y;destruct(mul_ok _ _ _ M Y Y) as [B [L _]].
 destruct(scaled_fields _ B L) as [U V].
 cbv [prepared prepared_from empty setup_ops fold_left execute_action reg slots masks saved eax put Nat.eqb].
 rewrite U,V. reflexivity.
Qed.
Lemma prepared_product k y sign : verified k Multiply=true -> split_field y ->
 slots(prepared k y sign) 3%nat=uv k y.
Proof. intros M Y;rewrite prepared_state by assumption;reflexivity. Qed.
Lemma scheduled_finish k y sign t : verified k Multiply=true -> split_field y -> squared t ->
 scheduled k y sign t=finish k y sign t.
Proof.
 intros M Y T. destruct(setup_ok _ _ M Y) as [_ [_ [U _]]].
 destruct(mul_ok _ _ _ M (bounded_split _ U) (squared_split _ T)) as [X _].
 destruct(mul_ok _ _ _ M (bounded_split _ X) sqrt_bound) as [IX _].
 unfold scheduled,scheduled_from;fold (prepared k y sign);rewrite prepared_state by assumption.
 cbv [finish_ops fold_left execute_action slots masks reg saved eax put Nat.eqb adjustment].
 unfold finish. fold (uv k y).
 set (raw:=mul k (u_digits (yy k y)) t) in *.
 set (q:=mul k (sq k t) (uv k y)).
 fold (high_test q (-1)). fold (high_test q 1). fold (high_test (u_digits (yy k y)) 0).
 set (x:=if high_test q (-1) then mul k raw sqrt_limbs else raw).
 assert (B:bounded x) by (unfold x;destruct(high_test q (-1));assumption).
 match goal with |- context[parity_after ?z] => rewrite (parity_after_ok z B),(native_neg_ok z B) end. reflexivity.
Qed.
Definition sqrt_load helper := group(map (fun i=>broadcast (5+i)%nat (helper+0xe20+8*Z.of_nat i)) (seq 0 5)
 ++[short 0xeb 0xa79]).
Definition glue_image decoder_pc decoder helper_pc helper :=
 let h:=helper_pc-decoder_pc in
 at_bytes decoder 0xf4 (subroutine h setup_ops 0xf4) /\ at_bytes decoder 0x385 (subroutine h finish_ops 0x385) /\
 at_bytes decoder 0xa23 (sqrt_load h 0xa23) /\
 at_bytes decoder 0xb00 (flat_map word_bytes
   (map (fun i=>2*Z.of_nat i) (seq 0 8)++map (fun i=>2*Z.of_nat i+1) (seq 0 8)++
   [1;radix-19;radix-18;radix-20;2*(radix-19)])) /\
 at_bytes helper 0xe18 (flat_map word_bytes (121666::map sqrt_limbs (seq 0 5))).
