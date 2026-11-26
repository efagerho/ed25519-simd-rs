From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.X86 isa.Instructions.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Import Kernels Image Glue.
From Ed25519Simd.KeyTable Require Import Fields Pack Frame.
Import ListNotations. Local Open Scope Z_scope.

(* Offsets are relative to the ELF entry. Each fragment must stop exactly at
   the start of the next block, including at every branch destination. *)
Definition near (op:list Z) target : fragment := fun pc=>op++le32(target-pc-Z.of_nat(length op)-4).
Definition keep start := group (map (fun i=>alu (start+i)%nat (Instructions.Copy i)) (seq 0 5)).
Definition linear_ins rhs_coord (v:instruction) := let '(i,op):=v in match op with
 | Add a b=>if (5<=?b)%nat && (b<?10)%nat then
   rm_memory 1 1 0xd4 i a 12 (320*Z.of_nat rhs_coord+64*Z.of_nat (b-5)) else encode v
 | Sub a b=>rm_memory 1 1 0xfb i a 12 (320*Z.of_nat rhs_coord+64*Z.of_nat (b-5))
 | _=>encode v end.
Definition field_code decoder op := group [
 field_mem false 12 (320*Z.of_nat(source op));
 match linear_op op with
 | None=>group [group(map (fun i=>broadcast (5+i)%nat (0x8c0+8*Z.of_nat i)) (seq 0 5));
                invoke(decoder+0xa79)]
 | Some f=>group [fixed(flat_map (linear_ins (rhs op)) (Fields.prefix f));invoke(decoder+0xa7e)] end;
 if Nat.eqb (saved_in op) 0 then fixed [] else keep (saved_in op)].
Definition entry_size := 160.
Definition table_size := 2720.
Definition identity_values := [(0,1);(5,1);(15,2)].
Definition identity_word i := fold_left (fun (z:Z) kv=>if i=?fst kv then snd kv else z)
                                       identity_values 0.
Definition write_identity kv := let '(i,z):=kv in
 (if i=?0 then [0x48;0xc7;0] else [0x48;0xc7;0x40;8*i])++le32 z.
Definition identity_code := group [fixed (rm_memory 1 2 0x7f 0 0 0 0 ++
 rm_memory 1 2 0x7f 0 0 0 64 ++ [0xc5;0xfe;0x7f;0x80]++le32 128);
 fixed(flat_map write_identity identity_values);fixed([0x48;0x05]++le32 table_size++[0xff;0xc9])].
Definition reg_for i := if (i<?10)%nat then (16+i)%nat else if (i<?15)%nat then (i-5)%nat else (i-15)%nat.
Definition stage := group (map (fun i=>Glue.aligned true (reg_for i) 4 (64*Z.of_nat i)) (seq 0 15)).
Definition pack_code ops := fixed(flat_map Pack.bytes ops).
Definition single_branch target := group [fixed[0x83;0xfb;1];near [0x0f;0x84] target].
Inductive label := Frame | Identity | Start | Multiple | Stage | Select | Bulk | Single
 | First | Remaining | EndRow | Advance | Restore.
Definition order := [Frame;Identity;Start;Multiple;Stage;Select;Bulk;Single;First;Remaining;EndRow;Advance;Restore].
Definition loc l := match l with Frame=>0 | Identity=>0x32 | Start=>0x68 | Multiple=>0x6e
 | Stage=>0x274 | Select=>0x2eb | Bulk=>0x2f4 | Single=>0x436 | First=>0x490
 | Remaining=>0x52b | EndRow=>0x79b | Advance=>0x7a1 | Restore=>0x7be end.
Inductive condition := MoreKeys | AlreadyStaged | SingleKey | LastMultiple.
Inductive transfer := Fall (next:label) | Jump (long:bool) (dst:label)
 | Branch (test:condition) (yes no:label) | Return.
Definition exit l := match l with
 | Frame=>Fall Identity | Identity=>Branch MoreKeys Identity Start | Start=>Fall Multiple
 | Multiple=>Branch AlreadyStaged Select Stage | Stage=>Fall Select | Select=>Branch SingleKey Single Bulk
 | Bulk=>Jump false First | Single=>Fall First | First=>Branch SingleKey EndRow Remaining
 | Remaining=>Fall EndRow | EndRow=>Branch LastMultiple Restore Advance
 | Advance=>Jump true Multiple | Restore=>Return end.
Definition exit_code e := match e with
 | Fall _=>fixed [] | Return=>fixed [0xc3]
 | Jump long l=>if long then near [0xe9] (loc l) else short 0xeb (loc l)
 | Branch t dst _=>match t with MoreKeys=>short 0x75 (loc dst)
   | SingleKey=>single_branch (loc dst)
   | AlreadyStaged=>group [fixed[0x41;0x83;0xff;1];short 0x75 (loc dst)]
   | LastMultiple=>group [fixed[0x41;0x83;0xff;8];short 0x74 (loc dst)] end end.
Definition operations decoder helper cached l := match l with
 | Frame=>group[fixed(Frame.prologue++[0x49;0x89;0xfc;0x4c;0x8d;0xae]++
   le32 (8*entry_size)++[0x4d;0x89;0xee;0x89;0xd3;0x4c;0x89;0xe8;0x89;0xd1]);alu 0 (Xor 0 0)]
 | Identity=>identity_code | Start=>fixed ([0x41;0xbf]++le32 1)
 | Multiple=>group [fixed([0x49;0x81;0xc5]++le32 entry_size++[0x49;0x81;0xee]++le32 entry_size);
   constants helper;group(map (field_code decoder) field_order)]
 | Stage=>stage | Select | EndRow=>fixed []
 | Bulk=>pack_code(transpose false) | Single=>pack_code(transpose true)
 | First=>group [indices 28 0x800;indices 29 0x840;indices 30 0x880;
   fixed([0xb8]++le32 mask++[0xc5;0xf8;0x92;0xc8]);pack_code first]
 | Remaining=>pack_code rest
 | Advance=>group [fixed([0x4c;0x89;0xe7;0x48;0x89;0xe6;0xba]++le32 1++[0xb9]++le32 1);
   invoke cached;fixed[0x41;0xff;0xc7]]
 | Restore=>fixed Frame.epilogue end.
Definition blocks dec helper cached := map (fun l=>(loc l,group[operations dec helper cached l;
 exit_code (exit l)])) order.
Definition fallthrough l := match exit l with Fall n | Branch _ _ n=>Some(loc n) | _=>None end.
Definition short_branch l := match exit l with
 | Jump false dst | Branch MoreKeys dst _ | Branch AlreadyStaged dst _ | Branch LastMultiple dst _ =>
   Some (loc dst) | _=>None end.
Definition transfer_ok l stop :=
 (match fallthrough l with Some dst=>dst=stop | None=>True end) /\
 (match short_branch l with Some dst=> -128<=dst-stop<128 | None=>True end).
Definition image raw decoder helper cached :=
 let bs:=blocks decoder helper cached in
 Forall (fun block=>let '(off,f):=block in at_bytes raw off (f off)) bs /\
 map (fun block=>let '(off,f):=block in off+Z.of_nat(length(f off))) bs =
 map fst (tl bs)++[0x7d0] /\
 Forall (fun ln=>transfer_ok (fst ln) (snd ln))
   (combine order (map fst (tl bs)++[0x7d0])) /\
 at_bytes raw 0x800 (flat_map word_bytes
   (index0++index8++biases++map two_d (seq 0 5))) /\ length raw=0x8e8%nat.

Fixpoint equal_bytes (a b:list Z) := match a,b with [],[]=>true
 | x::xs,y::ys=>Z.eqb x y && equal_bytes xs ys | _,_=>false end.
Lemma equal_bytes_sound a b : equal_bytes a b=true -> a=b.
Proof.
 revert b;induction a;intros [|y ys];cbn;try discriminate;auto.
 rewrite andb_true_iff,Z.eqb_eq;intros [-> E];f_equal;auto.
Qed.
Definition block_matches raw (b:Z*fragment) := let '(off,f):=b in let code:=f off in
 equal_bytes (firstn (length code) (skipn (Z.to_nat off) raw)) code.
Lemma blocks_checked raw bs : forallb (block_matches raw) bs=true ->
 Forall (fun block=>let '(off,f):=block in at_bytes raw off (f off)) bs.
Proof.
 rewrite forallb_forall,Forall_forall;intros B [off f] H;apply equal_bytes_sound,(B _ H).
Qed.

Definition helper_image k decoder ds helper hs :=
 at_bytes ds 0xa79 (call (decoder+0xa79) (helper+0xb90) ++ vectors(Kernels.carry k) ++ [0xc3]) /\
 at_bytes hs 0xb90 (vectors(seed_columns k)++call 0xbfc 0xcb0++vectors(fold_columns k)++[0xc3]) /\
 length(vectors(seed_columns k))=0x6c%nat /\
 at_bytes hs 0xcb0 (vectors(convolve k)++[0xc3]) /\
 at_bytes hs 0xde0 (flat_map word_bytes [19;2^51-1;(2^51-19)*1024;(2^51-1)*1024]).
