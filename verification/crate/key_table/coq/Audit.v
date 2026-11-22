From Coq Require Import List ZArith Bool Lia.
From Machine Require Import memory.ByteMemory memory.FlatMemory execution.WordBounds.
From Curve25519.group Require Import PrimeField Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.CachedAdd Require Audit.
From Ed25519Simd.Decode Require Import Kernels Image Decode.
From Ed25519Simd.KeyTable Require Import Frame Image Rows Advance Execution.
Import ListNotations. Local Open Scope Z_scope.

(* Decode the actual little-endian table at the addressing convention of the
   ladder. The witness of initialization is independent of incoming RSI bytes. *)
Definition slot base j digit i :=
 base + 2720*Z.of_nat j + 160*(8+digit) + 8*Z.of_nat i.
Definition output_byte incoming k w writes base a :=
 let off:=(a-base)/8 in
 match lookup (store_all writes) off with
 | Some v=>Some(word_byte (resolve incoming k w v) ((a-base) mod 8)) | None=>None end.
Definition table_view incoming k w writes base flat a :=
 match output_byte incoming k w writes base a with Some b=>b | None=>flat a end.
Definition signed_table_result incoming k count w base := exists writes,
 returning count=Some writes /\
 (forall off ws, In (off,ws) writes -> 0<=off /\ off+Z.of_nat(length ws)<=340*Z.of_nat count) /\
 (forall a,a<base \/ base+2720*Z.of_nat count<=a -> output_byte incoming k w writes base a=None) /\
 forall j digit,(j<count)%nat -> -8<=digit<=8 ->
 (forall i b,(i<20)%nat -> 0<=b<8 -> exists v,
   output_byte incoming k w writes base (slot base j digit i+b)=Some v) /\
 forall prior, let entry i := read_word (table_view incoming k w writes base prior) (slot base j digit i) in
 (forall i,(i<20)%nat -> 0<=entry i<2^52) /\
 (forall P, represents_point true (point_values w j) P -> value (coord w j 2)=1%fp ->
   represents_cache (scalar_cache false entry) (scale digit P)).

Definition span pc (raw:list Z) := (pc,pc+Z.of_nat(length raw)).
Fixpoint linked (spans:list (Z*Z)) := match spans with []=>true | (a,b)::tail=>
 (0<=?a)&&(b<?2^64)&&forallb (fun cd=>let '(c,d):=cd in
 ((b<=?c)||(d<=?a)) && (d-a <? 2^31) && (b-c <? 2^31)) tail && linked tail end.
Definition helper_image k decoder ds helper hs :=
 at_bytes ds 0xa79 (call (decoder+0xa79) (helper+0xb90) ++ vectors(Kernels.carry k) ++ [0xc3]) /\
 at_bytes hs 0xb90 (vectors(seed_columns k)++call 0xbfc 0xcb0++vectors(fold_columns k)++[0xc3]) /\
 length(vectors(seed_columns k))=0x6c%nat /\
 at_bytes hs 0xcb0 (vectors(convolve k)++[0xc3]) /\
 at_bytes hs 0xde0 (flat_map word_bytes [19;2^51-1;(2^51-19)*1024;(2^51-1)*1024]).
Definition preserves_kept k := forall ins, In ins (Kernels.carry k) ->
 (fst ins<5 \/ 10<=fst ins<15)%nat.

Record key_table_contract pc raw decoder ds helper hs cached cs : Prop := {
 entry_image : image raw (decoder-pc) (helper-pc) (cached-pc);
 image_layout : pc mod 64=0 /\ linked [span pc raw;span decoder ds;span helper hs;span cached cs]=true;
 cached_add_object : Audit.cached_add_contract cs;
 table_execution : exists k, helper_image k decoder ds helper hs /\ kernel_frame k Multiply /\
   field_frame (Kernels.carry k) (live Square) /\ preserves_kept k /\ forall count flat sp point_ptr table_ptr incoming,
   (count=1%nat \/ count=8%nat) ->
   placement [span pc raw;span decoder ds;span helper hs;span cached cs] count sp point_ptr table_ptr ->
   byte_memory flat -> (forall t,data_words(incoming t)) -> cache_bounds false (buffer_words flat point_ptr) ->
   staging sp mod 64=0 /\ sp-2424<=lowest sp /\
   signed_table_result incoming k count (buffer_words flat point_ptr) table_ptr
}.
