From Coq Require Import ZArith List Bool Lia.
From Machine Require Import isa.X86 isa.Instructions execution.LinkedCalls.
From Ed25519Simd.Decode Require Import Image Glue.
Import ListNotations. Local Open Scope Z_scope.

Inductive callee := Setup | PairedPower | SinglePower | Finish.
Inductive op := Push (r:nat) | Pop (r:nat) | Mov (wide:bool) (d s:nat)
 | Lea (d b:nat) (disp:Z) | Align | Adjust (sub:bool) (r:nat) (imm:Z)
 | Constants | Call (c:callee) | CmpTwo | Jne (dst:Z) | Jump (dst:Z)
 | ShiftMask | OrMask | Upper | Ret.
Definition ops := [
 Push 5;Mov true 5 4;Push 3;Push 12;Push 13;Push 14;Align;Adjust true 4 640;
 Mov true 3 7;Mov false 12 2;Constants;Call Setup;Mov false 13 0;CmpTwo;Jne 0xa8;
 Lea 7 3 1280;Adjust false 6 256;Call Setup;Mov false 14 0;Lea 2 3 2240;Lea 6 3 960;
 Mov true 7 4;Call PairedPower;Constants;Jump 0xb0;
 Mov true 6 4;Call SinglePower;Mov true 7 3;Mov true 6 4;Mov false 9 13;Call Finish;
 CmpTwo;Jne 0xe4;Mov false 13 0;Lea 7 3 1280;Lea 6 4 320;Mov false 9 14;Call Finish;
 ShiftMask;OrMask;Lea 4 5 (-32);Pop 14;Pop 13;Pop 12;Pop 3;Pop 5;Upper;Ret].
Definition rex wide r b := 0x40+(if wide:bool then 8 else 0)+4*(Z.of_nat r/8)+Z.of_nat b/8.
Definition encoding h p cmd : fragment := match cmd with
 | Push r=>fixed(reg_byte 0x50 r) | Pop r=>fixed(reg_byte 0x58 r)
 | Mov w d s=>fixed([rex w s d;0x89;modrm 3 (Z.of_nat s) (Z.of_nat d)])
 | Lea d b offset=>let short:=(-128<=?offset)&&(offset<?128) in
   fixed([rex true d b;0x8d;modrm (if short then 1 else 2) (Z.of_nat d) (Z.of_nat b)]++
      (if Nat.eqb b 4 then [0x24] else [])++(if short then [offset mod 256] else le32 offset))
 | Align=>fixed [0x48;0x83;0xe4;0xc0]
 | Adjust sub r n=>fixed ([0x48;0x81;modrm 3 (if sub then 5 else 0) (Z.of_nat r)]++le32 n)
 | Constants=>constants h | Call c=>invoke(match c with Setup=>0xf4 | PairedPower=>p | SinglePower=>0x7f1 | Finish=>0x385 end)
 | CmpTwo=>fixed [0x41;0x83;0xfc;2] | Jne dest=>short 0x75 dest | Jump dest=>short 0xeb dest
 | ShiftMask=>fixed [0xc1;0xe0;8] | OrMask=>fixed [0x44;0x09;0xe8]
 | Upper=>fixed [0xc5;0xf8;0x77] | Ret=>fixed [0xc3] end.

(* Symbolically follow the integer caller with disjoint point, input and stack
   bases. A callee event records the live pointers after the call has pushed
   its return word. Slots in this caller's stack hold its incoming registers. *)
Inductive word := Input (off:Z) | Point (off:Z) | Stack (off:Z) | Integer (n:Z)
 | Incoming (r:nat) | ReturnAddress | SavedSign (point:Z) | Validity (point:Z)
 | Shifted (x:word) | Combined (hi lo:word) | Unknown.
Definition low32 v := match v with
 | Integer n=>Integer(n mod 2^32) | SavedSign _ | Validity _=>v | _=>Unknown end.
Definition plus v n := match v with Input x=>Input(x+n) | Point x=>Point(x+n)
 | Stack x=>Stack(x+n) | Integer x=>Integer(x+n) | _=>Unknown end.
Definition event := (callee * list word)%type.
Record state := State { regs:nat->word; mem:Z->word; equal:bool; events:list event }.
Definition write s r w := State (put (regs s) r w) (mem s) (equal s) (events s).
Definition initial pair pad :=
 let g:=put (put (put (put Incoming 4 (Stack(40+16*Z.of_nat pad))) 7 (Point 0)) 6 (Input 0)) 2
   (Integer(if pair:bool then 2 else 1)) in State g (fun x=>if x=?40+16*Z.of_nat pad then ReturnAddress else Unknown) false [].
Definition next_call c s := let g:=regs s in
 let call args out:=State out (mem s) false (events s++[(c,args)]) in
 match c with
 | Setup=>match g 7%nat with Point n=>Some(call [g 7%nat;g 6%nat;plus(g 4%nat)(-8)]
     (put (put g 8 Unknown) 0 (SavedSign n))) | _=>None end
 | Finish=>match g 7%nat with Point n=>Some(call [g 7%nat;g 6%nat;g 9%nat;plus(g 4%nat)(-8)]
     (put(put(put g 8 Unknown) 10 Unknown) 0 (Validity n))) | _=>None end
 | SinglePower=>Some(call [g 3%nat;g 6%nat;plus(g 4%nat)(-8)] (put(put g 1 Unknown) 8 Unknown))
 | PairedPower=>Some(call [g 7%nat;g 6%nat;g 2%nat;plus(g 4%nat)(-8)]
     (fun r=>if existsb (Nat.eqb r) [3;4;5;12;13;14;15]%nat then g r else Unknown))
 end.
Fixpoint layout h p pc cmds := match cmds with []=>[] | c::rest=>
 let next:=pc+Z.of_nat(length(encoding h p c pc)) in (pc,(next,c))::layout h p next rest end.
Fixpoint walk fuel code pc s := match fuel with O=>None | S n=>
 match find (fun row=>fst row =? pc) code with None=>None | Some(_, (next,c))=>
 let g:=regs s in let m:=mem s in let go:=walk n code next in
 match c with
 | Push r=>match g 4%nat with Stack sp=>go(State (put g 4 (Stack(sp-8))) (fun x=>if x=?sp-8 then g r else m x) (equal s) (events s)) | _=>None end
 | Pop r=>match g 4%nat with Stack sp=>go(write (write s r (m sp)) 4 (Stack(sp+8))) | _=>None end
 | Align=>match g 4%nat with Stack sp=>go(write s 4 (Stack(sp-sp mod 64))) | _=>None end
 | Mov wide d src=>go(write s d (if wide then g src else low32(g src))) | Lea d b offset=>go(write s d (plus(g b)offset))
 | Adjust sub r v=>go(write s r (plus(g r)(if sub then -v else v)))
 | CmpTwo=>match g 12%nat with Integer cnt=>go(State g m (cnt=?2) (events s)) | _=>None end
 | Jne dst=>walk n code (if equal s then next else dst) s | Jump dst=>walk n code dst s
 | Call tag=>match next_call tag s with Some t=>go t | None=>None end
 | ShiftMask=>go(write s 0 (Shifted(g 0%nat))) | OrMask=>go(write s 0 (Combined(g 0%nat)(g 13%nat)))
 | Ret=>match g 4%nat with Stack sp=>match m sp with
        ReturnAddress=>Some(write s 4 (Stack(sp+8))) | _=>None end | _=>None end
 | Constants | Upper=>go s end end end.

Definition expected pair : list event :=
 [(Setup,[Point 0;Input 0;Stack(-648)])]++
 (if pair:bool then [(Setup,[Point 1280;Input 256;Stack(-648)]);
   (PairedPower,[Stack(-640);Point 960;Point 2240;Stack(-648)])]
 else [(SinglePower,[Point 0;Stack(-640);Stack(-648)])])++
 [(Finish,[Point 0;Stack(-640);SavedSign 0;Stack(-648)])]++
 (if pair then [(Finish,[Point 1280;Stack(-320);SavedSign 1280;Stack(-648)])] else []).
Definition run h p pair pad := walk 64 (layout h p 0 ops) 0 (initial pair pad).
Definition caller_result h p pair pad : Prop :=
 match run h p pair pad with None=>False | Some s=>
 events s=expected pair /\ regs s 0%nat=(if pair then Combined (Shifted(Validity 1280))(Validity 0) else Validity 0) /\
 map (regs s) [3;5;12;13;14;15]%nat=map Incoming [3;5;12;13;14;15]%nat /\
 regs s 4%nat=Stack(48+16*Z.of_nat pad) end.
Definition caller_image decoder_pc decoder helper_pc pow_pc :=
 at_bytes decoder 0 (group (map (encoding (helper_pc-decoder_pc) (pow_pc-decoder_pc)) ops) 0).

Fixpoint eval_mask (valid:Z->Z) w := match w with
 | Validity offset=>valid offset | Shifted v=>Z.shiftl (eval_mask valid v) 8
 | Combined hi lo=>Z.lor (eval_mask valid hi) (eval_mask valid lo) | _=>0 end.
Definition return_value h p pair pad valid := match run h p pair pad with
 | Some s=>eval_mask valid (regs s 0%nat) | None=>(-1) end.
Lemma return_value_ok h p pair pad valid : caller_result h p pair pad ->
 return_value h p pair pad valid=if pair then Z.lor (Z.shiftl (valid 1280) 8) (valid 0) else valid 0.
Proof.
 unfold caller_result,return_value;destruct(run h p pair pad) as [s|];[|contradiction].
 intros [_ [E _]]. rewrite E;destruct pair;reflexivity.
Qed.
