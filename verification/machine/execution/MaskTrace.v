From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions isa.X86 isa.ProgramLayout.
Import ListNotations. Local Open Scope Z_scope.

(* A word circuit denotes each of the eight lanes independently. Mask bits
   are 0 or 1. KMOVW assembles those bits before scalar control observes them. *)
Inductive arg := Lit (n:Z) | Input (base row:nat) | Initial (reg:nat) | Wire (id:nat) | UpperCleared (prior:arg).
Inductive gate :=
| AddQ (a b:arg) | SubQ (a b:arg) | MulQ (a b:arg) | AndQ (a b:arg)
| ShiftQ (a:arg) (n:nat) | MaddQ (high:bool) (acc a b:arg)
| EqQ (a b:arg) | OrK (a b:arg)
| LeftQ (a:arg) (n:nat) | MinUQ (a b:arg) | LessUQ (a b:arg).
Fixpoint operand (lane:nat) (input:nat->nat->Z) (initial wire:nat->Z) a := match a with
 | Lit n=>n | Input b i=>input b i | Initial r=>initial r | Wire i=>wire i | UpperCleared p=>if Nat.ltb lane 2 then operand lane input initial wire p else 0 end.
Definition denote (v:arg->Z) g := match g with
 | AddQ a b=>Arithmetic.vpaddq (v a) (v b) | SubQ a b=>Arithmetic.vpsubq (v a) (v b)
 | MulQ a b=>Arithmetic.vpmullq (v a) (v b) | AndQ a b=>Logic.vpandq (v a) (v b)
 | ShiftQ a n=>Shift.vpsrlq (v a) n | MaddQ h acc a b=>IFMA.madd52 h (v acc) (v a) (v b)
 | LeftQ a n=>Shift.vpsllq (v a) n
 | MinUQ a b=>Z.min (low64 (v a)) (low64 (v b))
 | LessUQ a b=>if low64 (v a) <? low64 (v b) then 1 else 0
 | EqQ a b=>if v a =? v b then 1 else 0 | OrK a b=>Z.lor (v a) (v b) end.
Definition circuit := list gate.
Fixpoint evaluate lane gs n input initial (w:nat->Z) := match gs with
 | []=>w | g::tail=>evaluate lane tail (S n) input initial
      (put w n (denote (operand lane input initial w) g)) end.
Definition value lane gs input initial :=
 operand lane input initial (evaluate lane gs O input initial (fun _=>0)).
Fixpoint mask_word (n:nat) (f:nat->Z) : Z := match n with
 | O=>0 | S k=>mask_word k f + f k * 2^(Z.of_nat k) end.

(* Displacements are relative to the end of the encoded instruction. Existing
   register and memory encoders are shared with the block machine. *)
Inductive ins :=
| Vector (i:instruction) | Store (src base:nat) (disp:Z)
| MemALU (sub:bool) (dst src base:nat) (disp:Z)
| RipBroadcast (dst:nat) (disp:Z) | CompareQ (k a b:nat)
| OrMask (k a b:nat) | KmovEax (k:nat) | CmpEax (imm:Z) | Je (disp:Z)
| RipMul (dst src:nat) (disp:Z) | MinUnsigned (dst a b:nat)
| RipLessUnsigned (k src:nat) (disp:Z) | TestMask (k:nat) | Jne8 (disp:Z)
| Jump (disp:Z) | ZeroEax
| PushBP | SetBP | AlignSP | SubSP (size:Z) | RestoreSP | PopBP | Call (disp:Z) | Return | VZeroUpper.
Definition kmov_to_gpr (dst k:nat) := [0xc5;if (dst<?8)%nat then 0xf8 else 0x78;0x93;modrm 3 (Z.of_nat dst) (Z.of_nat k)].
Definition encoding i := match i with
 | Vector v=>encode v | Store s b d=>Move.encode_store s (Z.of_nat b) d
 | MemALU sub r v b d=>rm_memory 1 1 (if sub then 0xfb else 0xd4) r v (Z.of_nat b) d
 | RipBroadcast r d=>prefix 2 1 (Z.of_nat r) 0 5 ++ [0x59;modrm 0 (Z.of_nat r) 5] ++ le32 d
 | RipMul r a d=>rip_bcst 2 1 0x40 r a d
 | RipLessUnsigned k a d=>rip_bcst 3 1 0x1e k a d ++ [1]
 | MinUnsigned r a b=>rr 2 1 0x3b r a b
 | TestMask k=>[0xc5;0xf8;0x98;modrm 3 (Z.of_nat k) (Z.of_nat k)]
 | Jne8 d=>[0x75;d mod 256] | Jump d=>0xe9::le32 d | ZeroEax=>[0x31;0xc0]
 | CompareQ k a b=>rr 2 1 0x29 k a b
 | OrMask k a b=>[0xc5;0x84 + 8*(15-Z.of_nat a);0x45;modrm 3 (Z.of_nat k) (Z.of_nat b)]
 | KmovEax k=>kmov_to_gpr 0 k
 | CmpEax n=>0x3d::le32 n | Je d=>[0x0f;0x84]++le32 d
 | PushBP=>exit_bytes PushRbp | PopBP=>exit_bytes PopRbp
 | SetBP=>op_bytes (Program [] []) (MovReg 5 4)
 | RestoreSP=>op_bytes (Program [] []) (MovReg 4 5)
 | SubSP n=>op_bytes (Program [] []) (AdjustRsp true n)
 | AlignSP=>op_bytes (Program [] []) AlignRsp64 | Call d=>exit_bytes (CallRel32 d)
 | Return=>exit_bytes Ret | VZeroUpper=>op_bytes (Program [] []) ZeroUpper end.
Definition legal i := match i with
 | Vector v=>encodable v | Store s b d=>encodable (s,Load b d)
 | MemALU _ r a b d=>Nat.ltb a 32 && encodable (r,Load b d)
 | RipBroadcast r d=>Nat.ltb r 32 && signed 32 d
 | CompareQ k a b=>Nat.ltb k 8 && Nat.ltb a 32 && Nat.ltb b 32
 | OrMask k a b=>Nat.ltb k 8 && Nat.ltb a 8 && Nat.ltb b 8 | KmovEax k=>Nat.ltb k 8
 | RipMul r a d=>Nat.ltb r 32 && Nat.ltb a 32 && signed 32 d
 | RipLessUnsigned k a d=>Nat.ltb k 8 && Nat.ltb a 32 && signed 32 d
 | MinUnsigned r a b=>Nat.ltb r 32 && Nat.ltb a 32 && Nat.ltb b 32
 | TestMask k=>Nat.ltb k 8 | Jne8 d=>signed 8 d | Jump d=>signed 32 d
 | CmpEax n=>unsigned 32 n | Call d | Je d | SubSP d=>signed 32 d | _=>true end.
Inductive part := Op (i:ins) | Literal (bytes:list Z).
Definition bytes p := flat_map (fun s=>match s with Op i=>encoding i|Literal bs=>bs end) p.
Definition well_formed := forallb (fun s=>match s with Op i=>legal i | Literal bs=>forallb (unsigned 8) bs end).
Fixpoint layout (p:list part) (pc:Z) := match p with
 | []=>[] | Op i::t=>let next:=pc+Z.of_nat(length(encoding i)) in (pc,(next,i))::layout t next
 | Literal bs::t=>layout t (pc+Z.of_nat(length bs)) end.

(* The two input regions are read-only views of arrays of 64-byte vectors.
   Stack offsets use the 64-byte-aligned origin below the incoming RSP.
   Calls, spills and saved RBP use the same qword slots. A vector reload
   succeeds only if all eight lanes still belong to the stored vector. *)
Inductive slot := CallerPC | SavedBP | CodePC (pc:Z) | LaneWord (a:arg) (lane:nat).
Definition arg_dec (a b:arg) : {a=b}+{a<>b}.
Proof. decide equality; first [apply Z.eq_dec|apply Nat.eq_dec]. Defined.
Record frame := Frame { sp:Z; bp:option Z; stack:Z->option slot }.
Definition write_slot (m:Z->option slot) a x := fun k=>if k=?a then Some x else m k.
Definition initial_frame entry := Frame entry None (write_slot (fun _=>None) entry CallerPC).
Definition push f s := let a:=sp f-8 in Frame a (bp f) (write_slot (stack f) a s).
Definition pop f := Frame (sp f+8) (bp f) (stack f).
Definition write_vec f a v := Frame (sp f) (bp f) (fold_left
 (fun m j=>write_slot m (a+8*Z.of_nat j) (LaneWord v j)) (seq 0 8) (stack f)).
Definition read_vec f a := match stack f a with
 | Some (LaneWord v O)=>if forallb (fun j=>match stack f (a+8*Z.of_nat j) with
   | Some(LaneWord w k)=>Nat.eqb j k && (if arg_dec v w then true else false)
   | _=>false end) (seq 0 8) then Some v else None | _=>None end.
Definition load (rows : nat -> nat) f (base : nat) d := match base with
 | 7%nat | 6%nat=>if (0<=?d)&&(d <? 64 * Z.of_nat (rows base))&&(d mod 64=?0)
    then Some(Input base (Z.to_nat (d/64))) else None
 | 4%nat=>read_vec f (sp f+d) | _=>None end.
Fixpoint little bs := match bs with []=>0 | b::t=>b+256*little t end.
Definition read_literal image a := if (0<=?a)&&(a+8<=?Z.of_nat(length image))
 then Some(little(firstn 8(skipn (Z.to_nat a) image))) else None.

Record data := Data { regs:nat->arg; masks:nat->option arg; eax:option arg;
                      cmp:option (arg*Z); count:nat; reversed:circuit }.
Definition initial_data := Data Initial (fun _=>None) None None O [].
Definition assign s r a := Data (put (regs s) r a) (masks s) (eax s) (cmp s) (count s) (reversed s).
Definition emit s r g := Data (put (regs s) r (Wire (count s))) (masks s) (eax s) (cmp s)
                         (S(count s)) (g::reversed s).
Definition emit_mask s k g := Data (regs s) (put (masks s) k (Some(Wire (count s))))
                         (eax s) (cmp s) (S(count s)) (g::reversed s).
(* A lifted vector write either copies an existing word or appends a gate.
   CircuitFacts.lower_vector_correct checks this translation against bits. *)
Inductive rhs := Existing (a : arg) | Compute (g : gate).

Definition lower_vector (read : nat -> Z -> option arg) (v : nat -> arg) dst op :=
  match op with
  | Copy a => Some (Existing (v a))
  | Load b d => option_map Existing (read b d)
  | Xor a b => if Nat.eqb a b then Some (Existing (Lit 0)) else None
  | Add a b => Some (Compute (AddQ (v a) (v b)))
  | Sub a b => Some (Compute (SubQ (v a) (v b)))
  | Mul a b => Some (Compute (MulQ (v a) (v b)))
  | And a b => Some (Compute (AndQ (v a) (v b)))
  | Shl a n => Some (Compute (LeftQ (v a) n))
  | Shr a n => Some (Compute (ShiftQ (v a) n))
  | Madd high a b => Some (Compute (MaddQ high (v dst) (v a) (v b)))
  | _ => None
  end.

Definition vector_step rows f s (i : instruction) :=
  let '(dst, op) := i in
  option_map (fun e => match e with
    | Existing a => assign s dst a
    | Compute g => emit s dst g
    end) (lower_vector (load rows f) (regs s) dst op).

Record access := Access { instruction_pc:Z; base_register:nat; stack_offset:Z; byte_count:Z }.
Inductive tree :=
| Fault
| Exit (gs : circuit) (result : arg)
| Branch (gs : circuit) (mask : arg) (imm : Z) (taken fallthrough : tree)
| Written (at_site:access) (rest:tree).

(* Translate both sides of a conditional jump before choosing a path. Only
   result below inspects lane values. Fetching literal data, accessing an
   unknown slot or exhausting the instruction budget cannot produce Exit. *)
Fixpoint walk fuel rows code literal_at bottom entry pc f s :=
  match fuel with
  | O => Fault
  | S n =>
    if (bottom <=? sp f) && (sp f <=? entry) && (sp f mod 8 =? 0) then
      match find (fun row => fst row =? pc) code with
      | None => Fault
      | Some (_, (next, i)) =>
        let go := fun pc f s => walk n rows code literal_at bottom entry pc f s in
        let continue := fun state => match state with
          | Some s' => go next f s' | None => Fault end in
        match i with
        | Vector v => continue (vector_step rows f s v)
        | MemALU sub dst src base disp =>
          match load rows f base disp with
          | Some v => go next f (emit s dst
              (if sub then SubQ (regs s src) v else AddQ (regs s src) v))
          | None => Fault end
        | RipBroadcast dst disp =>
          continue (option_map (fun z => assign s dst (Lit z)) (literal_at (next+disp)))
        | RipMul dst src disp =>
          continue (option_map (fun z => emit s dst (MulQ (regs s src) (Lit z))) (literal_at (next+disp)))
        | RipLessUnsigned dst src disp =>
          continue (option_map (fun z => emit_mask s dst (LessUQ (regs s src) (Lit z))) (literal_at (next+disp)))
        | MinUnsigned dst a b => go next f (emit s dst (MinUQ (regs s a) (regs s b)))
        | TestMask k =>
          match masks s k with
          | Some a => go next f (Data (regs s) (masks s) (eax s) (Some (a,0)) (count s) (reversed s))
          | None => Fault end
        | Jne8 disp =>
          match cmp s with
          | Some (a,imm) => Branch (rev (reversed s)) a imm (go next f s) (go (next+disp) f s)
          | None => Fault end
        | Jump disp => go (next+disp) f s
        | ZeroEax => go next f (Data (regs s) (masks s) (Some (Lit 0)) (Some (Lit 0,0)) (count s) (reversed s))
        | Store src base disp =>
          let addr := sp f + disp in
          Written (Access pc base addr 64) (if Nat.eqb base 4 && (sp f <=? addr) && (addr+64 <=? entry) && (addr mod 8 =? 0)
          then go next (write_vec f addr (regs s src)) s else Fault)
        | CompareQ dst a b => go next f (emit_mask s dst (EqQ (regs s a) (regs s b)))
        | OrMask dst a b =>
          match masks s a, masks s b with
          | Some x, Some y => go next f (emit_mask s dst (OrK x y))
          | _, _ => Fault end
        | KmovEax k =>
          match masks s k with
          | Some a => go next f (Data (regs s) (masks s) (Some a) (cmp s) (count s) (reversed s))
          | None => Fault end
        | CmpEax imm =>
          match eax s with
          | Some a => go next f (Data (regs s) (masks s) (eax s) (Some (a,imm)) (count s) (reversed s))
          | None => Fault end
        | Je disp =>
          match cmp s with
          | Some (a,imm) => Branch (rev (reversed s)) a imm (go (next+disp) f s) (go next f s)
          | None => Fault end
        | PushBP => Written (Access pc 4 (sp f-8) 8)
            (match bp f with None => go next (push f SavedBP) s | _ => Fault end)
        | SetBP => go next (Frame (sp f) (Some (sp f)) (stack f)) s
        | AlignSP | SubSP _ =>
          let addr := match i with SubSP k => sp f-k | _ => sp f-sp f mod 64 end in
          go next (Frame addr (bp f) (stack f))
            (Data (regs s) (masks s) (eax s) None (count s) (reversed s))
        | RestoreSP =>
          match bp f with Some addr => go next (Frame addr (bp f) (stack f)) s | None => Fault end
        | PopBP =>
          match stack f (sp f) with
          | Some SavedBP => go next (Frame (sp f+8) None (stack f)) s | _ => Fault end
        | Call disp => Written (Access pc 4 (sp f-8) 8) (go (next+disp) (push f (CodePC next)) s)
        | Return =>
          match stack f (sp f) with
          | Some (CodePC target) => go target (pop f) s
          | Some CallerPC =>
            match bp f, eax s with
            | None, Some a => if sp f =? entry then Exit (rev (reversed s)) a else Fault
            | _, _ => Fault end
          | _ => Fault end
        | VZeroUpper => go next f (Data (fun r =>
            if Nat.ltb r 16 then UpperCleared (regs s r) else regs s r)
            (masks s) (eax s) (cmp s) (count s) (reversed s))
        end
      end
    else Fault
  end.

Definition program_writes fuel depth rows p pad :=
  let entry := 8 + 16 * Z.of_nat pad in
  walk fuel (fun _ => rows) (layout p 0) (read_literal (bytes p)) (entry-depth) entry 0 (initial_frame entry) initial_data.

(* Calls, jumps and RIP-relative qword loads can cross either symbol boundary.
   Both regions use the same linked PC space. No instruction or qword can be
   fetched from a gap. The caller checks disjointness and the 64-bit extent. *)
Definition linked_writes fuel depth rows pad start code other helper :=
  let entry := 8 + 16 * Z.of_nat pad in
  let main_literal := read_literal (bytes code) in
  let other_literal := read_literal (bytes helper) in
  let read pc := match main_literal (pc-start) with
    | Some z => Some z | None => other_literal (pc-other) end in
  walk fuel rows (layout code start ++ layout helper other) read
       (entry-depth) entry start (initial_frame entry) initial_data.

Fixpoint erase_writes t := match t with
 | Written _ rest=>erase_writes rest
 | Branch gs a imm yes no=>Branch gs a imm (erase_writes yes) (erase_writes no)
 | _=>t end.
Definition program_tree fuel depth rows p pad := erase_writes (program_writes fuel depth rows p pad).
Definition linked_tree fuel depth rows pad start code other helper :=
 erase_writes (linked_writes fuel depth rows pad start code other helper).

Definition mask_value gs a (input : nat -> nat -> nat -> Z) (initial : nat -> nat -> Z) :=
  mask_word 8 (fun j => value j gs (input j) (initial j) a).

Fixpoint result t input initial := match t with
  | Fault => None
  | Written _ rest=>result rest input initial
  | Exit gs a => Some (mask_value gs a input initial)
  | Branch gs a imm yes no =>
    result (if mask_value gs a input initial =? imm then yes else no) input initial
  end.

Lemma erase_result t input initial : result (erase_writes t) input initial=result t input initial.
Proof.
 induction t;cbn [erase_writes result];try reflexivity;try assumption.
 destruct (_=?_);assumption.
Qed.

Fixpoint writes_on t input initial := match t with
 | Written a rest=>a::writes_on rest input initial
 | Branch gs a imm yes no=>writes_on (if mask_value gs a input initial=?imm then yes else no) input initial
 | _=>[] end.
Definition in_frame bottom top a := base_register a=4%nat /\
 bottom<=stack_offset a /\ stack_offset a+byte_count a<=top.
Fixpoint check_writes bottom top t := match t with
 | Fault=>false | Exit _ _=>true
 | Branch _ _ _ yes no=>check_writes bottom top yes && check_writes bottom top no
 | Written a rest=> Nat.eqb (base_register a) 4 && (bottom<=?stack_offset a) &&
   (stack_offset a+byte_count a<=?top) && check_writes bottom top rest end.

Lemma all_branch_writes bottom top t : check_writes bottom top t=true ->
 forall input initial, Forall (in_frame bottom top) (writes_on t input initial) /\
 exists mask,result t input initial=Some mask.
Proof.
 induction t;intros H input initial;cbn [check_writes] in H;cbn [writes_on result].
 - discriminate.
 - split;[constructor|eauto].
 - apply andb_true_iff in H as [Y N];destruct (_=?_);[apply IHt1|apply IHt2];assumption.
 - repeat rewrite andb_true_iff in H;destruct H as [[[B L] U] R].
   destruct (IHt R input initial) as [W E];split;[constructor|exact E];[|exact W].
   unfold in_frame;apply Nat.eqb_eq in B;apply Z.leb_le in L,U;auto.
Qed.

Definition stack_writes depth pad t := forall input initial,
 let top:=8+16*Z.of_nat pad in Forall (in_frame (top-depth) top) (writes_on t input initial) /\
 exists mask,result t input initial=Some mask.
