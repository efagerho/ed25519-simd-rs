From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.ScalarBytes execution.MappedFetch execution.LinkedCalls
 execution.WordSemantics execution.WordBounds memory.WriteTrace memory.MemoryGeometry.
From Machine Require isa.VectorMoves.
Import ListNotations. Local Open Scope Z_scope.

Definition line := (nat*instruction)%type.
Definition width (ops:list line) := fold_right (fun op n => Z.of_nat (fst op)+n) 0 ops.
Fixpoint decoded text off (ops:list line) : Prop := match ops with
 | []=>True | (n,op)::rest=>ScalarBytes.decode (skipn (Z.to_nat off) text)=Some(n,op) /\
                            decoded text (off+Z.of_nat n) rest end.

(* This certificate recognizes sequential instructions that leave RSP intact.
   Its only writable operands are fixed offsets in the supplied stack frame.
   The unconstrained machine step is the one used to execute each instruction. *)
Definition slot low capacity disp bytes := (low<=?disp)&&(disp+bytes<=?capacity).
Definition local low capacity op := match op with
 | VectorMove (VectorMoves.Input i)=>match i with
   | IndexedLoad.LoadY _ _ | IndexedLoad.InsertY _ _ _ _
   | IndexedLoad.UnpackWords _ _ _ _ | IndexedLoad.ShuffleWords _ _ _ _=>true | _=>false end
 | VectorMove (VectorMoves.Output _ b d)=>Nat.eqb b 4 && slot low capacity d 64
 | Store64 _ (Address b None d)=>Nat.eqb b 4 && slot low capacity d 8
 | CopyG r _ | LeaG r _ | Load64 r _ | Add64 r _=>negb (Nat.eqb r 4)
 | _=>false end.

Lemma changed_elsewhere s r v : Nat.eqb r 4=false -> regs (set s r v) 4%nat=regs s 4%nat.
Proof. unfold set,set_regs,Instructions.put;cbn;intros ->;reflexivity. Qed.
Lemma inside base low cap d n : 0<=low -> fits64 base cap -> 0<n -> slot low cap d n=true ->
 word (base+d)=base+d /\ forall x,base+d<=x<base+d+n -> base+low<=x<base+cap.
Proof.
 unfold fits64,slot;intros Low [L H] N B;apply Bool.andb_true_iff in B as [A E];
 apply Z.leb_le in A,E;split;[apply word_fits;unfold word64|];lia.
Qed.
Lemma next low cap base origin off n op s carry : local low cap op=true -> 0<=low -> fits64 base cap ->
 regs s 4%nat=base -> exists t c ws,
 step origin off n op s carry=Some(State (Running (off+Z.of_nat n)) t c,ws) /\
 regs t 4%nat=base /\ confined (fun x=>base+low<=x<base+cap) ws.
Proof.
 intros Valid Low Fit SP;destruct op;cbn [local] in Valid;try discriminate;
 try solve [apply Bool.negb_true_iff in Valid;do 3 eexists;split;[reflexivity|];
   split;[rewrite <- SP;apply changed_elsewhere,Valid|constructor]].
 - destruct a as [b [ix|] d];try discriminate.
   apply Bool.andb_true_iff in Valid as [B V];apply Nat.eqb_eq in B;subst b.
   destruct (inside _ _ _ d 8 Low Fit ltac:(lia) V) as [Addr Bounds].
   do 3 eexists;split;[reflexivity|split;[exact SP|]].
   constructor;[|constructor]. intros x X;apply Bounds.
   change (word (regs s 4%nat+0+d)<=x<word (regs s 4%nat+0+d)+8) in X.
   now rewrite SP,Z.add_0_r,Addr in X.
 - destruct op as [i|r b d].
   + destruct i;try discriminate. all: do 3 eexists;split;[reflexivity|split;[exact SP|constructor]].
   + apply Bool.andb_true_iff in Valid as [B V];apply Nat.eqb_eq in B;subst b.
     destruct (inside _ _ _ d 64 Low Fit ltac:(lia) V) as [Addr Bounds].
     do 3 eexists;split;[reflexivity|split;[exact SP|]].
     constructor;[|constructor];intros x X;apply Bounds.
     change (word(regs s 4%nat+d)<=x<word(regs s 4%nat+d)+64) in X.
     now rewrite SP,Addr in X.
Qed.

Theorem sequence origin text low cap base ops : 0<=low -> fits64 base cap ->
 forallb (fun p=>local low cap (snd p)) ops=true ->
 forall off s carry, 0<=off -> decoded text off ops -> regs s 4%nat=base ->
 exists t c ws, run (length ops) (ScalarBytes.fetch origin text) (State (Running off) s carry)=
                Some(State (Running (off+width ops)) t c,ws) /\
 regs t 4%nat=base /\ confined (fun x=>base+low<=x<base+cap) ws.
Proof.
 intros Low Fit;induction ops as [|[n op] rest IH];intros All off s carry O Bytes SP.
 - exists s,carry,[];cbn [width fold_right];rewrite Z.add_0_r;repeat split;auto;constructor.
 - apply Bool.andb_true_iff in All as [Valid All]. destruct Bytes as [D Rest].
   destruct (next _ _ _ origin off n _ _ carry Valid Low Fit SP) as [mid [cf [own [One [M W]]]]].
   destruct (IH All (off+Z.of_nat n) _ cf ltac:(lia) Rest M) as [t [c [ws [Steps [T Safe]]]]].
   exists t,c,(own++ws);split;[|split;[exact T|apply Forall_app;auto]].
   cbn [length run];unfold ScalarBytes.fetch at 1;cbn [loc cpu_state ScalarBytes.cf].
   cbn [snd] in One. rewrite (proj2 (Z.ltb_ge _ _) O),D,One,Steps.
   cbn [option_map width fold_right fst] in *;now rewrite Z.add_assoc.
Qed.

Lemma prefix_decoded text a xs : forall ys, decoded text a (xs++ys) ->
 decoded text a xs /\ decoded text (a+width xs) ys.
Proof.
 revert a;induction xs as [|[n op] xs IH];intros a ys B.
 - cbn [width fold_right decoded];rewrite Z.add_0_r;split;[exact I|exact B].
 - destruct B as [D B]. destruct (IH (a+Z.of_nat n) ys B) as [L R].
   split;[split;assumption|]. cbn [width fold_right fst] in R|-*;now rewrite Z.add_assoc.
Qed.
