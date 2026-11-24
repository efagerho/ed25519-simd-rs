From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.StoreInstructions
 execution.WordSemantics memory.ByteMemory memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* Scalar forms needed by the verdict scatter and the empty-batch return.
   The PC is a byte offset in the linked text. RET yields an absolute IP. *)
Inductive addr := Address (base:nat) (index:option (nat*Z)) (disp:Z).
Inductive condition := Equal | Below | Above | AtLeast.
Inductive instruction :=
| Load64 (r:nat) (a:addr) | Load8 (r:nat) (a:addr) | Store8 (i:indexed_byte)
| CompareImm (r:nat) (k:Z) | Compare (l r:nat) | Test (r:nat)
| Zero32 (r:nat) | OneEax | And8 (d r:nat) | ShrEax | Inc (r:nat)
| Branch (c:condition) (disp:Z) | Ret.

Definition decode (bs:list Z) : option (nat*instruction) := match bs with
 | 0x48::0x8b::0x4f::0x48::_ => Some (4%nat,Load64 1 (Address 7 None 72))
 | 0x48::0x83::0xf9::0x08::_ => Some (4%nat,CompareImm 1 8)
 | 0x45::0x31::0xc0::_ => Some (3%nat,Zero32 8)
 | 0x48::0x85::0xc9::_ => Some (3%nat,Test 1)
 | 0x48::0x85::0xf6::_ => Some (3%nat,Test 6)
 | 0x4e::0x8b::0x4c::0xc7::0x08::_ => Some (5%nat,Load64 9 (Address 7 (Some (8%nat,8)) 8))
 | 0x49::0x39::0xd1::_ => Some (3%nat,Compare 9 2)
 | 0x46::0x8a::0x14::0x07::_ => Some (4%nat,Load8 10 (Address 7 (Some (8%nat,1)) 0))
 | 0x41::0x20::0xc2::_ => Some (3%nat,And8 10 0)
 | 0x46::0x88::0x14::0x0e::_ => Some (4%nat,Store8 (IndexedByte 10 6 9))
 | 0xd1::0xe8::_ => Some (2%nat,ShrEax)
 | 0x49::0xff::0xc0::_ => Some (3%nat,Inc 8)
 | 0x49::0x39::0xc8::_ => Some (3%nat,Compare 8 1)
 | 0xb8::0x01::0x00::0x00::0x00::_ => Some (5%nat,OneEax)
 | 0x31::0xc0::_ => Some (2%nat,Zero32 0)
 | 0x77::d::_ => Some (2%nat,Branch Above (signed_value 128 d))
 | 0x74::d::_ => Some (2%nat,Branch Equal (signed_value 128 d))
 | 0x73::d::_ => Some (2%nat,Branch AtLeast (signed_value 128 d))
 | 0x72::d::_ => Some (2%nat,Branch Below (signed_value 128 d))
 | 0x0f::0x84::a::b::c::d::_ => Some (6%nat,Branch Equal (displacement32 [a;b;c;d]))
 | 0xc3::_ => Some (1%nat,Ret) | _=>None end.

Definition effective s a := match a with Address b ix d=>word (regs s b+
 (match ix with Some (i,k)=>regs s i*k | None=>0 end)+d) end.
Definition low_byte s d v := set s d (regs s d-regs s d mod 256+v mod 256).
Definition with_zf s z := CPU (regs s) (vectors s) (Some z) (mem s).
Inductive location := Running (off:Z) | Returned (ip:Z).
Record state := State { loc:location; cpu_state:cpu; cf:option bool }.
Definition eval_condition cc z c :=
 match cc with Equal=>z | Below=>c | AtLeast=>option_map negb c
 | Above=>match z,c with Some z,Some c=>Some (negb(z||c)) | _,_=>None end end.
Definition step origin off n op s carry : option (state*list store) :=
 let next:=off+Z.of_nat n in
 let go s c := Some (State (Running next) s c,[]) in
 let cmp a b:=go (with_zf s (a=?b)) (Some (a<?b)) in
 match op with
 | Load64 r a=>go (set s r (read_word (mem s) (effective s a))) carry
 | Load8 r a=>go (low_byte s r (mem s (effective s a))) carry
 | Store8 i=>let '(out,ws):=byte_step (word (origin+off)) i s in
      Some (State (Running next) out carry,ws)
 | CompareImm r k=>cmp (word (regs s r)) k
 | Compare l r=>cmp (word (regs s l)) (word (regs s r))
 | Test r=>go (with_zf s (word(regs s r)=?0)) (Some false)
 | OneEax=>go (set s 0 1) carry
 | Zero32 r=>go (with_zf (set s r 0) true) (Some false)
 | And8 d r=>let v:=Z.land (regs s d mod 256) (regs s r mod 256) in
      go (with_zf (low_byte s d v) (v=?0)) (Some false)
 | ShrEax=>let v:=regs s 0%nat mod 2^32 in let t:=v/2 in
      go (with_zf (set s 0 t) (t=?0)) (Some (Z.odd v))
 | Inc r=>let t:=word(regs s r+1) in go (with_zf (set s r t) (t=?0)) carry
 | Branch cc d=>option_map (fun take:bool=>(State (Running (if take then next+d else next)) s carry,[]))
     (eval_condition cc (flag s) carry)
 | Ret=>let '(ip,out):=caller_step 0 0 Return s in Some (State (Returned ip) out carry,[])
 end.

Definition fetch origin text st := match loc st with Returned _=>None | Running off=>
 if off<?0 then None else
 match decode (skipn (Z.to_nat off) text) with Some (n,op)=>step origin off n op (cpu_state st) (cf st)
 | None=>None end end.
Inductive steps origin text : state -> list store -> state -> Prop :=
| stop s : steps origin text s [] s
| advance s mid last ws tail : fetch origin text s=Some(mid,ws) ->
    steps origin text mid tail last -> steps origin text s (ws++tail) last.

Lemma step_memory o off n op s c t ws : step o off n op s c=Some(t,ws) ->
 mem (cpu_state t)=WriteTrace.replay (mem s) ws.
Proof.
 destruct op;cbn [step];try solve [intro E;injection E as <- <-;reflexivity].
 destruct (eval_condition _ _ _) as [[]|];intro E;try discriminate;injection E as <- <-;reflexivity.
Qed.
Theorem steps_memory o text s ws t : steps o text s ws t ->
 mem (cpu_state t)=WriteTrace.replay (mem (cpu_state s)) ws.
Proof.
 induction 1 as [|s mid last ws tail F R IH];[reflexivity|].
 unfold fetch in F;destruct (loc s);try discriminate. destruct (_<?_);try discriminate.
 destruct (decode _) as [[n op]|];try discriminate. rewrite replay_app,<-(step_memory _ _ _ _ _ _ _ _ F);exact IH.
Qed.

Fixpoint observe fuel origin text st : state * list store := match fuel with
| O=>(st,[]) | S n=>match fetch origin text st with
 | Some (mid,ws)=>let '(t,tail):=observe n origin text mid in (t,ws++tail)
 | None=>(st,[]) end end.
Lemma observe_steps fuel origin text : forall st,
 let '(t,ws):=observe fuel origin text st in steps origin text st ws t.
Proof.
 induction fuel as [|n IH];intros st;cbn [observe];[constructor|].
 destruct (fetch _ _ _) as [[mid ws]|] eqn:F;[|constructor].
 specialize (IH mid);destruct (observe _ _ _ _) as [t tail];eapply advance;eauto.
Qed.

(* Any prefix starting at the same state is an initial segment of a known
   terminating execution. This also supplies progress at every live prefix. *)
Lemma prefix_of_return o text s full last : steps o text s full last ->
 forall ip, loc last=Returned ip ->
 forall pre mid, steps o text s pre mid ->
 exists tail, full=pre++tail /\ steps o text mid tail last.
Proof.
 induction 1 as [s|s next last ws rest F R IH];intros ip End pre mid P.
 - inversion P as [|a b f w t Step Run];subst.
   + exists [];split;[reflexivity|constructor].
   + unfold fetch in Step;rewrite End in Step;discriminate.
 - inversion P as [|a b f w t Step Run];subst.
   + exists (ws++rest);split;[reflexivity|eapply advance;eauto].
   + rewrite F in Step;injection Step as <- <-.
     destruct (IH ip End _ _ Run) as [tail [-> T]]. exists tail;split;[apply app_assoc|exact T].
Qed.
