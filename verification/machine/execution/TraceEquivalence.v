From Coq Require Import List ZArith Bool Lia FSets.FMapPositive.
From Machine Require Import isa.Instructions execution.Blocks execution.Lane
  execution.MaskTrace execution.CircuitFacts execution.LaneTrace.
Import ListNotations. Local Open Scope Z_scope.

(* Translation validation for a changed instruction schedule. Both traces
   must reproduce the same circuit wires at the requested memory addresses.
   The hash table is only a search hint: every hit checks the gate itself. *)
Definition gate_eq (a b:gate) : {a=b}+{a<>b}.
Proof. decide equality; auto using arg_dec,Nat.eq_dec,Bool.bool_dec. Defined.

Fixpoint arg_key a := match a with
 | Lit n=>5*n | Initial r=>5*Z.of_nat r+1 | Wire i=>5*Z.of_nat i+2
 | Input r i=>5*(65599*Z.of_nat r+Z.of_nat i)+3 | UpperCleared b=>5*arg_key b+4 end.
Definition gate_key g :=
 let tag:=match g with AddQ _ _=>1 | SubQ _ _=>2 | MulQ _ _=>3 | AndQ _ _=>4
 | ShiftQ _ n=>32+2*Z.of_nat n | LeftQ _ n=>33+2*Z.of_nat n
 | MaddQ false _ _ _=>5 | MaddQ true _ _ _=>6 | EqQ _ _=>7 | OrK _ _=>8
 | MinUQ _ _=>9 | LessUQ _ _=>10 end in
 Z.to_pos (1 + fold_left (fun h a=>(65599*h+arg_key a) mod 2147483647) (arguments g) tag).
Definition table := PositiveMap.t (gate*nat).
Definition lookup_gate (t:table) g :=
 match PositiveMap.find (gate_key g) t with
 | Some (old,i) => if gate_eq old g then Some i else None | None=>None end.
Record builder := Builder { memo:table; next:nat; gates_rev:list gate }.
Definition insert b g :=
 let i:=next b in Builder (PositiveMap.add (gate_key g) (g,i) (memo b)) (S i) (g::gates_rev b).
Definition emit b g := match lookup_gate (memo b) g with
 | Some i=>Some (b,Wire i) | None=>Some (insert b g,Wire (next b)) end.
Definition seed := Builder (PositiveMap.empty _) 0 [].
Record symbols := Symbols { reg:nat->arg; mem:pointer->option arg }.
Definition initial := Symbols Initial (fun a=>if 0<=?snd a then Some (Input (fst a) (Z.to_nat (snd a))) else None).
Definition writes s dst v := Symbols (put (reg s) dst v) (mem s).

Section Run.
Variable T:Type.
Variable emit_gate : T -> gate -> option (T*arg).
Definition step (t:T) s a := match a with
 | Vector (dst,op) addr =>
   let read (_:nat) (_:Z) := match addr with Some p=>mem s p | None=>Some (Lit 0) end in
   match lower_vector read (reg s) dst op with
   | Some (Existing v)=>Some (t,writes s dst v)
   | Some (Compute g)=> match emit_gate t g with Some (t',v)=>Some (t',writes s dst v) | None=>None end
   | None=>None end
 | LoadCell r a => match mem s a with Some v=>Some (t,writes s r v) | None=>None end
 | StoreCell r a => Some (t,Symbols (reg s) (fun p=>if ptr_eq p a then Some (reg s r) else mem s p))
 | Constant r n => Some (t,writes s r (Lit n))
 | UpperZero => Some (t,Symbols (fun r=>if Nat.ltb r 16 then UpperCleared (reg s r) else reg s r) (mem s))
 end.
Fixpoint execute t s xs := match xs with []=>Some(t,s) | a::tail=>
 match step t s a with Some(t',s')=>execute t' s' tail | None=>None end end.
End Run.

Definition circuit_for x y :=
 match execute _ emit seed initial x with
 | Some(b,_)=>match execute _ emit b initial y with Some(c,_)=>rev (gates_rev c) | None=>[] end
 | None=>[] end.
Fixpoint dictionary gs (i:nat) (t:table) := match gs with []=>t | g::tl=>
 dictionary tl (S i) (PositiveMap.add (gate_key g) (g,i) t) end.
Definition replay_gate (t:table) (_:unit) g := option_map (fun i=>(tt,Wire i)) (lookup_gate t g).
Definition same_cell x y a := match mem x a, mem y a with
 | Some u,Some v=>if arg_dec u v then true else false | _,_=>false end.
Definition check gs x y output :=
 let t:=dictionary gs O (PositiveMap.empty _) in
 ordered O gs && match execute _ (replay_gate t) tt initial x,execute _ (replay_gate t) tt initial y with
 | Some(_,a),Some(_,b)=>forallb (same_cell a b) output | _,_=>false end.

Section Sound.
Variable j:nat.
Variable original:lane.
Variable gs:list gate.
Let v := value j gs (fun r i=>cells original (r,Z.of_nat i)) (registers original).
Definition models s (l:lane) :=
 (forall r, v(reg s r)=registers l r) /\
 (forall a u,mem s a=Some u -> v u=cells l a).
Lemma starts : models initial original.
Proof.
 split;[reflexivity|]. intros [r off] u;cbn [initial mem fst snd].
 destruct (0<=?off) eqn:E;try discriminate;intros [= <-].
 apply Z.leb_le in E;unfold v,value;cbn [operand];now rewrite Z2Nat.id by exact E.
Qed.
Definition consistent (t:table) := forall k g i, PositiveMap.find k t=Some(g,i) ->
 v (Wire i)=denote v g.
Lemma build_consistent tail n t : satisfies v n tail -> consistent t -> consistent (dictionary tail n t).
Proof.
 revert n t;induction tail as [|g tail IH];intros n t S C;[exact C|];apply IH.
 - intros i h E;replace (Datatypes.S n+i)%nat with (n+Datatypes.S i)%nat by lia;apply S;exact E.
 - intros k h i E;destruct(Pos.eq_dec k (gate_key g))as[->|N].
   + rewrite PositiveMap.gss in E;injection E as <- <-;replace n with (n+0)%nat at 1 by lia;apply S;reflexivity.
   + rewrite PositiveMap.gso in E by congruence;eapply C;exact E.
Qed.
Lemma checked_gate t u g u' a : consistent t -> replay_gate t u g=Some(u',a) -> v a=denote v g.
Proof.
 intros C;unfold replay_gate,lookup_gate;destruct(PositiveMap.find _ t)as[[h i]|]eqn:F;try discriminate.
 destruct(gate_eq h g)as[->|];try discriminate;intros[= <- <-];now apply(C _ _ _ F).
Qed.
Lemma write_models s l d u z : models s l -> v u=z ->
 models (writes s d u) (Lane (put (registers l) d z) (cells l)).
Proof. intros [R M] V;split;[intro r;unfold writes;cbn;unfold put;destruct(Nat.eqb d r);auto|exact M]. Qed.
Lemma step_models t u s a u' s' l : consistent t -> models s l ->
 step _ (replay_gate t) u s a=Some(u',s') -> models s' (perform j l a).
Proof.
 intros C [R M];destruct a as [[d op] addr|d addr|d addr|d n|];cbn [step perform].
 - set (rd:=fun (_:nat) (_:Z)=>match addr with Some p=>mem s p | None=>Some (Lit 0) end).
   set (load:=fun (_:nat) (_:Z)=>match addr with Some p=>cells l p | None=>0 end).
   assert (Read:forall b off a,rd b off=Some a -> v a=load b off).
   { unfold rd,load;destruct addr;[apply (fun b off=>M p)|intros b off a [= <-];reflexivity]. }
   destruct(lower_vector rd (reg s) d op)as[[a|g]|]eqn:E;try discriminate.
   + intros [= <- <-];apply write_models;[now split|].
     pose proof(lower_vector_correct _ _ _ _ _ v _ Read eq_refl E)as H.
     change (v a=bits load (registers l) d op). rewrite H;destruct op;cbn [bits];now rewrite ?R.
   + destruct(replay_gate t u g)as[[u0 a]|]eqn:G;try discriminate;intros [= <- <-].
     apply write_models;[now split|]. rewrite (checked_gate _ _ _ _ _ C G).
     pose proof(lower_vector_correct _ _ _ _ _ v _ Read eq_refl E)as H.
     change (denote v g=bits load (registers l) d op). rewrite H;destruct op;cbn [bits];now rewrite ?R.
 - destruct(mem s addr)as[a|]eqn:E;try discriminate;intros[= <- <-];apply write_models;[now split|exact (M _ _ E)].
 - intros[= <- <-];split;[exact R|];intros k a;cbn [mem cells];destruct(ptr_eq k addr);[intros[= <-];apply R|apply M].
 - intros[= <- <-];apply write_models;[now split|reflexivity].
 - intros[= <- <-];split;[|exact M];intro r;cbn [reg registers];destruct(Nat.ltb r 16);cbn [andb];[|apply R].
   unfold v,value;cbn [operand];destruct(Nat.ltb_spec j 2), (Nat.leb_spec 2 j);try lia;try reflexivity;apply R.
Qed.
Lemma execute_models t xs s s' u u' l : consistent t -> models s l ->
 execute _ (replay_gate t) u s xs=Some(u',s') -> models s' (fold_left (perform j) xs l).
Proof.
 intros C;revert u s l;induction xs as[|a xs IH];intros u s l M E;[injection E as <- <-;exact M|].
 cbn [execute] in E;destruct(step _ _ u s a)as[[u0 s0]|]eqn:S;try discriminate.
 eapply IH;[eapply step_models;eassumption|exact E].
Qed.
Theorem check_sound x y out : check gs x y out=true -> forall a,In a out ->
 cells (fold_left (perform j) x original) a = cells (fold_left (perform j) y original) a.
Proof.
 unfold check;rewrite andb_true_iff;intros[O E].
 set (t:=dictionary gs 0 (PositiveMap.empty _)) in *.
 assert(C:consistent t).
 { apply build_consistent;[apply evaluated_gates,O|intros k g i H;rewrite PositiveMap.gempty in H;discriminate]. }
 destruct(execute _ _ tt initial x)as[[u s]|]eqn:X;try discriminate.
 destruct(execute _ _ tt initial y)as[[u' s']|]eqn:Y;try discriminate.
 intros a A;apply forallb_forall with (x:=a) in E;auto;unfold same_cell in E.
 destruct(mem s a)as[h|]eqn:L;try discriminate;destruct(mem s' a)as[h'|]eqn:R;try discriminate.
 destruct(arg_dec h h')as[->|];try discriminate.
 rewrite <-(proj2 (execute_models _ _ _ _ _ _ _ C starts X) _ _ L).
 exact (proj2 (execute_models _ _ _ _ _ _ _ C starts Y) _ _ R).
Qed.
End Sound.
