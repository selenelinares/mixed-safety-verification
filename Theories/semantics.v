Require Import Coq.Strings.String.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype choice seq ssrnum ssrint ssralg bigop.

From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun fperm.

From CoqUtils Require Import nominal.

From memsafe Require Import syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Structured.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.


Notation locals := {fmap string -> value}.
Notation heap := {fmap ptr -> value}.

Implicit Types (ls : locals) (h : heap) (x : string) (s : locals * heap).
Implicit Types (A : {fset name}).


(* Variable T : restrType. *)

Definition eval_binop b v1 v2 :=
  match b, v1, v2 with
  | Add, VNum n1, VNum n2 => VNum (n1 + n2)
  | Add, VPtr p sz, VNum n
  | Add, VNum n, VPtr p sz => VPtr (p.1, p.2 + n) sz
  | Add, _, _ => VNil
  | Sub, VNum n1, VNum n2 => VNum (n1 - n2)
  | Sub, VPtr p sz, VNum n => VPtr (p.1, p.2 - n) sz
  | Sub, _, _ => VNil
  | Mul, VNum n1, VNum n2 => VNum (n1 * n2)
  | Mul, _, _ => VNil
  | Eq, _, _ => VBool (v1 == v2)
  | Leq, VNum n1, VNum n2 => VBool (n1 <= n2)
  | Leq, _, _ => VNil
  | And, VBool b1, VBool b2 => VBool (b1 && b2)
  | And, _, _ => VNil
  | Or, VBool b1, VBool b2 => VBool (b1 || b2)
  | Or, _, _ => VNil
  end%R.

(** Function [eval_expr] computes the value of an expression [e] given a local
store [ls]. It takes an additional argument [cast] which determines how the cast
operator is interpreted: when [cast = true], cast is just the identity; when
[cast = false], cast converts the block identifier to an integer. *)

Fixpoint eval_expr cast e ls :=
  match e with
  | Var x => odflt VNil (ls x)
  | Bool b => VBool b
  | Num n => VNum n
  | Binop b e1 e2 => eval_binop b (eval_expr cast e1 ls) (eval_expr cast e2 ls)
  | ENil => VNil
  | Neg e =>
    if eval_expr cast e ls is VBool b then VBool (~~ b)
    else VNil
  | Offset e =>
    if eval_expr cast e ls is VPtr p _ then VNum p.2 else VNil
  | Size e =>
    if eval_expr cast e ls is VPtr _ sz then VNum sz else VNil
  | Cast e =>
    let v := eval_expr cast e ls in
    if cast then v
    else if eval_expr cast e ls is VPtr p _ then VNum (val p.1) else VNil
  end.


Section Result.

Inductive error := 
| OutofBoundsRead 
| OutofBoundsWrite
| OutofBoundsFree
| Other.

Definition mem_safety_errors := [:: OutofBoundsRead; OutofBoundsWrite; OutofBoundsFree].

Canonical error_indDef := [indDef for error_rect].
Canonical error_indType := IndType error error_indDef.
Definition error_eqMixin := [derive eqMixin for error].
Canonical error_eqType := EqType error error_eqMixin.
Definition error_choiceMixin := [derive choiceMixin for error].
Canonical error_choiceType := Eval hnf in ChoiceType error error_choiceMixin.
Definition error_ordMixin := [derive ordMixin for error].
Canonical error_ordType := OrdType error error_ordMixin.
Canonical error_nominalType := Eval hnf in [nominalType for error by //].

Canonical error_trivialNominalType := Eval hnf in [trivialNominalType for error].

(** Type of results of computations. [Done x] indicates that a
computation successfully terminated, returning [x] as a
result. [Error] indicates that an error occurred. [NotYet] indicates
that the computation ran for too many steps and couldn't complete. *)
Variable T : Type.

Inductive result :=
| Done of T
| Error of error
| NotYet.

Definition sum_of_result r :=
  match r with
  | Done x => inl x
  | Error e => inr (inl e)
  | NotYet => inr (inr tt)
  end.

Definition result_of_sum r :=
  match r with
  | inl x => Done x
  | inr (inl e) => Error e
  | inr (inr tt) =>NotYet
  end.
Lemma sum_of_resultK : cancel sum_of_result result_of_sum.
Proof. case; simpl.
         reflexivity.
       (case; simpl; reflexivity).
      reflexivity. 
Qed.
Lemma result_of_sumK : cancel result_of_sum sum_of_result.
Proof. by do ![case=>//]. Qed.

End Result.

Arguments Error {_}.
Arguments NotYet {_}.



Definition result_eqMixin (T : eqType):=
  CanEqMixin (@sum_of_resultK T).
Canonical result_eqType (T : eqType) :=
  Eval hnf in EqType (result T) (result_eqMixin T).
Definition result_choiceMixin (T : choiceType) :=
  CanChoiceMixin (@sum_of_resultK T).
Canonical result_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (result T) (result_choiceMixin T).
Definition result_ordMixin (T : ordType) :=
  CanOrdMixin (@sum_of_resultK T).
Canonical result_ordType (T : ordType) :=
  Eval hnf in OrdType (result T) (result_ordMixin T).
Definition result_nominalMixin (T : nominalType) :=
  BijNominalMixin (@sum_of_resultK T) (@result_of_sumK T).
Canonical result_nominalType (T : nominalType) :=
  Eval hnf in NominalType (result T) (result_nominalMixin T).


Section Nominal.

Variable T : nominalType.

Global Instance Done_eqvar : {eqvar @Done T}.
Proof. by move=> s x _ <-. Qed.

Lemma renamevE pm v :
  rename pm v =
  match v with
  | VBool b => VBool b
  | VNum n => VNum n
  | VPtr p sz => VPtr (rename pm p) sz
  | VNil => VNil
  end.
Proof. by case: v. Qed.

Lemma namesvE v :
  names v =
  match v with
  | VPtr p _ => fset1 p.1
  | _ => fset0
  end.
Proof.
by case: v=> [b|n|[i n] ?|] //=; rewrite -2![RHS]fsetU0.
Qed.

Lemma renameresE pm (r : result T) :
  rename pm r =
  match r with
  | Done x => Done (rename pm x)
  | Error e => Error e
  | NotYet => NotYet
  end.
Proof.  
case: r; simpl.
reflexivity.
(case; simpl; reflexivity).
reflexivity.
Qed. 

Lemma namesresE (r : result T) :
  names r = if r is Done x then names x else fset0.
Proof.  
    case: r; simpl.
    reflexivity.
    (case; simpl; reflexivity).
    reflexivity.
Qed. 

End Nominal.


Section Monotonicity.

(** The semantics defined as a function is consistent, in the sense
that increasing the maximum number of steps it can run for, can only
cause it to produce a better result. *)

Definition refine_result (T : eqType) (r1 r2 : result T) :=
  (r1 == NotYet) || (r1 == r2).


End Monotonicity.


Definition stateu s1 s2 : locals * heap :=
  (unionm s1.1 s2.1, unionm s1.2 s2.2).


Section Restriction.

Variable T : restrType.

Definition hide_result A (r : result T) :=
  match r with
  | Done x => Done (hide A x)
  | Error e => Error e
  | NotYet => NotYet
  end.


Lemma hide_result_law : Restriction.law hide_result.
Proof.
rewrite /hide_result; constructor.
- move=> s A _ <- [x| e|] _ <- //=; finsupp.
- by move=> A [x| e|] //; rewrite hideI.
- by move=> ?? [x| e|] //; rewrite hideU.
- by move=> [x| e|] //; rewrite hide0.
by move=> ? [x| e|] /=; rewrite ?hideP ?fdisjoints0.
Qed.

Definition result_restrMixin := RestrMixin hide_result_law.
Canonical result_restrType := RestrType (result T) result_restrMixin.

End Restriction.


Global Instance match_result_eqvar
  (T : nominalType) S {eS : nominalRel S}
  π (r1 r2 : result T) b11 b12 b21 b22 b31 b32 :
  nomR π r1 r2 ->
  nomR π b11 b12 ->
  nomR π b21 b22 ->
  nomR π b31 b32 ->
  nomR π 
       match r1 with
       | Done x => b11 x : S
       | Error e => b21 e 
       | NotYet => b31
       end
       match r2 with
       | Done x => b12 x 
       | Error e => b22 e
       | NotYet => b32
       end.
Proof.
case: r1 => [?|?|] // <- ; finsupp.
Qed.

Definition bind_res (T S : nominalType) A (f : T -> result {restr S}) (rx : result {restr T}) :=
  match rx with
  | Done rx => bindr A f rx
  | Error e   => Error e
  | NotYet  => NotYet
  end.

Global Instance bind_res_eqvar
  (T S : nominalType) A (f : T -> result {restr S}) :
  {finsupp A f} -> {finsupp A bind_res A f}.
Proof. 
  rewrite /bind_res; finsupp.
Qed.

Definition pbind_res (T : nominalType) A (P : T -> Prop) (rx : result {restr T}) :=
  forall (rx' : {restr T}), rx = Done rx' -> pbindr A P rx'.

Lemma pbind_resE (T : nominalType) A (P : T -> Prop) (rx : {restr T}) :
  pbind_res A P (Done rx) <-> pbindr A P rx.
Proof. by split; [move=> /(_ rx erefl)|move=> ? _ [<-]]. Qed.

Lemma hide_pbind_res (T : nominalType) A A' (P : T -> Prop) (rx : result {restr T}) :
  {finsupp A P} -> fdisjoint A A' -> pbind_res A P (hide A' rx) <-> pbind_res A P rx.
Proof.
case: rx => [rx| |] //= fs dis.
by rewrite -[hide A' (Done rx)]/(Done (hide A' rx)) 2!pbind_resE hide_pbindr.
Qed.


Lemma pbind_res_bind (T S : nominalType) A1 A2 A3
                     (P : T -> Prop) (Q : S -> Prop)
                     (f : T -> result {restr S}) (rx : result {restr T}) :
  {finsupp A1 P} ->
  {finsupp A2 Q} ->
  {finsupp A3 f} ->
  (forall x : T, P x -> pbind_res A2 Q (f x)) ->
  pbind_res A1 P rx ->
  pbind_res A2 Q (bind_res A3 f rx).
Proof.
move=> fs1 fs2 fs3 Pf.
case: rx => [rx| |] //=.
case/(restrP (A1 :|: A2 :|: A3)): rx => /= A4 x.
rewrite 2!fdisjointUl -andbA => /and3P [dis1 dis2 dis3] sub.
rewrite pbind_resE pbindrE // => Px.
rewrite bindrE // hide_pbind_res //.
by apply: Pf.
Qed.

Lemma pbind_res_impl (T : nominalType) A1 A2 (P1 P2 : T -> Prop) rx :
  {finsupp A1 P1} ->
  {finsupp A2 P2} ->
  (forall x : T, P1 x -> P2 x) ->
  pbind_res A1 P1 rx -> pbind_res A2 P2 rx.
Proof.
move: rx => [rx| |] //=; rewrite 2!pbind_resE; exact: pbindr_impl.
Qed.

Definition mkblock (b : name) vs : heap :=
  uncurrym (setm emptym b
                 (mkfmapfp (fun i => if i is Posz n then
                                       Some (nth VNil vs n)
                                     else None)
                           [seq Posz n | n <- iota 0 (size vs)])).

Lemma mkblockE p b vs :
  mkblock b vs p =
  if p.1 == b then
    if p.2 is Posz n then
      if n < size vs then Some (nth VNil vs n)
      else None
    else None
  else None.
Proof.
rewrite /mkblock uncurrymE setmE.
case: ifP=> //= _; rewrite mkfmapfpE.
case: p.2=> [n|n] /=.
  rewrite mem_map; last by move=> ?? [->].
  by rewrite mem_iota /= add0n.
by case: ifP.
Qed.

Global Instance mkblock_eqvar : {eqvar mkblock}.
Proof.
move=> s i _ <- vs _ <-.
eapply getm_nomR => - [i' [n|n]] _ <-; rewrite !mkblockE /=; last by finsupp.
rewrite -[size (rename s vs)]size_eqvar renameT; finsupp.
Qed.


Fixpoint eval_com c s k : result {restr locals * heap} :=
  if k is S k' then
    match c with
    | Assn x e =>
      Done (Restr (setm s.1 x (eval_expr true e s.1), s.2))

    | Load x e =>
      if eval_expr true e s.1 is VPtr p _ then
        if s.2 p is Some v then Done (Restr (setm s.1 x v, s.2))
        else Error OutofBoundsRead
      else Error Other

    | Store e e' =>
      if eval_expr true e s.1 is VPtr p _ then
        if updm s.2 p (eval_expr true e' s.1) is Some h' then Done (Restr (s.1, h'))
        else Error OutofBoundsWrite
      else Error Other

    | Alloc x e =>
      if eval_expr true e s.1 is VNum (Posz n) then
        Done (new (names s) (fun i =>
                Restr (setm s.1 x (VPtr (i, 0 : int) n),
                       unionm (mkblock i (nseq n (VNum 0))) s.2)))
      else Error Other

    | Free e =>
      if eval_expr true e s.1 is VPtr p _ then
        if p.2 == 0 then
          if p.1 \in domm (currym s.2) then
            Done (Restr (s.1, filterm (fun (p' : ptr) _ => p'.1 != p.1) s.2))
          else Error OutofBoundsFree
        else Error Other
      else Error Other  

    | Skip => Done (Restr s)

    | Seq c1 c2 => bind_res fset0 (fun s' => eval_com c2 s' k') (eval_com c1 s k')

    | If e ct ce =>
      if eval_expr true e s.1 is VBool b then
        eval_com (if b then ct else ce) s k'
      else Error Other

    | While e c =>
      if eval_expr true e s.1 is VBool b then
        eval_com (if b then Seq c (While e c) else Skip) s k'
      else Error Other
    end
  else NotYet.

Global Instance eval_binop_eqvar b : {eqvar eval_binop b}.
Proof.
by case: b => [] π [b1|n1|p1 sz1|] _ <- [b2|n2|p2 sz2|] _ <- //=; finsupp.
Qed.

Global Instance eval_expr_eqvar e : {eqvar eval_expr true e}.
Proof.
move=> π ls _ <-; elim: e=> [x|b|n|b e1 IH1 e2 IH2|e IH| |e IH|e IH|e IH] //=.
- rewrite renamemE /= renameT.
  by case: (ls x)=> [v|] //=.
- by rewrite -IH1 -IH2; apply: eval_binop_eqvar.
- by rewrite -IH; case: eval_expr.
- by rewrite -IH; case: eval_expr.
by rewrite -IH; case: eval_expr.
Qed.

Global Instance match_value_eqvar
  T {eT : nominalRel T}
  π v1 v2 b11 b12 b21 b22 b31 b32 b41 b42 :
  nomR π v1 v2 ->
  nomR π b11 b12 ->
  nomR π b21 b22 ->
  nomR π b31 b32 ->
  nomR π b41 b42 ->
  nomR π
       match v1 with
       | VBool x => b11 x : T
       | VNum x => b21 x
       | VPtr x sz => b31 x sz
       | VNil => b41
       end
       match v2 with
       | VBool x => b12 x : T
       | VNum x => b22 x
       | VPtr x sz => b32 x sz
       | VNil => b42
       end.
Proof. by move=> <- ????; case: v1=> * /=; finsupp. Qed.

Global Instance match_int_eqvar
  T {eT : nominalRel T}
  π n1 n2 b11 b12 b21 b22 :
  nomR π n1 n2 ->
  nomR π b11 b12 ->
  nomR π b21 b22 ->
  nomR π
       match n1 with
       | Posz x => b11 x : T
       | Negz x => b21 x
       end
       match n2 with
       | Posz x => b12 x : T
       | Negz x => b22 x
       end.
Proof. by move=> <- ? ?; case: n1=> // n; finsupp. Qed.


Hint Extern 4 (@nomR ?S ?cS ?π (?f1 ?x1) (?f2 ?x2)) =>
  let T  := type of x1 in
  let cT := constr:(_ : nominalRel T) in
  eapply (@nomR_app T S cT cS π f1 f2 x1 x2) : typeclass_instances.

Global Instance eval_com_eqvar : {eqvar eval_com}.
Proof.
  move=> π c1 c2 c1c2 s1 s2 s1s2 k _ <-; rewrite renameT.
  elim: k π c1 c2 c1c2 s1 s2 s1s2 => [|k IH] π c _ <- s1 s2 s1s2 //=.
  case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=; by finsupp.
  Qed.


(** Set of variables occurring in an expression. *)
Fixpoint vars_e e :=
  match e with
  | Var x => fset1 x
  | Bool _ => fset0
  | Num _ => fset0
  | Binop _ e1 e2 => vars_e e1 :|: vars_e e2
  | ENil => fset0
  | Neg e => vars_e e
  | Offset e => vars_e e
  | Size e => vars_e e
  | Cast e => vars_e e
  end.

(** Set of variables occurring in a command. *)
Fixpoint vars_c c :=
  match c with
  | Assn x e => x |: vars_e e
  | Load x e => x |: vars_e e
  | Store e e' => vars_e e :|: vars_e e'
  | Alloc x e => x |: vars_e e
  | Free e => vars_e e
  | Skip => fset0
  | Seq c1 c2 => vars_c c1 :|: vars_c c2
  | If e ct ce => vars_e e :|: vars_c ct :|: vars_c ce
  | While e c => vars_e e :|: vars_c c
  end.

(** Potentially modified variables in a command. *)
Fixpoint mod_vars_c c :=
  match c with
  | Assn x _   => fset1 x
  | Load x _   => fset1 x
  | Store _ _  => fset0
  | Alloc x _  => fset1 x
  | Free _     => fset0
  | Skip       => fset0
  | Seq c1 c2  => mod_vars_c c1 :|: mod_vars_c c2
  | If _ c1 c2 => mod_vars_c c1 :|: mod_vars_c c2
  | While _ c  => mod_vars_c c
  end.


End Structured.

Arguments Error {_}.
Arguments NotYet {_}.

Infix "∪" := stateu (at level 40, left associativity) : state_scope.

Instance stateu_eqvar : {eqvar stateu}.
Proof. by rewrite /stateu; finsupp. Qed.