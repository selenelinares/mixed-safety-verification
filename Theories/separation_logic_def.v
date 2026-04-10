(*In this file, the definition of the separating conjunction operator was taken from Arthur's formalisation. We adapted Arthur's definition of triple to our set of errors, which resulted in mem_safe_triple.*)
Require Import Coq.Strings.String.

From Coq Require Import Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssrnum ssrint seq.
From mathcomp Require Import eqtype choice seq order. 
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun fperm.

From CoqUtils Require Import nominal.

From memsafe Require Import syntax semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Definitions.


Local Open Scope fset_scope.
Local Open Scope state_scope.

Local Notation locals := {fmap string -> value}.
Local Notation heap := {fmap ptr -> value}.
Local Notation state := (locals * heap)%type.

Implicit Type (e : expr) (c : com) (ls : locals) (h : heap)
              (s st: state) (π : {fperm name}) (v : value)
              (E : seq error)
              (P Q R : state -> Prop)
              (T : Type).

Definition mem_safe_triple_counted P c Q (E : seq error) k :=
  forall s, fsubset (vars_c c) (domm s.1) ->
          P s ->  
          match eval_com c s k with
              | Done rs' => forall A, {finsupp A Q} -> pbindr A Q rs'
              | Error e =>  e \notin E
              | NotYet   => True
          end.

Definition mem_safe_triple P c Q (E : seq error) :=
forall s k, fsubset (vars_c c) (domm s.1) ->
        P s ->  
        match eval_com c s k with
            | Done rs' => forall A, {finsupp A Q} -> pbindr A Q rs'
            | Error e =>  e \notin E
            | NotYet   => True
        end.
                  
Notation "{{ P }} c {{ Q }} E" := (mem_safe_triple P c Q E) (at level 50). 

Definition separating_conjunction P Q s :=
  exists ls h1 h2,
    [/\ s = (ls, unionm h1 h2),
        P (ls, h1),
        Q (ls, h2) &
        fdisjoint (domm h1) (domm h2)].

Local Infix "*" := separating_conjunction.


Definition separating_conjunction_names P Q s :=
  exists ls h1 h2,
    [/\ s = (ls, unionm h1 h2),
        P (ls, h1),
        Q (ls, h2) &
        fdisjoint (names (domm h1)) (names (domm h2))].

Local Infix "*N" := separating_conjunction_names (at level 20).


Definition empty_heap (s : state) : Prop :=  
  domm s.2 = fset0.

Definition empty_h_and_P (P : state -> Prop) (s : state) : Prop := 
  (empty_heap s)  /\ P s.

Definition singleton (p : ptr) (s : state) : Prop := 
  domm s.2 = fset1 p.

Definition p_points_to_v (p : ptr) (v : value) (s : state) : Prop := 
  (p, v) \in s.2.

Definition singleton_points_to (s : state) (p : ptr) (v : value) : Prop := 
  domm s.2 = fset1 p /\ s.2 p = Some v.

Definition st_true (s : state) : Prop := True. 

Definition ls_true (ls : locals) : Prop := True. 

Definition h_true (h : heap) : Prop := True. 

Definition conj (P : state -> Prop) (Q : state -> Prop) (s : state) : Prop :=
  P s /\ Q s.

Definition disj (P : state -> Prop) (Q : state -> Prop) (s : state) : Prop :=
  P s \/ Q s.

Definition pred_ls (Pls : locals -> Prop) (s : state) := 
  Pls s.1 /\ s.2 = emptym.
   

Definition ind_vars (xs : {fset string}) P :=
  forall s s', P s ->
               (forall x, x \notin xs -> s.1 x = s'.1 x) ->
               s.2 = s'.2 ->
               P s'.


End Definitions.