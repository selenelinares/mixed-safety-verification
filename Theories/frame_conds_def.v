Require Import Coq.Strings.String.

From Coq Require Import Program.Equality. 

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssrnum ssrint seq.
From mathcomp Require Import eqtype choice seq order. 
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun fperm.

From CoqUtils Require Import nominal.

From memsafe Require Import syntax semantics separation_logic_def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Frame_conditions_definitions.


Local Open Scope fset_scope.
Local Open Scope state_scope.

Local Notation locals := {fmap string -> value}.
Local Notation heap := {fmap ptr -> value}.
Local Notation state := (locals * heap)%type.

Local Infix "*" := separating_conjunction.

Implicit Type (e : expr) (c : com) (ls : locals) (h : heap)
              (s st: state) (π : {fperm name}) (v : value)
              (E : seq error)
              (P Q R : state -> Prop)
              (T : Type).

Definition leak_freedom (wi wo dommh: {fset ptr}) :=
  fsubset (wi :&: dommh) wo.

Definition fresh_allocation (wi wo dommh : {fset ptr}):=
  fsubset (wo :&: dommh) wi.

Definition inertia (wi wo : {fset ptr}) (h h' : heap) :=
  forall l, l \notin wi -> l \notin wo -> h l = h' l.

Definition lift_pred_seq_ptr_in_heap :=
  fun (ws : {fset ptr}) => map singleton ws.

Definition lift_bop_seq 
  (bop: (state -> Prop) -> (state -> Prop) -> state -> Prop) 
  (fs: {fset ptr} -> seq (state -> Prop)) :=
  fun ws => fun s => foldr bop empty_heap (fs ws) s.

Definition lift_sc_seq_ptr_in_heap :=
  fun (ws: {fset ptr}) => 
    lift_bop_seq separating_conjunction lift_pred_seq_ptr_in_heap ws.

Definition fc_triple c (wi wo : {fset ptr}) :=
 mem_safe_triple 
 (lift_sc_seq_ptr_in_heap wi)
 c
 (lift_sc_seq_ptr_in_heap wo) 
 mem_safety_errors.
 
Definition name_inclusive_submap
{T : nominalType} {S} (m : {fmap T -> S}) A :=
filterm (fun k _ => names k :&: A != fset0) m.

Definition name_avoiding_submap
  {T : nominalType} {S} (m : {fmap T -> S}) A :=
  filterm (fun k _ => fdisjoint (names k) A) m.

End Frame_conditions_definitions.