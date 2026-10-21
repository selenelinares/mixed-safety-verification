Require Import Coq.Strings.String.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssrint seq.
From extructures Require Import ord fset fmap fperm.
From CoqUtils Require Import nominal.

From memsafe Require Import syntax semantics separation_logic_def
  frame_conds_def nominal_extension nominal_proj_extension lang_properties
  separation_logic frame_conditions derived_sl_rules.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope string_scope.
Local Open Scope fset_scope.

(* A one-cell scratch-buffer stub:

     buf := alloc(1);
     alias := buf;
     *alias := 65;
     result := *buf;
     free(alias);
     alias := nil;
     buf := nil;

   Both buf and alias refer to the same live cell when it is updated.
   Reading through buf after writing through alias makes this sharing
   observable: result receives 65. This is the internal mutable aliasing
   that an exclusive-ownership uniqueness discipline would disallow.
   There is no uniqueness typing judgement in this development, so this
   observation is explanatory rather than a formal non-typability claim.

   The whole program is nevertheless memory-safe: it accesses the allocated
   cell, frees it exactly once, and clears both aliases afterwards. Its
   boundary footprints are empty because the allocation is temporary.
   FC Triple establishes boundary frame conditions; it cannot establish
   that those same conditions are violated.
*)
Definition aliased_buffer : com :=
  Seq (Alloc "buf" (Num (Posz 1)))
    (Seq (Assn "alias" (Var "buf"))
      (Seq (Store (Var "alias") (Num (Posz 65)))
        (Seq (Load "result" (Var "buf"))
          (Seq (Free (Var "alias"))
            (Seq (Assn "alias" ENil)
                 (Assn "buf" ENil)))))).

(* FC Triple is the repository's fc_triple. Its precondition
   here describes an empty heap; its postcondition requires an empty heap
   on successful completion, and its validity excludes memory errors.
   As in every use of mem_safe_triple, the initial local store must contain
   the program variables (buf, alias, result); their initial values do not
   matter because each is assigned before it is read.

   Internal assertions track the fresh allocation and the equality of
   aliases; the fixed empty footprint specifies the whole stub.
*)

Local Notation locals := {fmap string -> value}.
Local Notation heap := {fmap ptr -> value}.
Local Notation state := (locals * heap)%type.

(* Before the alias assignment only buf is known; afterwards both names
   refer to the same owned cell. Heap contents are irrelevant to FC Triple. *)
Definition buffer_locals (p : ptr) (aliased : bool) (ls : locals) : Prop :=
  ls "buf" = Some (VPtr p (Posz 1)) /\
  (aliased = true -> ls "alias" = Some (VPtr p (Posz 1))).

Definition buffer_assert p aliased : state -> Prop :=
  footprint_locals (fset1 p) (buffer_locals p aliased).

Lemma buffer_assert_finsupp p aliased :
  {finsupp (names p) buffer_assert p aliased}.
Proof.
have supported_foot :
    {finsupp (names p) lift_sc_seq_ptr_in_heap (fset1 p)}.
  rewrite -(names_fset1_eq p).
  apply Precond_finsupp.
move => pi fixed s t renamed.
have Hfoot := supported_foot pi fixed s t renamed.
have Hbuf : nomR pi
    (s.1 "buf" = Some (VPtr p (Posz 1)))
    (t.1 "buf" = Some (VPtr p (Posz 1))) by finsupp.
have Halias : nomR pi
    (s.1 "alias" = Some (VPtr p (Posz 1)))
    (t.1 "alias" = Some (VPtr p (Posz 1))) by finsupp.
change (buffer_assert p aliased s <-> buffer_assert p aliased t).
unfold buffer_assert, footprint_locals, buffer_locals.
change (lift_sc_seq_ptr_in_heap (fset1 p) s <->
        lift_sc_seq_ptr_in_heap (fset1 p) t) in Hfoot.
change (s.1 "buf" = Some (VPtr p (Posz 1)) <->
        t.1 "buf" = Some (VPtr p (Posz 1))) in Hbuf.
change (s.1 "alias" = Some (VPtr p (Posz 1)) <->
        t.1 "alias" = Some (VPtr p (Posz 1))) in Halias.
tauto.
Qed.

Lemma buffer_alias_rule p :
  mem_safe_triple (buffer_assert p false) (Assn "alias" (Var "buf"))
    (buffer_assert p true) mem_safety_errors.
Proof.
apply frame_conds_assn_local.
move => ls [buf _]; split.
- by rewrite setmE.
- move => _; by rewrite setmE eqxx /= buf.
Qed.

Lemma buffer_store_rule p :
  mem_safe_triple (buffer_assert p true)
    (Store (Var "alias") (Num (Posz 65)))
    (buffer_assert p true) mem_safety_errors.
Proof.
apply frame_conds_store_local.
move => s [[buf alias] footprint] v ev q sz ptr_eq.
have alias_ptr := alias erefl.
rewrite /= alias_ptr in ev.
rewrite -ev in ptr_eq.
injection ptr_eq => _ <-.
by rewrite in_fset1.
Qed.

Lemma buffer_load_rule p :
  mem_safe_triple (buffer_assert p true) (Load "result" (Var "buf"))
    (buffer_assert p true) mem_safety_errors.
Proof.
apply frame_conds_load_local.
- move => s [[buf alias] footprint] v ev q sz ptr_eq.
  rewrite /= buf in ev.
  rewrite -ev in ptr_eq.
  injection ptr_eq => _ <-.
  by rewrite in_fset1.
- move => ls v [buf alias]; split.
  + by rewrite setmE.
  + move => _; by rewrite setmE; apply alias.
Qed.

Lemma buffer_free_rule p :
  mem_safe_triple (buffer_assert p true) (Free (Var "alias"))
    (lift_sc_seq_ptr_in_heap fset0) mem_safety_errors.
Proof.
eapply consequence_rule.
- exact finsupp_empty_heap.
- apply free_rule.
- move => s [[buf alias] footprint] q sz ev.
  have alias_ptr := alias erefl.
  rewrite /= alias_ptr in ev.
  injection ev => _ <-.
  exact (domm_sepconj_s footprint).
- move => s empty; apply fsubset_dom_impl_precond.
  exact empty.
Qed.

Lemma buffer_tail_rule p :
  mem_safe_triple (buffer_assert p false)
    (Seq (Assn "alias" (Var "buf"))
      (Seq (Store (Var "alias") (Num (Posz 65)))
        (Seq (Load "result" (Var "buf"))
          (Seq (Free (Var "alias"))
            (Seq (Assn "alias" ENil) (Assn "buf" ENil))))))
    (lift_sc_seq_ptr_in_heap fset0) mem_safety_errors.
Proof.
have supported_buffer := @buffer_assert_finsupp p true.
have supported_empty := @Precond_finsupp (fset0 : {fset ptr}).
eapply sequencing_rule.
- exact supported_buffer.
- exact supported_empty.
- exact (@buffer_alias_rule p).
eapply sequencing_rule.
- exact supported_buffer.
- exact supported_empty.
- exact (@buffer_store_rule p).
eapply sequencing_rule.
- exact supported_buffer.
- exact supported_empty.
- exact (@buffer_load_rule p).
eapply sequencing_rule.
- exact supported_empty.
- exact supported_empty.
- exact (@buffer_free_rule p).
apply (frame_conds_seq (w1 := fset0));
  by apply fc_triple_assn.
Qed.

Lemma aliased_buffer_fc_triple :
  fc_triple aliased_buffer fset0 fset0.
Proof.
unfold fc_triple, aliased_buffer.
eapply sequencing_rule.
- exact (@allocation_post_finsupp "buf" 1 fset0).
- exact (@Precond_finsupp fset0).
- apply frame_conds_alloc.
  by move => s footprint v <-.
- move => s k vars_in_store [i [fresh [buf [footprint initialized]]]].
  apply (@buffer_tail_rule (i, (0 : int)) s k vars_in_store).
  split.
  + split => //; discriminate.
  + rewrite fset0U domm_mkblock /= in footprint.
    by rewrite fset1E.
Qed.
