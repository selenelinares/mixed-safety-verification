Require Import Coq.Strings.String.

From Coq Require Import Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssrnum ssrint seq.
From mathcomp Require Import eqtype choice seq order. 
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun fperm.

From CoqUtils Require Import nominal.

From memsafe Require Import syntax semantics separation_logic_def lang_properties nominal_proj_extension nominal_extension 
separation_logic frame_conds_def frame_conditions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Notation "{{ P }} c {{ Q }} E" := (mem_safe_triple P c Q E) (at level 50). 
Local Infix "*" := separating_conjunction.
Local Infix "*N" := separating_conjunction_names (at level 20).

(* Definitions *)

Definition exp_triple P e (Qv : value -> Prop ) :=
  forall s, P s ->  
          forall v, eval_expr true e s.1 = v ->
          Qv v.

Definition fc_triple_strenghten_pre 
  c (wi wo : {fset ptr}) (P : state -> Prop) :=
  mem_safe_triple 
    (conj P (lift_sc_seq_ptr_in_heap wi))
    c
    (lift_sc_seq_ptr_in_heap wo) 
    mem_safety_errors.

Definition fc_triple_weaken_pre 
  c (wi wo : {fset ptr}) (P : state -> Prop) :=
  mem_safe_triple 
    (disj (lift_sc_seq_ptr_in_heap wi) P)
    c
    (lift_sc_seq_ptr_in_heap wo) 
    mem_safety_errors.

Definition fc_triple_strenghen_post 
  c (wi wo : {fset ptr}) (Q : state -> Prop) :=
  mem_safe_triple 
   (lift_sc_seq_ptr_in_heap wi) 
   c
   (conj (lift_sc_seq_ptr_in_heap wo) Q) 
   mem_safety_errors.

Definition fc_triple_weaken_post 
  c (wi wo : {fset ptr}) (Q : state -> Prop) :=
  mem_safe_triple 
   (lift_sc_seq_ptr_in_heap wi) 
   c
   (disj (lift_sc_seq_ptr_in_heap wo) Q) 
   mem_safety_errors.

Definition fc_triple_pre_post_conj 
  c (wi wo : {fset ptr}) (P Q:state ->Prop) :=
  mem_safe_triple 
    (conj (lift_sc_seq_ptr_in_heap wi) P) 
    c
    (conj (lift_sc_seq_ptr_in_heap wo) Q) 
    mem_safety_errors.
          

Lemma expr_triple_import P Pv Q e c :
  exp_triple P e Pv ->
  mem_safe_triple 
    (conj P (fun s => Pv (eval_expr true e s.1))) c Q mem_safety_errors->
  mem_safe_triple P c Q mem_safety_errors.
Proof.
move => expr_tripleP triple_strenghten s k varsc_in_ls Ps.
apply triple_strenghten.
exact varsc_in_ls.
split.
exact Ps.
specialize (expr_tripleP s Ps (eval_expr true e s.1)).
have H : (eval_expr true e s.1) = (eval_expr true e s.1).
  reflexivity.
exact (expr_tripleP H).
Qed. 

Lemma finsupp_empty_heap : 
  {finsupp fset0 empty_heap}.
Proof.
move => pi H x y H0.
unfold empty_heap.
finsupp.
Qed.

Lemma ind_vars_fset0 P :
  ind_vars fset0 P.
Proof.
unfold ind_vars.
move => s s' Ps H eq_s_s'.
replace s' with s.
exact Ps.
rewrite (surjective_pairing s) (surjective_pairing s').
apply injective_projections.
simpl.
apply/eq_fmap=> k.
apply H.
case cx : (k \notin fset0).
apply is_true_true.
discriminate cx.
simpl.
exact eq_s_s'.
Qed.


Lemma fc_triple_heap_depd s1 s2 : 
  forall w, s1.2 = s2.2 
  -> lift_sc_seq_ptr_in_heap w s1 
  -> lift_sc_seq_ptr_in_heap w s2.
Proof.
move => w h1_eq_h2 bigseps1.
apply fsubset_dom_impl_precond in bigseps1.
apply fsubset_dom_impl_precond.
rewrite <- h1_eq_h2.
exact bigseps1.
Qed.

Lemma fc_triple_domm_heap_depd s1 s2 : 
  forall w, domm s1.2 = domm s2.2 
  -> lift_sc_seq_ptr_in_heap w s1 
  -> lift_sc_seq_ptr_in_heap w s2.
Proof.
move => w domm_h1_eq_h2 bigseps1.
apply fsubset_dom_impl_precond in bigseps1.
apply fsubset_dom_impl_precond.
rewrite <- domm_h1_eq_h2.
exact bigseps1.
Qed.


Lemma sep_conj0l s P : (separating_conjunction empty_heap P) s <-> P s.
Proof.
unfold separating_conjunction.
unfold empty_heap.
split.
- move => H.
  destruct H as [ls [h1 [h2 [H1 H2 Plsh2 h1h2_disjoint]]]].
  simpl in H2.
  move /eqP in H2.
  move /emptymP in H2.
  rewrite H2 in H1.
  rewrite union0m in H1.
  rewrite H1.
  exact Plsh2.    
- move => Ps.
  exists s.1, emptym, s.2.
  split.
  + rewrite union0m.
    apply surjective_pairing. 
  + simpl.
    apply domm0.
  + rewrite <- surjective_pairing.
    exact Ps.
  + rewrite domm0.
    apply fdisjoint0s.
Qed. 

Lemma finsupp_sep_conj0l w : 
  {finsupp (names w) empty_heap * lift_sc_seq_ptr_in_heap w}.
Proof.
move => pi H x y H0.
  assert (finsupp_sc := (@Precond_finsupp w pi H x y H0)). 
  split.
  + repeat rewrite sep_conj0l.
    apply finsupp_sc.
  + repeat rewrite sep_conj0l.
    apply finsupp_sc.
Qed.

Section Derived_rules.

(*Triple discharge for each command*)

Lemma fc_triple_skip: 
  forall wi wo, wi = wo -> fc_triple Skip wi wo.
Proof.
unfold fc_triple.
move => wi wo eq_wi_wo.
rewrite eq_wi_wo.
apply skip_rule.
Qed.

Lemma fc_triple_assn: 
forall wi wo x e,
  wi = wo
  -> fc_triple (Assn x e) wi wo.
Proof.
move => wi wo x e eq_wiwo.
unfold fc_triple.
apply (@consequence_rule (Assn x e) (names wo) (fun s => (lift_sc_seq_ptr_in_heap wi) (setm s.1 x (eval_expr true e s.1), s.2)) (lift_sc_seq_ptr_in_heap wo)).
- apply Precond_finsupp.
- rewrite eq_wiwo.
  apply assn_rule.
- move => s H.
  apply (@fc_triple_heap_depd s (setm s.1 x (eval_expr true e s.1), s.2) wi).
  reflexivity.
  exact H.
- auto.
Qed. 

Lemma frame_conds_load : 
  forall x e wi wo, wi = wo 
    -> exp_triple (lift_sc_seq_ptr_in_heap wi) 
                  e
                  (fun v => forall p sz, v == VPtr p sz -> p \in wi)
    -> fc_triple (Load x e) wi wo.
Proof.
move => x e wi wo eq_wi_wo expr_triple. 
unfold fc_triple.
move => ss k varsc_subset precond.
unfold exp_triple in expr_triple.
case ck : k => [|n].
  - simpl; exact I.
  - simpl.
    case ev_e : (eval_expr true e ss.1) => [||p sz|].
      - by [].
      - by []. 
      - specialize (expr_triple ss precond (VPtr p sz) ev_e p sz).
        specialize (expr_triple (eqxx (VPtr p sz))).
        assert (domm_ss2_eq := precond).
        apply domm_sepconj_s in domm_ss2_eq.
        rewrite <- domm_ss2_eq in expr_triple.
        rewrite <- eq_wi_wo.
        rewrite <- domm_ss2_eq.
        move /dommP in expr_triple.
        destruct expr_triple.
        rewrite H.
        move => A H2.
        apply pbindrE0.
        rewrite domm_ss2_eq.
        apply (@fc_triple_domm_heap_depd ss).
        by simpl.
        exact precond.
      by [].
Qed.

Lemma frame_cond_store : 
  forall x e wi wo, wi = wo -> 
    exp_triple (lift_sc_seq_ptr_in_heap wi) 
                 x
               (fun v => forall p sz, v == VPtr p sz -> p \in wi) ->
    fc_triple (Store x e) wi wo.
Proof.
move => x e wi wo eq_wi_wo expr_triple. 
unfold fc_triple.
move => ss k varsc_subset precond.
unfold exp_triple in expr_triple.
case ck : k => [|n].
  - simpl; exact I.
  - simpl.
    case ev_e : (eval_expr true x ss.1) => [||p sz|].
      - by [].
      - by []. 
      - specialize (expr_triple ss precond (VPtr p sz) ev_e).
        specialize (expr_triple p sz (eqxx (VPtr p sz))).
        assert (domm_ss2_eq := precond).
        apply domm_sepconj_s in domm_ss2_eq.
        rewrite <- eq_wi_wo.
        rewrite <- domm_ss2_eq.
        rewrite <- domm_ss2_eq in expr_triple.
        move /dommP in expr_triple.
        destruct expr_triple.
        unfold updm.
        rewrite H.
        simpl.
        move => A H2.
        apply pbindrE0.
        rewrite domm_ss2_eq.
        apply (@fc_triple_domm_heap_depd ss).
        simpl.
        rewrite domm_setm_eq.
        reflexivity.
        apply /dommP.
        exists x0.
        exact H.
        exact precond.
      by [].
Qed.

Definition singletonm 
  {T : ordType} (S : Type) (k : T) (v : S) : {fmap T -> S} :=
  setm emptym k v.

Lemma ptr_match v Pv Qv: 
match v with
        | VPtr p n => Pv p n
        | _ => Qv
        end
<->
(exists p n, v = VPtr p n /\ Pv p n) \/
 ((forall p n, v <> VPtr p n) /\ Qv).
Proof.
case cv : v => [b|i| p sz|]. 
- split.
  + move => Q_v.
    right.
    split.
    intros.
    discriminate.
    exact Q_v.
  + move => disj_ptr.
    destruct disj_ptr as [H | H1].
    destruct H as [x [sz [H1 H2]]].
    discriminate H1.
    destruct H1 as [H Q_v].
    exact Q_v.
- split.
  + move => Q_v.
    right.
    split.
    intros.
    discriminate.
    exact Q_v.
  + move => disj_ptr.
    destruct disj_ptr as [H | H1].
    destruct H as [x [sz [H1 H2]]].
    discriminate H1.
    destruct H1 as [H Q_v].
    exact Q_v.
- split.
  + move => Pv_p.
    left.
    exists p, sz.
    split.
    reflexivity.
    exact Pv_p.
  + move => H.
    destruct H as [v_ptr | v_not_ptr].
    * destruct v_ptr as [p0 [n [H Pv_p0]]].
      injection H.
      move => sz_n p_p0.
      rewrite <- sz_n in Pv_p0.
      rewrite <- p_p0 in Pv_p0.
      exact Pv_p0. 
    * destruct v_not_ptr as [contr Q_v].
      specialize (contr p sz).
      exfalso.
      apply contr.
      reflexivity.
- split.
  + move => Q_v.
    right.
    split.
    intros.
    discriminate.
    exact Q_v.
  + move => disj_ptr.
    destruct disj_ptr as [H | H1].
    destruct H as [x [sz [H1 H2]]].
    discriminate H1.
    destruct H1 as [H Q_v].
    exact Q_v.
Qed.

Lemma frame_conds_if_then_else:
  forall wi wo_t wo_f e b ct cf, 
    exp_triple (lift_sc_seq_ptr_in_heap wi) 
               e
               (fun v => v == VBool b) ->
    fc_triple ct wi wo_t ->
    fc_triple cf wi wo_f ->     
    fc_triple_weaken_post (If e ct cf) wi wo_t (lift_sc_seq_ptr_in_heap wo_f).
Proof. 
move => wi wo_t wo_f e b ct cf exp_triple fc_t fc_f.
unfold fc_triple in fc_t, fc_f.
apply (@if_then_else_rule_g (names wo_t) (names wo_f)).
- apply Precond_finsupp.
- apply Precond_finsupp.
- move => s k varscr_in_ls precond.
  destruct precond as [ev_e precond].
  case ev_c : (eval_com ct s k) => [rs||].
    + move => A finsupp_st_true.
      specialize (fc_t s k varscr_in_ls precond).
      rewrite ev_c in fc_t.
      specialize (fc_t A finsupp_st_true).
      exact fc_t.
    + specialize (fc_t s k varscr_in_ls precond).
      rewrite ev_c in fc_t.
      exact fc_t.
    + exact I. 
- move => s k varscr_in_ls precond.
  destruct precond as [ev_e precond].
  case ev_c : (eval_com cf s k) => [rs||].
    + move => A finsupp_st_false.
      specialize (fc_f s k varscr_in_ls precond).
      rewrite ev_c in fc_f.
      specialize (fc_f A finsupp_st_false).
      exact fc_f.
    + specialize (fc_f s k varscr_in_ls precond).
      rewrite ev_c in fc_f.
      exact fc_f.
    + exact I. 
Qed.

Lemma frame_conds_seq:
  forall wi w1 wo c1 c2,
  fc_triple c1 wi w1 ->
  fc_triple c2 w1 wo ->      
  fc_triple (Seq c1 c2) wi  wo.
Proof.
move => wi w1 wo c1 c2 fc_c1 fc_c2.
unfold fc_triple.
apply (@sequencing_rule _ (lift_sc_seq_ptr_in_heap w1) _ _ _ _ (names w1) (names wo)).
- apply Precond_finsupp. 
- apply Precond_finsupp.
- unfold fc_triple in fc_c1.
  exact fc_c1.
- unfold fc_triple in fc_c2.
  exact fc_c2.
Qed.

End Derived_rules.

(* Additional derived rules for allocation, local-store assertions, and free. *)
Section Derived_rules_extensions.

(* Allocation introduces a fresh name, so its output footprint cannot be
   fixed in advance as in fc_triple. Keep the fresh name
   existentially bound, together with the pointer returned in x. The block
   footprint is {(i, 0), ..., (i, sz - 1)} (empty when sz = 0). *)
Definition allocation_post x sz (wi : {fset ptr}) (s : state) : Prop :=
  exists i,
    i \notin names wi /\
    s.1 x = Some (VPtr (i, (0 : int)) (Posz sz)) /\
    lift_sc_seq_ptr_in_heap
      (wi :|: domm (mkblock i (nseq sz (VNum 0)))) s /\
    forall j, j < sz -> s.2 (i, Posz j) = Some (VNum 0).

(* Needed when this existential postcondition is the intermediate assertion
   of the sequencing rule. *)
Lemma allocation_post_finsupp x sz wi :
  {finsupp (names wi) allocation_post x sz wi}.
Proof.
have transport pi : finsupp_perm (names wi) pi ->
    forall s t, nomR pi s t ->
    allocation_post x sz wi s -> allocation_post x sz wi t.
  move => fixed s t renamed [i [fresh [stored [footprint initialized]]]].
  exists (rename pi i).
  split.
  - have H : nomR pi (is_true (i \notin names wi))
        (is_true (rename pi i \notin names wi)) by finsupp.
    exact (proj1 H fresh).
  split.
  - have H : nomR pi
        (s.1 x = Some (VPtr (i, (0 : int)) (Posz sz)))
        (t.1 x = Some (VPtr (rename pi i, (0 : int)) (Posz sz)))
      by finsupp.
    exact (proj1 H stored).
  split.
  - apply fsubset_dom_impl_precond.
    have H : nomR pi
        (domm s.2 = wi :|: domm (mkblock i (nseq sz (VNum 0))))
        (domm t.2 = wi :|: domm (mkblock (rename pi i) (nseq sz (VNum 0))))
      by finsupp.
    apply (proj1 H).
    exact (domm_sepconj_s footprint).
  - move => j j_lt_sz.
    have H : nomR pi
        (s.2 (i, Posz j) = Some (VNum 0))
        (t.2 (rename pi i, Posz j) = Some (VNum 0)) by finsupp.
    exact (proj1 H (initialized j j_lt_sz)).
move => pi fixed s t renamed; split.
- exact (transport pi fixed s t renamed).
- apply (transport (pi^-1)%fperm (finsupp_perm_inv fixed) t s).
  change (rename (pi^-1)%fperm t = s).
  by rewrite -renamed renameK.
Qed.

Lemma frame_conds_alloc x e sz wi :
  exp_triple (lift_sc_seq_ptr_in_heap wi) e
    (fun v => v = VNum (Posz sz)) ->
  mem_safe_triple
    (lift_sc_seq_ptr_in_heap wi)
    (Alloc x e)
    (allocation_post x sz wi)
    mem_safety_errors.
Proof.
move => expr_triple s [|k] vars_in_store precond /=;
  first exact I.
have eval_size := expr_triple s precond _ erefl.
rewrite eval_size.
move => A supported_post.
apply pbindr_new.
- exact supported_post.
- finsupp.
- move => i fresh_A fresh_s.
  apply pbindrE0.
  exists i.
  have dom_s : domm s.2 = wi := domm_sepconj_s precond.
  have names_wi_sub : fsubset (names wi) (names s).
    rewrite -dom_s namespE namesmE.
    exact (fsubset_trans (fsubsetUl _ _) (fsubsetUr _ _)).
  split.
  + apply/negP => i_in_wi.
    have i_in_s := (fsubsetP names_wi_sub) _ i_in_wi.
    by rewrite i_in_s in fresh_s.
  split.
  + by rewrite /= setmE eqxx.
  split.
  + apply fsubset_dom_impl_precond.
    by rewrite /= domm_union dom_s fsetUC.
  + move => j j_lt_sz.
    by rewrite /= unionmE mkblockE /= eqxx size_nseq j_lt_sz
      /= nth_nseq j_lt_sz.
Qed.

(* Local-store facts, such as alias relationships, must survive between
   commands. These variants retain them alongside the exact footprint. *)
Definition footprint_locals (w : {fset ptr}) (L : locals -> Prop) s :=
  L s.1 /\ lift_sc_seq_ptr_in_heap w s.

Lemma frame_conds_assn_local wi (L L' : locals -> Prop) x e :
  (forall ls, L ls -> L' (setm ls x (eval_expr true e ls))) ->
  mem_safe_triple (footprint_locals wi L) (Assn x e)
    (footprint_locals wi L') mem_safety_errors.
Proof.
move => update s [|k] vars_in_store [local_facts footprint] /=;
  first exact I.
move => A supported_post; apply pbindrE0; split.
- exact (update _ local_facts).
- apply fsubset_dom_impl_precond.
  exact (domm_sepconj_s footprint).
Qed.

Lemma frame_conds_store_local wi L e e' :
  exp_triple (footprint_locals wi L) e
    (fun v => forall p sz, v = VPtr p sz -> p \in wi) ->
  mem_safe_triple (footprint_locals wi L) (Store e e')
    (footprint_locals wi L) mem_safety_errors.
Proof.
move => address s [|k] vars_in_store precond /=; first exact I.
case ev_e : (eval_expr true e s.1) => [b|n|p sz|] //.
have p_in_wi := address s precond _ ev_e p sz erefl.
case: precond => local_facts footprint.
have dom_s : domm s.2 = wi := domm_sepconj_s footprint.
have p_in_heap : p \in domm s.2 by rewrite dom_s.
have [v lookup] := (dommP p_in_heap).
rewrite /updm lookup /=.
move => A supported_post; apply pbindrE0; split => //.
apply fsubset_dom_impl_precond.
by rewrite /= domm_setm_eq.
Qed.

Lemma frame_conds_load_local wi (L L' : locals -> Prop) x e :
  exp_triple (footprint_locals wi L) e
    (fun v => forall p sz, v = VPtr p sz -> p \in wi) ->
  (forall ls v, L ls -> L' (setm ls x v)) ->
  mem_safe_triple (footprint_locals wi L) (Load x e)
    (footprint_locals wi L') mem_safety_errors.
Proof.
move => address update s [|k] vars_in_store precond /=;
  first exact I.
case ev_e : (eval_expr true e s.1) => [b|n|p sz|] //.
have p_in_wi := address s precond _ ev_e p sz erefl.
case: precond => local_facts footprint.
have dom_s : domm s.2 = wi := domm_sepconj_s footprint.
have p_in_heap : p \in domm s.2 by rewrite dom_s.
have [v lookup] := (dommP p_in_heap).
rewrite lookup.
move => A supported_post; apply pbindrE0; split.
- exact (update _ _ local_facts).
- apply fsubset_dom_impl_precond.
  exact dom_s.
Qed.

Corollary frame_cond_free_no_ptr: 
  forall e wi wo, 
  exp_triple
    (lift_sc_seq_ptr_in_heap wi)
    e
    (fun v => forall p sz, v <> VPtr p sz)
  -> fc_triple (Free e) wi wo.
Proof.
move => e wi wo expr_triple s [|k] vars_in_store precond /=;
  first exact I.
case ev_e : (eval_expr true e s.1) => [b|n|p sz|] //.
exfalso.
exact (expr_triple s precond (VPtr p sz) ev_e p sz erefl).
Qed.

Corollary frame_cond_free_wi_wo: 
  forall e wi wo, 
  exp_triple
    (fun s => exists p, singleton p s) 
    e
    (fun v =>
      exists p sz, 
        v = VPtr p sz /\ p \in wi /\ wo = wi :\: fset1 p 
          /\ fdisjoint (names (fset1 p)) (names (wi :\ p)))
  -> fc_triple (Free e) wi wo.
Proof.
move => e wi wo expr_triple s [|k] vars_in_store precond /=;
  first exact I.
case ev_e : (eval_expr true e s.1) => [b|n|p sz|] //.
(* Expression evaluation is unchanged when we replace the heap. *)
have singleton_s : exists q, singleton q
    (s.1, setm emptym p VNil).
  exists p.
  by rewrite /singleton /= domm_set domm0 fsetU0.
have [q [sz' [ptr_eq [p_in_wi [wo_eq names_disj]]]]] :=
  expr_triple _ singleton_s _ ev_e.
injection ptr_eq => sz_eq p_eq.
subst q.
have dom_s : domm s.2 = wi := domm_sepconj_s precond.
case offset_zero : (p.2 == 0) => //.
have block_live : p.1 \in domm (currym s.2).
  rewrite domm_curry dom_s.
  exact (mem_imfset fst p_in_wi).
rewrite block_live.
move => A supported_post.
apply pbindrE0.
apply fsubset_dom_impl_precond.
rewrite /= domm_filter_eq dom_s wo_eq.
apply/eq_fset => q.
rewrite in_fset_filter in_fsetD in_fset1.
case q_in_wi : (q \in wi); last by rewrite !andbF.
rewrite !andbT.
apply bool_ext.
- move => different_blocks.
  apply/negP => /eqP same_ptr.
  by subst q; rewrite eqxx in different_blocks.
- move => different_ptrs.
  apply/negP => /eqP same_block.
  have q_in_rest : q \in wi :\ p.
    by rewrite in_fsetD in_fset1 different_ptrs q_in_wi.
  have p_name : p.1 \in names (fset1 p).
    apply ptr_namesin_in.
    by rewrite in_fset1.
  have not_in_rest := (fdisjointP names_disj) _ p_name.
  have in_rest := ptr_namesin_in q_in_rest.
  rewrite same_block in in_rest.
  by rewrite in_rest in not_in_rest.
Qed.

End Derived_rules_extensions.