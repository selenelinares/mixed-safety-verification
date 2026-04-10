(*In this file, the definition of the separating conjunction operator was taken from Arthur's formalisation. We adapted Arthur's definition of triple to our set of errors, which resulted in mem_safe_triple.*)
Require Import Coq.Strings.String.

From Coq Require Import Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssrnum ssrint seq.
From mathcomp Require Import eqtype choice seq order. 
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun fperm.

From CoqUtils Require Import nominal.

From memsafe Require Import syntax semantics separation_logic_def lang_properties nominal_proj_extension nominal_extension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Separation.


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

Lemma sepconj_names_impl_sepconj (P Q : state -> Prop) (s : state) :
  (P *N Q) s -> (separating_conjunction P Q) s.
Proof.
move => scn.
unfold separating_conjunction_names in scn.
destruct scn as [ls [h1 [h2 [s_unionm Ph1 Qh2 h1h2_disjoint]]]].
unfold separating_conjunction.
exists ls, h1, h2.
split.
- exact s_unionm.
- exact Ph1.
- exact Qh2.
- apply fdisjoint_names_domm_set.
  exact h1h2_disjoint.
Qed.

Lemma names_disjnt_sepconj_impl_sepconj_names
  (P Q : state -> Prop) (s : state) :
  (forall s1 s2,
    P s1 -> Q s2 ->
    fdisjoint (domm s1.2) (domm s2.2) ->
    fdisjoint (names (domm s1.2)) (names (domm s2.2))) ->
  (separating_conjunction P Q) s ->
  (P *N Q) s.
Proof.
move => H scPQ.
unfold separating_conjunction in scPQ.
destruct scPQ as [ls [h1 [h2 [s_unionm Ph1 Qh2 h1h2_disjoint]]]].
unfold separating_conjunction_names.
exists ls, h1, h2.
split.
- exact s_unionm.
- exact Ph1.
- exact Qh2.
- apply (@H (ls,h1) (ls,h2) Ph1 Qh2 h1h2_disjoint).
Qed.

Section FMap.

Lemma domm_filter_eq {T : ordType} {S : Type} (p : pred T) (m : {fmap T -> S}) :
  domm (filterm (fun k _ => p k) m) = fset_filter p (domm m).
Proof.
apply/eq_fset => k; rewrite !(mem_domm, in_fset_filter) filtermE andbC.
by case: (m k) => //= v; case: ifP.
Qed.


End FMap.


Section Nominal_extension_lemmas.

 
Lemma pbindr_conj A1 A2 P1 P2 rx :
  {finsupp A1 P1} ->
  {finsupp A2 P2} ->
  pbindr A1 P1 rx ->
  pbindr A2 P2 rx ->
  pbindr (A1 :|: A2) (conj P1 P2) rx.
Proof.
move => H H0 H1 H2.
unfold pbindr.
move => A' x H3 H4.
rewrite fdisjointUl in H4.
case /andP : H4 => H4' H4''.
unfold pbindr in H1.
specialize (H1 A' x H3 H4').
unfold pbindr in H2.
specialize (H2 A' x H3 H4'').
unfold conj.
split.
exact H1.
exact H2. 
Qed.

End Nominal_extension_lemmas.

Section semantics_extension_lemmas.

Lemma ind_vars_eval c k ls ls' h1 h1' h2 (A' : {fset name}) R : 
 ind_vars (mod_vars_c c) R -> 
 R (ls, h2) ->
 eval_com c (ls, h1) k = Done (hide A' (Restr (ls', h1'))) ->
 R (ls', h2).
Proof. 
intros.
unfold ind_vars in H.
eapply H.
exact H0. 
intros.
simpl. 
have H3 : mapr fset0 (fun s0 : state => s0.1 x) 
            (hide A' (Restr (ls', h1'))) = Restr ((ls,h1).1 x).
  eapply mod_vars_cP.
   exact H1.
   exact H2.
rewrite maprE in H3. 
apply Logic.eq_sym in H3.
apply restr_eq0 in H3.
destruct H3.
simpl in H3.
exact H3.
apply fdisjoint0s.
simpl;reflexivity.
Qed.

Lemma eval_domm_ls s c k :
  fsubset (vars_c c) (domm s.1) ->
  pbind_res
    (names s)
    (fun s' => domm s'.1 = domm s.1)
    (eval_com c s k).
Proof.
have sub: forall (T : ordType) (x : T) (X : {fset T}),
            x \in X -> x |: X = X.
  by move=> T x X Px; apply/fsetUidPr; rewrite fsub1set.
elim: k s c => [|k IH] /= s; first by [].
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=;
rewrite ?fsub1set ?fsubUset.
- move=> Px _ [<-].
  move /andP in Px.
  destruct Px as [x_in_ls varse_in_ls].
  rewrite restrE0 domm_set sub.
  reflexivity.
  rewrite fsub1set in x_in_ls.
  exact x_in_ls.
- move=> Px.
  move /andP in Px.
  destruct Px as [x_in_ls varse_in_ls].
  case: eval_expr => // p sz rs.
  case: getm=> [v|] //=.
  move => rs_eq.
  injection rs_eq => rs_eq'.
  rewrite <- rs_eq'.
  rewrite restrE0 domm_set sub.
  reflexivity.
  rewrite fsub1set in x_in_ls.
  exact x_in_ls.
- move=> Px.
  case: eval_expr=> // p sz rs.
  rewrite /updm.
  case: getm=> [v|] //=.
  move => done_eq.
  injection done_eq => rs_eq.
  rewrite <- rs_eq.
  rewrite restrE0.
  simpl.
  reflexivity.
- case: eval_expr => [|[n|]| |] // Px _ [<-].
  rewrite /new pbindrE ?fdisjoints1 ?freshP //= domm_set sub.
  reflexivity.
  move /andP in Px.
  destruct Px as [x_in_ls varse_in_ls].
  rewrite fsub1set in x_in_ls.
  exact x_in_ls.
- case: eval_expr => // p sz _.
  case: ifP=> // _; case: ifP=> //= in_h1 _ [<-].
  by rewrite restrE0.
- by move=> _ _ [<-]; rewrite restrE0.
- case/andP=> /IH vars_c1 vars_c2.
  move: vars_c1; eapply pbind_res_bind; try by typeclasses eauto.
  move=> /= s' ess'; move: vars_c2; rewrite -{1}ess' => /IH.
  eapply pbind_res_impl; try by typeclasses eauto.
  by move=> /= ? ->.
- case: eval_expr=> // - b.
  case/andP=> Px vars_c2; case: b; eapply IH; eauto.
  move /andP in Px.
  destruct Px as [x_in_ls varsc_in_ls].
  exact varsc_in_ls.
- case: eval_expr=> // - [] P; apply: IH; try by rewrite fsub0set.
  simpl.
  move /andP in P.
  destruct P as [x_in_ls varse_in_ls]. 
  rewrite fsubUset.
  rewrite fsubUset.
  apply /andP.
  split.
  exact varse_in_ls.
  apply /andP.
  split.
  exact x_in_ls.
  exact varse_in_ls.
Qed.

Lemma subset_modvars_vars c : fsubset (mod_vars_c c) (vars_c c).
Proof.
elim c => [x e|x e |e e1 |x e |e | | c1 H c2 H0|e ct H cf H0 |e cw H].
  - simpl.
    apply fsubsetUl.
  - simpl. 
    apply fsubsetUl.
  - simpl.
    apply fsub0set.
  - simpl.
    apply fsubsetUl.
  - simpl.
    apply fsub0set.
  - simpl.
    apply fsub0set.
  - simpl.
    apply (fsetUSS H H0).
  - simpl.
    apply (@fsubset_trans _ (vars_c ct :|: vars_c cf) _).
    apply (fsetUSS H H0).
    rewrite <- fsetUA.
    apply fsubsetUr.
  - simpl.
    apply (@fsubset_trans _ (vars_c cw) _).
    exact H. 
    apply fsubsetUr.
Qed.
 

End semantics_extension_lemmas.


Section fset_extension_lemmas.

Lemma fsubsetD {A : ordType} (s1 s2 : {fset A}): fsubset (s1 :\: s2) s1.
Proof.
  apply /fsetIidPr.
  rewrite fsetIDA.
  rewrite fsetIid.
  reflexivity.
Qed.

End fset_extension_lemmas.

Section InferenceRules.

Lemma skip_rule P :
  {{P}} Skip {{P}} mem_safety_errors.
Proof.
move => s k vars_c p_true.
case ck: k; simpl.
- exact I.
- intros. 
  apply pbindrE0.
  assumption.
Qed.


Lemma assn_rule x e P:
  {{fun s => P (setm s.1 x (eval_expr true e s.1), s.2)}}
  (Assn x e)
  {{P}}
  mem_safety_errors.
Proof.
move => s k vars_c P_subst.
case ck: k => [|n].
- simpl.
  exact I.
- simpl.
  intros.
  rewrite pbindrE0.
  exact P_subst.
Qed.



Lemma load_rule x e:
  forall v p,
  mem_safe_triple
    (fun s =>
      exists n,
        eval_expr true e s.1 = VPtr p n /\ 
        singleton_points_to s p v)
    (Load x e)
    (fun s' =>
      s'.1 x = Some v /\ singleton_points_to s' p v)
    mem_safety_errors.
Proof.
move => v p s k varsc precond.
destruct precond as [n [precond1 precond2]].
case ck: k.
- simpl.
  exact I. 
- simpl.
  rewrite precond1.
  destruct precond2 as [precond2 precond3].
  rewrite precond3.
  intros.
  rewrite pbindrE0.
  split.
    + rewrite setmE.
      rewrite eqxx.
      reflexivity.
    + split.
      exact precond2.
      exact precond3.
Qed.


Lemma store_rule e e':
  forall p v, 
  mem_safe_triple
  (fun s =>
    exists n,
      eval_expr true e s.1 = VPtr p n 
      /\ p \in domm s.2 /\ eval_expr true e' s.1 = v)
  (Store e e')
  (fun s' => s'.2 p = Some v)
  mem_safety_errors.
Proof.
move => p v s k vars_c H.
destruct H as [n [eval_expr_e [in_domm eval_exp_e']]].
case ck: k.
by simpl.
unfold eval_com.
rewrite eval_expr_e.
unfold updm.
rewrite mem_domm in in_domm.
rewrite in_domm.
intros.
rewrite pbindrE0.
simpl.
rewrite eval_exp_e'.
rewrite setmE.
rewrite eqxx.
reflexivity.
Qed.

Lemma alloc_rule x e:
  forall sz,
  mem_safe_triple 
    (fun s => 
      eval_expr true e s.1 = VNum (Posz sz)) 
    (Alloc x e)
    (fun s' =>
      exists p,
      s'.1 x = Some (VPtr (p, (0 : int)) sz) /\
      forall j, j < sz -> s'.2 (p, (Posz j)) = Some (VNum 0))
    mem_safety_errors.
Proof.
move => sz s k vars_c eval_expr.
case ck: k => [|k'].
by simpl; exact I.
unfold eval_com.
rewrite eval_expr.
intros.
apply pbindr_new.
  - exact H.
  - finsupp.
  - move => i i_notin_A i_notin_s. 
    apply pbindrE0.
    exists i.
    simpl.
    split.
      - rewrite setmE.
        rewrite eqxx.
        reflexivity.
      - move => j j_lt_sz.
        rewrite unionmE.
        rewrite mkblockE.
        simpl.
        rewrite eqxx.
        rewrite size_nseq.
        rewrite j_lt_sz.
        simpl.
        rewrite nth_nseq.
        rewrite j_lt_sz.
        reflexivity.
Qed.


Lemma free_rule:
  forall e, mem_safe_triple
    (fun s => forall p n, eval_expr true e s.1 = VPtr p n
      -> singleton p s)
    (Free e)
    empty_heap
    mem_safety_errors.
Proof.
move => e s k vars_c_in_ls precond.
case ck : k => [|k'].
by exact I.
simpl.
case case_e : (eval_expr true e s.1) => [||p sz|].
- exact.
- exact.
- case c_offset : (p.2 == 0).
  specialize (precond p sz case_e).
  unfold singleton in precond.
  rewrite domm_curry precond imfset1 in_fset1 (eqxx p.1).
  move => A finsuppAempty.
  apply pbindrE0.
  unfold empty_heap.
  simpl.
  rewrite domm_filter_eq precond.
  apply/eq_fset => x.
  rewrite in_fset_filter in_fset1 in_fset0.
  rewrite {2} (surjective_pairing p).
  rewrite {2} (surjective_pairing x).
  apply (@contraFF 
    ((x.1 != p.1) && ((x.1, x.2) == (p.1, p.2)))
    ((x.1 != p.1) && (x.1 == p.1))).
  + case /andP => H1 H2.
    move /eqP in H2.
    injection H2.
    move => H3 H4.
    apply /andP.
    split.
    exact H1.
    apply /eqP.
    exact H4.
  + apply andNb.
- exact.
- exact.
Qed.


Lemma free_rule_simp:
  forall e, mem_safe_triple
    (fun s => exists p n, eval_expr true e s.1 = VPtr p n
        /\ singleton p s)
    (Free e)
    empty_heap
    mem_safety_errors.
Proof.
move => e s k vars_c_in_ls precond.
case ck : k => [|k'].
by exact I.
destruct precond as [p [n [eval_e s_singleton]]].
simpl.
rewrite eval_e.
case c_offset : (p.2 == 0).
  unfold singleton in s_singleton.
  rewrite domm_curry s_singleton imfset1 in_fset1 (eqxx p.1).
  move => A finsuppAempty.
  apply pbindrE0.
  unfold empty_heap.
  simpl.
  rewrite domm_filter_eq s_singleton.
  apply/eq_fset => x.
  rewrite in_fset_filter in_fset1 in_fset0.
  rewrite {2} (surjective_pairing p).
  rewrite {2} (surjective_pairing x).
  apply (@contraFF 
    ((x.1 != p.1) && ((x.1, x.2) == (p.1, p.2)))
    ((x.1 != p.1) && (x.1 == p.1))).
  + case /andP => H1 H2.
    move /eqP in H2.
    injection H2.
    move => H3 H4.
    apply /andP.
    split.
    exact H1.
    apply /eqP.
    exact H4.
  + apply andNb.
- exact.
Qed.


Lemma mem_frame_rule_names P Q R c AQ:
  {finsupp AQ Q} -> 
  mem_safe_triple P c Q mem_safety_errors ->
  ind_vars (mod_vars_c c) R ->
  mem_safe_triple (P *N R) c (Q *N R) mem_safety_errors.
Proof.
  move=> finsuppQ t ind s k sub [ls [h1 [h2 [e ph1 ph2 dis]]]].
  rewrite {}e {s} in sub *. 
  unfold mem_safe_triple in t.
  move/(_ (ls, h1) k sub ph1): t. 
  rewrite -{2}[ls]unionm0.
  case ev: (eval_com c (ls, h1) k)=> [rs'| e|] //=; first last.
    - by rewrite (@frame_loop _ (ls, h1) (emptym, h2)).
    - move => e_not_seqE.
      rewrite (@frame_mem_safe_error c (ls, h1) (emptym, h2) k e). 
      exact e_not_seqE.
      exact sub.
      simpl.
      exact dis.
      exact ev.
      exact e_not_seqE. 
  - move=> Q_rs'.
    rewrite (@frame_ok _ (ls, h1) (emptym, h2) _ _ sub dis ev).
    move => A finsuppQR.
    case: rs' / (restrP (names (ls, h1) :|: names ((emptym, h2) : state) :|: A :|: AQ) rs')
            Q_rs' ev => /= A' [ls' h1'] dis'' sub' Q_rs' ev.
    move: dis''; rewrite 3!fdisjointUl=> /andP [/andP [/andP dis1 dis2] dis3].
    destruct dis1 as [dis_h1A' dis_h2A'].
    rewrite maprE // /stateu unionm0.
    simpl.
    rewrite pbindrE.
    2: exact dis2.
    unfold separating_conjunction_names.
    exists ls', h1', h2.
    split.
      + reflexivity.
      + specialize (Q_rs' AQ finsuppQ).
        apply pbindrE in Q_rs'; repeat assumption.
      + eapply ind_vars_eval.
        exact ind. 
        exact ph2.
        exact ev.
      + have dis_pbindr: pbind_res (names (names (domm h2))) 
                        (fun s' : state => fdisjoint (names (domm s'.2)) (names (domm h2))) 
                        (eval_com c (ls, h1) k).
        apply (@eval_com_blocks (names (domm h2)) (ls, h1) c k).
        simpl; exact dis. 
        rewrite ev in dis_pbindr.
        apply pbind_resE in dis_pbindr.
        rewrite names_names_eq in dis_pbindr.
        apply pbindrE in dis_pbindr.
        - simpl in dis_pbindr.
          exact dis_pbindr.
        - rewrite -{1} names_names_eq.
          apply (@finsupp_fsetD (names (domm h2))).
        - rewrite namespE in dis_h2A'.
          simpl in dis_h2A'.
          rewrite namesm_empty in dis_h2A'.
          rewrite fset0U in dis_h2A'. 
          eapply fdisjoint_trans.
            2: exact dis_h2A'.
            rewrite namesmE.
          apply fsubsetUl.
Qed.

Lemma mem_frame_rule P Q R c AQ:
  {finsupp AQ Q} -> 
  mem_safe_triple P c Q mem_safety_errors ->
  ind_vars (mod_vars_c c) R ->
  (forall s1 s2, P s1 -> R s2 ->
    fdisjoint (domm s1.2) (domm s2.2) ->
    fdisjoint (names (domm s1.2)) (names (domm s2.2))) ->
  (forall s1 s2, Q s1 -> R s2 ->
    fdisjoint (domm s1.2) (domm s2.2) ->
    fdisjoint (names (domm s1.2)) (names (domm s2.2))) ->
  mem_safe_triple (P * R) c (Q * R) mem_safety_errors.
Proof.
  move=> finsuppQ t ind disjPR disjQR s k sub [ls [h1 [h2 [e ph1 ph2 dis]]]].
  rewrite {}e {s} in sub *. 
  unfold mem_safe_triple in t.
  move/(_ (ls, h1) k sub ph1): t. 
  rewrite -{2}[ls]unionm0.
  assert (name_disjoint_PR := disjPR _ _ ph1 ph2 dis).
  simpl in name_disjoint_PR.
  case ev: (eval_com c (ls, h1) k)=> [rs'| e|] //=; first last.
    - by rewrite (@frame_loop _ (ls, h1) (emptym, h2)).
    - move => e_not_seqE.
      rewrite (@frame_mem_safe_error c (ls, h1) (emptym, h2) k e). 
      exact e_not_seqE.
      exact sub.
      simpl.
      exact name_disjoint_PR.
      exact ev.
      exact e_not_seqE. 
  - move=> Q_rs'.
    rewrite (@frame_ok _ (ls, h1) (emptym, h2) _ _ sub name_disjoint_PR ev).
    move => A finsuppQR.
    case: rs' / (restrP (names (ls, h1) :|: names ((emptym, h2) : state) :|: A :|: AQ) rs')
            Q_rs' ev => /= A' [ls' h1'] dis'' sub' Q_rs' ev.
    move: dis''; rewrite 3!fdisjointUl=> /andP [/andP [/andP dis1 dis2] dis3].
    destruct dis1 as [dis_h1A' dis_h2A'].
    rewrite maprE // /stateu unionm0.
    simpl.
    rewrite pbindrE.
    + 2: exact dis2.
    unfold separating_conjunction.
    exists ls', h1', h2.
    split.
    + reflexivity.
    + specialize (Q_rs' AQ finsuppQ).
      apply pbindrE in Q_rs'; repeat assumption.
    + eapply ind_vars_eval.
      exact ind. 
      exact ph2.
      exact ev.
    + have dis_pbindr: pbind_res (names (names (domm h2))) 
                      (fun s' : state => fdisjoint (names (domm s'.2)) (names (domm h2))) 
                      (eval_com c (ls, h1) k).
      * apply (@eval_com_blocks (names (domm h2)) (ls, h1) c k).
        simpl; exact name_disjoint_PR.
      rewrite ev in dis_pbindr.
      apply pbind_resE in dis_pbindr.
      rewrite names_names_eq in dis_pbindr.
      apply pbindrE in dis_pbindr.
      - simpl in dis_pbindr.
        apply (fdisjoint_names_domm dis_pbindr).
      - rewrite -{1} names_names_eq.
        apply (@finsupp_fsetD (names (domm h2))). 
      - rewrite namespE in dis_h2A'.
        simpl in dis_h2A'.
        rewrite namesm_empty in dis_h2A'.
        rewrite fset0U in dis_h2A'. 
        eapply fdisjoint_trans.
        + 2: exact dis_h2A'.
        + rewrite namesmE.
          apply fsubsetUl.
Qed.

Lemma mem_frame_rule_simpl P Q R c AQ:
  {finsupp AQ Q} -> 
  mem_safe_triple P c Q mem_safety_errors ->
  ind_vars (mod_vars_c c) R ->
  (forall s1 s2, P s1 -> R s2 ->
    fdisjoint (names (domm s1.2)) (names (domm s2.2))) ->
  (forall s1 s2, Q s1 -> R s2 ->
    fdisjoint (names (domm s1.2)) (names (domm s2.2))) ->
  mem_safe_triple (P * R) c (Q * R) mem_safety_errors.
Proof.
  move=> finsuppQ t ind disjPR disjQR s k sub [ls [h1 [h2 [e ph1 ph2 dis]]]].
  rewrite {}e {s} in sub *. 
  unfold mem_safe_triple in t.
  move/(_ (ls, h1) k sub ph1): t. 
  rewrite -{2}[ls]unionm0.
  assert (name_disjoint_PR := disjPR _ _ ph1 ph2).
  simpl in name_disjoint_PR.
  case ev: (eval_com c (ls, h1) k)=> [rs'| e|] //=; first last.
    - by rewrite (@frame_loop _ (ls, h1) (emptym, h2)).
    - move => e_not_seqE.
      rewrite (@frame_mem_safe_error c (ls, h1) (emptym, h2) k e). 
      exact e_not_seqE.
      exact sub.
      simpl.
      exact name_disjoint_PR.
      exact ev.
      exact e_not_seqE. 
  - move=> Q_rs'.
    rewrite (@frame_ok _ (ls, h1) (emptym, h2) _ _ sub name_disjoint_PR ev).
    move => A finsuppQR.
    case: rs' / (restrP (names (ls, h1) :|: names ((emptym, h2) : state) :|: A :|: AQ) rs')
            Q_rs' ev => /= A' [ls' h1'] dis'' sub' Q_rs' ev.
    move: dis''; rewrite 3!fdisjointUl=> /andP [/andP [/andP dis1 dis2] dis3].
    destruct dis1 as [dis_h1A' dis_h2A'].
    rewrite maprE // /stateu unionm0.
    simpl.
    rewrite pbindrE.
    + 2: exact dis2.
    unfold separating_conjunction.
    exists ls', h1', h2.
    split.
    + reflexivity.
    + specialize (Q_rs' AQ finsuppQ).
      apply pbindrE in Q_rs'; repeat assumption.
    + eapply ind_vars_eval.
      exact ind. 
      exact ph2.
      exact ev.
    + have dis_pbindr: pbind_res (names (names (domm h2))) 
                      (fun s' : state => fdisjoint (names (domm s'.2)) (names (domm h2))) 
                      (eval_com c (ls, h1) k).
      * apply (@eval_com_blocks (names (domm h2)) (ls, h1) c k).
        simpl; exact name_disjoint_PR.
      rewrite ev in dis_pbindr.
      apply pbind_resE in dis_pbindr.
      rewrite names_names_eq in dis_pbindr.
      apply pbindrE in dis_pbindr.
      - simpl in dis_pbindr.
        apply (fdisjoint_names_domm dis_pbindr).
      - rewrite -{1} names_names_eq.
        apply (@finsupp_fsetD (names (domm h2))). 
      - rewrite namespE in dis_h2A'.
        simpl in dis_h2A'.
        rewrite namesm_empty in dis_h2A'.
        rewrite fset0U in dis_h2A'. 
        eapply fdisjoint_trans.
        + 2: exact dis_h2A'.
        + rewrite namesmE.
          apply fsubsetUl.
Qed.


Lemma if_then_else_rule P Q e c1 c2 :
  mem_safe_triple 
  (fun s => eval_expr true e s.1 = VBool true /\ P s) c1 Q mem_safety_errors ->
  mem_safe_triple 
  (fun s => eval_expr true e s.1 = VBool false /\ P s) c2 Q mem_safety_errors ->
  mem_safe_triple P (If e c1 c2) Q mem_safety_errors.
Proof.
move => c1_triple c2_triple s k varsc_in_ls Ps.
case ck: k => [| k'].
by exact I.
simpl in varsc_in_ls.
rewrite !fsubUset in varsc_in_ls.
move /andP in varsc_in_ls.
destruct varsc_in_ls as [vars_in_ls vars_c2_in_ls].
move /andP in vars_in_ls.
destruct vars_in_ls as [vars_e_in_ls vars_c1_in_ls].
case expr_ev : (eval_expr true e s.1) => [b|||].
- simpl.
  rewrite expr_ev.
  case case_b: b => [|].
  + case ev_c1: (eval_com c1 s k') => [rs1| e1|].
    * specialize (c1_triple s k' vars_c1_in_ls).
      rewrite ev_c1 in c1_triple.
      apply c1_triple.
      split.
        rewrite case_b in expr_ev.
        exact expr_ev.
        exact Ps.
    * specialize (c1_triple s k' vars_c1_in_ls).
      rewrite ev_c1 in c1_triple.
      apply c1_triple.
      split.
        rewrite case_b in expr_ev.
        exact expr_ev.
        exact Ps.
    * exact I.
  + case ev_c2: (eval_com c2 s k') => [rs2| e2|].
    * specialize (c2_triple s k' vars_c2_in_ls).
      rewrite ev_c2 in c2_triple.
      apply c2_triple.
      split.
        rewrite case_b in expr_ev.
        exact expr_ev.
        exact Ps.
    * specialize (c2_triple s k' vars_c2_in_ls).
      rewrite ev_c2 in c2_triple.
      apply c2_triple.
      split.
        rewrite case_b in expr_ev.
        exact expr_ev.
        exact Ps.
    * exact I.
- simpl.
  rewrite expr_ev.
  by [].
- simpl.
  rewrite expr_ev.
  by [].
- simpl.
  rewrite expr_ev.
  by [].
Qed. 

Lemma if_then_else_rule_g AQ1 AQ2 P Q1 Q2 e c1 c2 :
  {finsupp AQ1 Q1} -> {finsupp AQ2 Q2} ->
  mem_safe_triple 
  (fun s => eval_expr true e s.1 = VBool true /\ P s) c1 Q1 mem_safety_errors ->
  mem_safe_triple 
  (fun s => eval_expr true e s.1 = VBool false /\ P s) c2 Q2 mem_safety_errors ->
  mem_safe_triple P (If e c1 c2) (disj Q1 Q2) mem_safety_errors.
Proof.
move => finsuppQ1 finsuppQ2 c1_triple c2_triple s k varsc_in_ls Ps.
case ck: k => [| k'].
by exact I.
simpl in varsc_in_ls.
rewrite !fsubUset in varsc_in_ls.
move /andP in varsc_in_ls.
destruct varsc_in_ls as [vars_in_ls vars_c2_in_ls].
move /andP in vars_in_ls.
destruct vars_in_ls as [vars_e_in_ls vars_c1_in_ls].
case expr_ev : (eval_expr true e s.1) => [b|||].
- simpl.
  rewrite expr_ev.
  case case_b: b => [|].
  + case ev_c1: (eval_com c1 s k') => [rs1| e1|].
    * specialize (c1_triple s k' vars_c1_in_ls).
      rewrite ev_c1 in c1_triple.
      move => A finsuppQ1orQ2.
      case : (restrP (names s :|: AQ1 :|: AQ2 :|: A) rs1) => [A' rs1' namesd namessub] in c1_triple *.
      rewrite fdisjointUl in namesd.
      move /andP in namesd.
      destruct namesd as [namesd fdisjntAA'].
      rewrite fdisjointUl in namesd.
      move /andP in namesd.
      destruct namesd as [namesd fdisjntAQ2A'].
      rewrite fdisjointUl in namesd.
      move /andP in namesd.
      destruct namesd as [fdisjointsA' fdisjntAQ1A'].
      apply pbindrE.
        ** exact finsuppQ1orQ2.
        ** exact fdisjntAA'.
        ** unfold disj.
           left.
           have H : eval_expr true e s.1 = VBool true /\ P s.
            split.
            rewrite case_b in expr_ev.
            exact expr_ev.
            exact Ps.
           specialize (c1_triple H AQ1 finsuppQ1).
           apply pbindrE in c1_triple.
            exact c1_triple. 
            apply finsuppQ1.
            exact fdisjntAQ1A'.
    * specialize (c1_triple s k' vars_c1_in_ls).
      rewrite ev_c1 in c1_triple.
      apply c1_triple.
      split.
        rewrite case_b in expr_ev.
        exact expr_ev.
        exact Ps.
    * exact I.
  + case ev_c2: (eval_com c2 s k') => [rs2| e2|].
  * specialize (c2_triple s k' vars_c2_in_ls).
    rewrite ev_c2 in c2_triple.
    move => A finsuppQ1orQ2.
    case : (restrP (names s :|: AQ1 :|: AQ2 :|: A) rs2) => [A' rs2' namesd namessub] in c2_triple *.
    rewrite fdisjointUl in namesd.
    move /andP in namesd.
    destruct namesd as [namesd fdisjntAA'].
    rewrite fdisjointUl in namesd.
    move /andP in namesd.
    destruct namesd as [namesd fdisjntAQ2A'].
    rewrite fdisjointUl in namesd.
    move /andP in namesd.
    destruct namesd as [fdisjointsA' fdisjntAQ1A'].
    apply pbindrE.
      ** exact finsuppQ1orQ2.
      ** exact fdisjntAA'.
      ** unfold disj.
         right.
         have H : eval_expr true e s.1 = VBool false /\ P s.
          split.
          rewrite case_b in expr_ev.
          exact expr_ev.
          exact Ps.
         specialize (c2_triple H AQ2 finsuppQ2).
         apply pbindrE in c2_triple.
          exact c2_triple. 
          apply finsuppQ2.
          exact fdisjntAQ2A'.
  * specialize (c2_triple s k' vars_c2_in_ls).
    rewrite ev_c2 in c2_triple.
    apply c2_triple.
    split.
      rewrite case_b in expr_ev.
      exact expr_ev.
      exact Ps.
  * exact I.
- simpl.
  rewrite expr_ev.
  by [].
- simpl.
  rewrite expr_ev.
  by [].
- simpl.
  rewrite expr_ev.
  by [].
Qed. 

   
Lemma sequencing_rule_strong P Q R c1 c2 e_set AQ AR k :
  {finsupp AQ Q} -> {finsupp AR R} ->
  mem_safe_triple_counted P c1 Q e_set (k.-1) ->
  mem_safe_triple_counted Q c2 R e_set (k.-1) ->
  mem_safe_triple_counted P (Seq c1 c2) R e_set k.
Proof.
move => finsuppQ finsuppR c1_triple c2_triple s varsSeq Ps.
case ck : k => [|n].
simpl; exact I.
unfold eval_com; fold eval_com.
simpl in varsSeq.
rewrite fsubUset in varsSeq.
move /andP in varsSeq.
destruct varsSeq as [varsc1_in_ls varsc2_in_ls].
rewrite ck in c1_triple c2_triple.
case ev_c1: (eval_com c1 s n) => [rs|e|].
- simpl.
  case : (restrP (names s :|: AQ :|: AR) rs) => [A s' namesd namessub] in ev_c1 *.
  rewrite bindrE.
  2: apply fdisjoint0s.
  case ev_c2 : (eval_com c2 s' n) => [rs2|e2|]. 
  + simpl.
    move => A0 finsuppR_c.
    apply (@pbindr_irrel _ AR A0 R (hide A rs2)).
      exact finsuppR.
      exact finsuppR_c.
      rewrite fdisjointUl in namesd.
      case /andP : namesd => namesd1 namesdAR.
      rewrite fdisjointUl in namesd1.
      case /andP : namesd1 => namesds namesdAQ.
      specialize (c1_triple s varsc1_in_ls Ps).
      rewrite ev_c1 in c1_triple.
      specialize (c1_triple AQ finsuppQ).
      apply (pbindrE _ finsuppQ namesdAQ) in c1_triple. 
      have domm_eq: pbind_res
                      (names s)
                      (fun s' => domm s'.1 = domm s.1)
                      (eval_com c1 s n).
        apply eval_com_vars.
        apply (fsubset_trans (subset_modvars_vars c1) varsc1_in_ls).
      rewrite ev_c1 in domm_eq.
      apply pbind_resE in domm_eq.
      apply pbindrE in domm_eq.
      - specialize (c2_triple s').
        rewrite ev_c2 in c2_triple.
        rewrite domm_eq in c2_triple.
        specialize (c2_triple varsc2_in_ls c1_triple).
        apply hide_pbindr.
        + exact finsuppR.
        + exact namesdAR.
        + apply (c2_triple AR finsuppR).
      - apply (@finsupp_subset _ _ _ (names (domm s.1))). (* finsupp subgoal *)
        + apply finsupp_domm_ls_eq. (* finsupp subgoal *)
        + apply (@fsubset_trans _ (names s.1)).
          rewrite namesmE.
          apply fsubsetUl.
          rewrite {2} (surjective_pairing s).
          rewrite namespE.
          simpl.
          apply fsubsetUl.
      - exact namesds.
  + simpl.
    specialize (c1_triple s varsc1_in_ls Ps).
    rewrite ev_c1 in c1_triple.
    rewrite fdisjointUl in namesd.
    case /andP : namesd => namesd1 namesdAR.
    rewrite fdisjointUl in namesd1.
    case /andP : namesd1 => namesds namesdAQ.
    specialize (c1_triple AQ finsuppQ).
    apply (pbindrE _ finsuppQ namesdAQ) in c1_triple. 
    have domm_eq: pbind_res
                    (names s)
                    (fun s' => domm s'.1 = domm s.1)
                    (eval_com c1 s n).
      apply eval_com_vars.
      apply (fsubset_trans (subset_modvars_vars c1) varsc1_in_ls).
    rewrite ev_c1 in domm_eq.
    apply pbind_resE in domm_eq.
    apply pbindrE in domm_eq.
    - specialize (c2_triple s').
      rewrite ev_c2 in c2_triple.
      rewrite domm_eq in c2_triple.
      apply (c2_triple varsc2_in_ls c1_triple).
    - apply (@finsupp_subset _ _ _ (names (domm s.1))).
      + apply finsupp_domm_ls_eq. 
      + apply (@fsubset_trans _ (names s.1)).
        rewrite namesmE.
        apply fsubsetUl.
        rewrite {2} (surjective_pairing s).
        rewrite namespE.
        simpl.
        apply fsubsetUl.
    - exact namesds.
  + exact I.
- simpl.
  specialize (c1_triple s varsc1_in_ls Ps).
  rewrite ev_c1 in c1_triple.
  exact c1_triple.
- by exact I.
Qed.

Lemma sequencing_rule P Q R c1 c2 e_set AQ AR :
  {finsupp AQ Q} -> {finsupp AR R} ->
  mem_safe_triple P c1 Q e_set ->
  mem_safe_triple Q c2 R e_set ->
  mem_safe_triple P (Seq c1 c2) R e_set.
Proof.
move => finsuppQ finsuppR c1_triple c2_triple s k varsc_in_ls Ps.
eapply sequencing_rule_strong.
- exact finsuppQ.
- exact finsuppR.
- move => s1 varsc1 Ps1.
  apply (c1_triple _ _ varsc1 Ps1).
- move => s2 varsc2 Qs2.
  apply (c2_triple _ _ varsc2 Qs2).
- exact varsc_in_ls.
- exact Ps.
Qed. 


Lemma while_rule_strong AP P e c k :
  {finsupp AP P} ->
  {{fun s => eval_expr true e s.1 = VBool true /\ P s}} c {{P}} mem_safety_errors ->
  forall k'', k'' <= k ->
  mem_safe_triple_counted
    P
    (While e c)
    (fun s => eval_expr true e s.1 = VBool false /\ P s)
    mem_safety_errors
    k''.
Proof.
move => finsuppP c_triple.
induction k => [|].
- move => k'' k''_le_k s vars_c1_in_ls Ps.
  rewrite leqn0 in k''_le_k.
  move /eqP in k''_le_k.
  rewrite k''_le_k.
  simpl.
  exact I.
- move => k'' k''_le_k s vars_while Ps.
  case e_ev : (eval_expr true e s.1) => [b|||].
  + rewrite leq_eqVlt in k''_le_k.
    move /orP in k''_le_k.
    destruct k''_le_k.
    * move /eqP in H.
      rewrite H.
      unfold eval_com.
      rewrite e_ev.
      fold eval_com.
      ** case cb : b.
         eapply (@sequencing_rule_strong 
          (fun s => eval_expr true e s.1 = VBool true /\ P s) 
          P 
          (fun s => eval_expr true e s.1 = VBool false /\ P s)
          c
          (While e c)
          mem_safety_errors
          AP
          AP).
          -- exact finsuppP.
          -- apply (@finsupp_eval_eq_bool_conj_prop _ AP e P finsuppP).
          -- move => s0c varscs0c Ps0c.
             apply c_triple.
             exact varscs0c.
             exact Ps0c.
          -- apply IHk.
             apply leq_pred.
             simpl in vars_while.
             simpl.
             rewrite fsetUC.
             rewrite <- fsetUA.
             rewrite fsetUid.
             exact vars_while.
             split.
             rewrite cb in e_ev.
             exact e_ev.
             exact Ps.
      ** apply (skip_rule).
         simpl. 
         apply fsub0set.
         split.
         rewrite cb in e_ev.
         exact e_ev.
         exact Ps.
    * rewrite ltnS in H.
      eapply IHk in H.
      apply H.
      exact vars_while.
      exact Ps.
  + rewrite leq_eqVlt in k''_le_k.
    move /orP in k''_le_k.
    destruct k''_le_k.
    * move /eqP in H.
      rewrite H.
      unfold eval_com.
      rewrite e_ev.
      exact. 
    * rewrite ltnS in H.
      eapply IHk in H.
      apply H.
      exact vars_while.
      exact Ps.
  + rewrite leq_eqVlt in k''_le_k.
    move /orP in k''_le_k.
    destruct k''_le_k.
    * move /eqP in H.
      rewrite H.
      unfold eval_com.
      rewrite e_ev.
      exact. 
    * rewrite ltnS in H.
      eapply IHk in H.
      apply H.
      exact vars_while.
      exact Ps.
  + rewrite leq_eqVlt in k''_le_k.
    move /orP in k''_le_k.
    destruct k''_le_k.
    * move /eqP in H.
      rewrite H.
      unfold eval_com.
      rewrite e_ev.
      exact. 
    * rewrite ltnS in H.
      eapply IHk in H.
      apply H.
      exact vars_while.
      exact Ps.
Qed.



Lemma while_rule AP P e c :
  {finsupp AP P} 
  -> {{fun s => eval_expr true e s.1 = VBool true /\ P s}} c {{P}}
      mem_safety_errors 
  -> {{P}} While e c {{fun s => eval_expr true e s.1 = VBool false /\ P s}}   
     mem_safety_errors.
Proof.
move => finsuppP c_triple s k vars_c1_in_ls Ps.
move : s vars_c1_in_ls Ps.
elim ck : k => [|k' IH].
intros.
by exact I.
have H := (@while_rule_strong AP P e c k finsuppP c_triple k (leqnn k)).
rewrite ck in H.
exact H.
Qed.

Lemma consequence_rule c AQ P Q P' Q' err_set:
  {finsupp AQ Q} ->
  {{P}} c {{Q}} err_set -> 
  (forall s, P' s -> P s) -> 
  (forall s, Q s -> Q' s) -> 
  {{P'}} c {{Q'}} err_set.
Proof.
move => finsuppQ c_triple P'implP QimplQ' s k varsc P's.
assert (Ps := P'implP s P's).
specialize (c_triple s k varsc Ps).
case c_ev : (eval_com c s k) => [s'|e|].
- move => A finsuppQ'.
  eapply pbindr_impl.
  exact finsuppQ.
  exact finsuppQ'.
  exact QimplQ'.
  rewrite c_ev in c_triple.
  apply c_triple. 
  exact finsuppQ.
- rewrite c_ev in c_triple.
  exact c_triple.
- exact I.
Qed.

Lemma conjunction_rule P1 P2 Q1 AQ1 Q2 AQ2 c e_set :
  {finsupp AQ1 Q1} -> {finsupp AQ2 Q2} ->
  {finsupp (AQ1 :|: AQ2) (conj Q1 Q2)} -> 
  mem_safe_triple P1 c Q1 e_set ->
  mem_safe_triple P2 c Q2 e_set ->
  mem_safe_triple (conj P1 P2) c (conj Q1 Q2) e_set.
Proof.
move => finsuppAQ1 finsuppAQ2 finsuppQ1Q2 Q1_triple Q2_triple 
  s k varsc_in_ls Ps.
elim ck : k => [|n].
by exact I.
move => H.
rewrite <- ck.
destruct Ps as [P1s P2s].
case ev_c: (eval_com c s k) => [rs|e|].
- have conj_suppU : pbindr (AQ1 :|: AQ2) (conj Q1 Q2) rs.
    apply pbindr_conj.
    + exact finsuppAQ1.
    + exact finsuppAQ2.
    + specialize (Q1_triple s k varsc_in_ls P1s).
      rewrite ev_c in Q1_triple.
      specialize (Q1_triple AQ1 finsuppAQ1).
      exact Q1_triple.
    + specialize (Q2_triple s k varsc_in_ls P2s).
      rewrite ev_c in Q2_triple.
      specialize (Q2_triple AQ2 finsuppAQ2).
      exact Q2_triple.
  move => A finsupp_conj.
  eapply (pbindr_impl finsuppQ1Q2 finsupp_conj).
  move => x conj_x.
  exact conj_x.
  exact conj_suppU.  
- specialize (Q2_triple s k varsc_in_ls P2s).
  rewrite ev_c in Q2_triple.
  exact Q2_triple.
- exact I.
Qed. 


Lemma conjunction_rule_postc P Q1 AQ1 Q2 AQ2 c e_set :
  {finsupp AQ1 Q1} -> {finsupp AQ2 Q2} ->
  {finsupp (AQ1 :|: AQ2) (conj Q1 Q2)} -> 
  mem_safe_triple P c Q1 e_set ->
  mem_safe_triple P c Q2 e_set ->
  mem_safe_triple P c (conj Q1 Q2) e_set.
Proof.
move => finsuppAQ1 finsuppAQ2 finsuppQ1Q2 Q1_triple Q2_triple 
  s k varsc_in_ls Ps.
elim ck : k => [|n].
by exact I.
move => H.
rewrite <- ck.
case ev_c: (eval_com c s k) => [rs|e|].
- have conj_suppU : pbindr (AQ1 :|: AQ2) (conj Q1 Q2) rs.
    apply pbindr_conj.
    + exact finsuppAQ1.
    + exact finsuppAQ2.
    + specialize (Q1_triple s k varsc_in_ls Ps).
      rewrite ev_c in Q1_triple.
      specialize (Q1_triple AQ1 finsuppAQ1).
      exact Q1_triple.
    + specialize (Q2_triple s k varsc_in_ls Ps).
      rewrite ev_c in Q2_triple.
      specialize (Q2_triple AQ2 finsuppAQ2).
      exact Q2_triple.
  move => A finsupp_conj.
  eapply (pbindr_impl finsuppQ1Q2 finsupp_conj).
  move => x conj_x.
  exact conj_x.
  exact conj_suppU.  
- specialize (Q2_triple s k varsc_in_ls Ps).
  rewrite ev_c in Q2_triple.
  exact Q2_triple.
- exact I.
Qed. 

Lemma disjunction_rule P1 P2 Q c e_set :
  mem_safe_triple P1 c Q e_set ->
  mem_safe_triple P2 c Q e_set ->
  mem_safe_triple (disj P1 P2) c Q e_set.
Proof.
move => Q1_triple Q2_triple s k varsc_in_ls disjP1P2s.
elim ck : k => [|n].
by exact I.
move => H.
rewrite <- ck.
unfold disj in disjP1P2s.
destruct disjP1P2s as [P1s | P2s].
- case ev_c: (eval_com c s k) => [rs|e|].
  + specialize (Q1_triple s k varsc_in_ls P1s).
    rewrite ev_c in Q1_triple.
    exact Q1_triple.
  + specialize (Q1_triple s k varsc_in_ls P1s).
    rewrite ev_c in Q1_triple.
    exact Q1_triple.
  + exact I.
- case ev_c: (eval_com c s k) => [rs|e|].
  + specialize (Q2_triple s k varsc_in_ls P2s).
    rewrite ev_c in Q2_triple.
    exact Q2_triple.
  + specialize (Q2_triple s k varsc_in_ls P2s).
    rewrite ev_c in Q2_triple.
    exact Q2_triple.
  + exact I.
Qed. 


End InferenceRules.

End Separation.