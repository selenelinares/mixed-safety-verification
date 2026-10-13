Require Import Coq.Strings.String.

From Coq Require Import Program.Equality. 

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssrnum ssrint seq.
From mathcomp Require Import eqtype choice seq order. 
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun fperm.

From CoqUtils Require Import nominal.

From memsafe Require Import syntax semantics lang_properties separation_logic_def separation_logic frame_conds_def nominal_proj_extension nominal_extension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope fset_scope.
Local Open Scope state_scope.

Local Notation locals := {fmap string -> value}.
Local Notation heap := {fmap ptr -> value}.
Local Notation state := (locals * heap)%type.

Notation "{{ P }} c {{ Q }} E" := (mem_safe_triple P c Q E) (at level 50). 
Local Infix "*" := separating_conjunction.
Local Infix "*N" := separating_conjunction_names (at level 20).

Implicit Type (e : expr) (c : com) (ls : locals) (h : heap)
              (s st: state) (π : {fperm name}) (v : value)
              (E : seq error)
              (P Q R : state -> Prop)
              (T : Type).


Section Fset_extension_lemmas.


Lemma fdisjoint_transR (T : ordType) (s1 s2 s3 : {fset T}) :
  fsubset s2 s3 -> fdisjoint s1 s3 -> fdisjoint s1 s2.
Proof.
move => H1 H2.
rewrite fdisjointC in H2.
rewrite fdisjointC.
apply (fdisjoint_trans H1 H2).
Qed.

Lemma fset_insert_remove_eq {T : ordType} (x : T) A:
  x \notin A -> (x |: A) :\ x = A.
Proof.
  move => H.
  rewrite fsetDUl.
  rewrite fsetDv.
  rewrite fset0U.
  apply /fsetDidPl.
  rewrite fdisjoints1.
  exact H.
Qed.

Lemma eq_of_fset0_iff {T : ordType} (A : {fset T}) :
  reflect (forall x, x \notin A) (A == fset0).
Proof.
apply /(iffP idP).
- move => A_eq_fset0 x.
  move /eqP in A_eq_fset0.
  rewrite A_eq_fset0 in_fset0.
  apply negbT; reflexivity.
- move => all_notin_A.
  apply /eqP; apply /eq_fset.
  move => x.
  apply bool_ext.
  + move => x_in_A.
    specialize (all_notin_A x).
    move /negP in all_notin_A.
    contradiction.
  + move => ff.
    rewrite in_fset0 in ff.
    discriminate ff.
Qed.

Lemma fsetInP {T : ordType} (A B : {fset T}) x :
  reflect (x \notin A \/ x \notin B) (x \notin A :&: B).
Proof.
apply /(iffP idP).
- move => x_nin_AB.
  apply /orP.
  rewrite <- negb_and.
  move /fsetIP in x_nin_AB.
  move /andP in x_nin_AB.
  exact x_nin_AB.
- move => nA_or_nB.
  apply /fsetIP.
  apply /andP.
  rewrite negb_and.
  apply /orP.
  exact nA_or_nB.
Qed.

End Fset_extension_lemmas.

Section Fmap_extension_lemmas.


Lemma f_nequal (A B : Type) (f : A -> B) (x y : A) :
  f x <> f y -> x <> y.
Proof.
apply contrapos.
apply f_equal.
Qed.

Lemma unionm_filterm (T: ordType) (S: Type) p q (m: {fmap T -> S}) :
  unionm (filterm p m) (filterm q m) 
   = filterm (fun k x => (p k x) || (q k x)) m.
Proof.
apply/eq_fmap=> k.
rewrite filtermE unionmE !filtermE.
case get_k: (m k)=> [x|] //=.
case c_pkv: (p k x).
- simpl; reflexivity. 
- case c_qkv: (q k x).
  + simpl; reflexivity.
  + simpl; reflexivity.
Qed.

Lemma filterm_true (T: ordType) (S: Type) (m: {fmap T -> S}): 
  filterm (fun _ _ => true) m = m.
Proof. 
apply/eq_fmap=> k.
rewrite filtermE.
case get_k: (m k)=> [x|] //=.
Qed.


Lemma domm_filterm {T : ordType} {S : Type} (m : {fmap T -> S}) p :
  domm (filterm (fun k _ => p k) m) = fset_filter p (domm m).
Proof.
apply/eq_fset => k.
rewrite mem_domm filtermE in_fset_filter.
case get_k: (m k) => [x|].
- simpl.
  rewrite mem_domm.
  rewrite get_k.
  case (p k); reflexivity.
- simpl.
  rewrite mem_domm.
  rewrite get_k.
  case (p k); reflexivity.
Qed.


End Fmap_extension_lemmas.

Section Nominal_extension_lemmas.

Lemma names_domm_name_inclusive_subheap
  {S} (m : {fmap ptr -> S}) A :
  fsubset A (names (domm m)) ->
  names (domm (name_inclusive_submap m A))
    = A.
Proof.
move => fsubset_A_dommm.
rewrite domm_filterm.
apply /eq_fset => n.
apply /namessP.
case_eq (n \in A) => [n_in_A|n_nin_A].
- assert (n_in_names_domm_m: n \in names (domm m)).
  + move /fsubsetP in fsubset_A_dommm.
    specialize (fsubset_A_dommm n n_in_A).
    exact fsubset_A_dommm.
  move /namessP in n_in_names_domm_m.
  destruct n_in_names_domm_m as [x x_in_domm_m].
  exists x.
  + rewrite in_fset_filter.
    apply /andP; split.
    * apply /fset0Pn.
      exists n.
      rewrite in_fsetI.
      apply /andP; split.
      exact H.
      exact n_in_A.
    * exact x_in_domm_m.
  + exact H.
- eapply (elimF idP) in n_nin_A.
  move => H.
  destruct H as [x x_in_filter n_in_names].
  rewrite in_fset_filter in x_in_filter.
  move /andP in x_in_filter; destruct x_in_filter as [disjoint_nx_A x_in_dommm].
  move /fdisjointP in disjoint_nx_A.
  apply disjoint_nx_A.
  move => y y_in_names.
  apply /negP.
  move => y_nin_A.
  assert (names_x_eq := names_ptr_eq x).
  rewrite names_x_eq in y_in_names n_in_names.
  move /fset1P in y_in_names.
  move /fset1P in n_in_names.
  rewrite y_in_names in y_nin_A.
  rewrite n_in_names in n_nin_A.
  contradiction.
Qed.


Lemma finsupp_perm_map_lookup_key
  {S T : nominalType} (m : {fmap S -> T}) x pi :
  finsupp_perm (names m) pi ->
  m (rename pi x) = m x.
Proof.
move => finsupperm.
case c_mx : (m x) => [v|].
- rewrite renameJ.
  + exact c_mx.
  + rewrite namesmE in finsupperm.
    unfold finsupp_perm in finsupperm.
    apply (fun p => fdisjoint_transR p finsupperm).
    apply (fun p => fsubset_trans p (fsubsetUl _ _)).
    apply namesin_subset.
    apply /dommP.
    exists v.
    exact c_mx.
- case x_case : (fsubset (names x) (names m) || (rename pi x == x)).
  + have x_rename : (rename pi x = x).
    * move /orP in x_case.
      destruct x_case.
      ** apply renameJ.
        unfold finsupp_perm in finsupperm.
        apply (fdisjoint_transR H finsupperm).
      ** move /eqP in H.
        exact H.
    rewrite x_rename.
    exact c_mx.
  + apply negbT in x_case.
    rewrite negb_or in x_case.
    move /andP in x_case.
    destruct x_case as [namesx_not_subset rename_x_neq_x].
    rewrite <- (renameK pi x) in rename_x_neq_x at 2.
    move /eqP in rename_x_neq_x.
    rewrite <- (renameK pi (rename pi x)) in rename_x_neq_x at 1.
    apply f_nequal in rename_x_neq_x.
    unfold finsupp_perm in finsupperm.
    move /fdisjointP in finsupperm.
    assert (overlap_supppi_pix :=
            (contrapos (@renameJ _ _ _) rename_x_neq_x)).
    move /negP in overlap_supppi_pix.
    unfold fdisjoint in overlap_supppi_pix.
    move /fset0Pn in overlap_supppi_pix.
    destruct overlap_supppi_pix as [n].
    move /fsetIP in H.
    destruct H as [n_in_supp n_in_names].
    specialize (finsupperm n n_in_supp).
    rewrite namesmE in finsupperm.
    rewrite in_fsetU in finsupperm.
    rewrite negb_or in finsupperm.
    move /andP in finsupperm.
    destruct finsupperm as [n_notin_domm n_notin_codomm].
    move /namesfsPn in n_notin_domm.
    specialize (n_notin_domm (rename pi x)).
    apply contrapos in n_notin_domm.
    * move /negP in n_notin_domm.
      move /dommPn in n_notin_domm.
      exact n_notin_domm.
    * apply /negP; apply /negPn.
      exact n_in_names.
Qed.



Lemma finsupp_perm_map_lookup_val
  {S T : nominalType} pi (m : {fmap S -> T}) x :
  (* weaken to names (codomm m) *)
  finsupp_perm (names m) pi ->
  rename pi (m x) = m x.
Proof.
move => finsupperm.
case c_mx : (m x) => [v|].
- rewrite renameJ.
  + reflexivity.
  + rewrite namesmE in finsupperm.
    unfold finsupp_perm in finsupperm.
    apply (fun p => fdisjoint_transR p finsupperm).
    apply (fun p => fsubset_trans p (fsubsetUr _ _)).
    have ex_c_mx : (exists x', m x' = Some v).
      exists x.
      exact c_mx.
    move /codommP in ex_c_mx.
    apply namesin_subset in ex_c_mx.
    rewrite (names_someE v).
    exact ex_c_mx.
- reflexivity.
Qed.

Lemma rename_preserves_map {S T: nominalType} pi (m : {fmap S -> T}) x:
  finsupp_perm (names m) pi -> 
  rename pi m x = m x.
Proof.
move => finsupperm.
rewrite renamemE.
rewrite (finsupp_perm_map_lookup_key _ (finsupp_perm_inv finsupperm)).
apply (finsupp_perm_map_lookup_val _ finsupperm).
Qed.

End Nominal_extension_lemmas.


Section Frame_conditions.

Lemma domm_sepconj_s :
  forall w s, lift_sc_seq_ptr_in_heap w s -> domm s.2 = w.
Proof.
rewrite /lift_sc_seq_ptr_in_heap /lift_bop_seq /lift_pred_seq_ptr_in_heap.
move => w s H.
rewrite -[RHS] fsvalK /=.
move : (uniq_fset w) H.
elim: (val w) => [|x {} w IH] /= in s *.
move =>  H1 H2.
rewrite /empty_heap in H2.
rewrite H2.
rewrite fset0E.
reflexivity.
case /andP => H1 H2.
case.
move => ls [h1] [h2] [-> h1_singleton h2_w h1h2_disjoint] /=.
rewrite domm_union fset_cons (IH _ _ h2_w) //. 
rewrite h1_singleton.
reflexivity.
Qed.

Lemma fset_insert_def {T:ordType} (x:T) X :
  (x |: X) = fset (x :: val X).
Proof.
unfold fsetU, fset1.
simpl.
reflexivity.
Qed.



(**** Proving Big-Sep as Domain Equation ****)

Lemma unionm_left_commute_disjoint 
  (T: ordType) (S: Type) (m1 m2 m3: {fmap T -> S}) :
    fdisjoint (domm m1) (domm m2)
    -> unionm m1 (unionm m2 m3) = unionm m2 (unionm m1 m3).
Proof.
move => disj_m1_m2.
rewrite unionmA.
rewrite (unionmC disj_m1_m2).
rewrite <- unionmA.
reflexivity.
Qed.


Lemma sepconj_left_commute (A B C : state -> Prop) s :
  (separating_conjunction A (separating_conjunction B C)) s
  <-> (separating_conjunction B (separating_conjunction A C)) s.
Proof.
unfold separating_conjunction.
split.
- move => ABC.
  destruct ABC as [ls [hA [hBC [s_eq pA BC disj_hA_hBC]]]].
  destruct BC as [ls2 [hB [hC [s_eq2 pB pC disj_hB_hC]]]].
  apply pair_equal_spec in s_eq2.
  destruct s_eq2 as [ls_eq_ls2 hBC_eq].
  rewrite hBC_eq domm_union fdisjointUr in disj_hA_hBC.
  move /andP in disj_hA_hBC.
  destruct disj_hA_hBC as [disj_hA_hB disj_hA_hC].
  rewrite <- ls_eq_ls2 in pB, pC.
  exists ls, hB, (unionm hA hC).
  split.
  * rewrite s_eq hBC_eq.
    f_equal.
    apply (@unionm_left_commute_disjoint _ _ _ _ _ disj_hA_hB).
  * exact pB.
  * exists ls, hA, hC.
    split.
    -- reflexivity.
    -- exact pA.
    -- exact pC.
    -- exact disj_hA_hC.
    -- rewrite domm_union fdisjointUr.
       apply /andP.
       split.
       ++ rewrite fdisjointC.
          exact disj_hA_hB.
       ++ exact disj_hB_hC.
- move => BAC.
  destruct BAC as [ls [hB [hAC [s_eq pB AC disj_hB_hAC]]]].
  destruct AC as [ls2 [hA [hC [s_eq2 pA pC disj_hA_hC]]]].
  apply pair_equal_spec in s_eq2.
  destruct s_eq2 as [ls_eq_ls2 hAC_eq].
  rewrite hAC_eq domm_union fdisjointUr in disj_hB_hAC.
  move /andP in disj_hB_hAC.
  destruct disj_hB_hAC as [disj_hB_hA disj_hB_hC].
  rewrite <- ls_eq_ls2 in pA, pC.
  exists ls, hA, (unionm hB hC).
  split.
  * rewrite s_eq hAC_eq.
    f_equal.
    apply (@unionm_left_commute_disjoint _ _ _ _ _ disj_hB_hA).
  * exact pA.
  * exists ls, hB, hC.
    split.
    -- reflexivity.
    -- exact pB.
    -- exact pC.
    -- exact disj_hB_hC.
    -- rewrite domm_union fdisjointUr.
      apply /andP.
      split.
      ++ rewrite fdisjointC.
          exact disj_hB_hA.
      ++ exact disj_hA_hC.
Qed.


Lemma fsetU_left_commute {T:ordType} (A B C : {fset T}) :
  A :|: (B :|: C) = B :|: (A :|: C).
Proof. 
rewrite fsetUA.
rewrite (fsetUC A B).
rewrite <- fsetUA.
reflexivity.
Qed.

Lemma fset_first {T : ordType} (x : T) A :
  (forall a, a \in A -> (x < a)%ord) ->
  val (fset (x :: A)) = (x :: val (fset A)).
Proof.
move => H.
rewrite /fset unlock.
simpl.
assert (x_notin_A : x \notin A).
apply (fun H => contraFN H Logic.eq_refl).
move => contr.
specialize (H x contr).
rewrite Ord.ltxx in H.
exact H.
rewrite (ifF _ _ (negbTE x_notin_A)).
apply (path.eq_sorted (@Ord.leq_trans _) (@Ord.anti_leq _)).
- apply (path.sort_sorted (@Ord.leq_total _)).
- simpl.
  rewrite path.path_min_sorted.
  + apply (path.sort_sorted (@Ord.leq_total _)).
  + apply /allP.
    move => a a_in_A'. 
    apply Ord.ltW.
    apply H.
    rewrite path.mem_sort in a_in_A'.
    by rewrite mem_undup in a_in_A'.
- apply uniq_perm_eq.
  + rewrite path.sort_uniq.
    simpl.
    apply /andP; split.
    * by rewrite mem_undup.
    * apply undup_uniq.
  + simpl.
    apply /andP; split.
    * rewrite path.mem_sort.
      by rewrite mem_undup.
    * rewrite path.sort_uniq.
      apply undup_uniq.
  move => y.
  rewrite path.mem_sort.
  rewrite in_cons.
  rewrite in_cons.
  rewrite path.mem_sort.
  reflexivity.
Qed.


Lemma fset_ordered_ind {T : ordType} (P : {fset T} -> Type) :
  P fset0 ->
  (forall x A, (forall a, a \in A -> (x < a)%ord) -> P A -> P (x |: A)) ->
  forall A, P A.
Proof.
move=> P0 PS []; elim=> [|/= x xs IH] Pxs.
- by rewrite eq_axiomK.
- move: IH => /(_ (path.path_sorted Pxs)).
  set s : {fset T} := FSet.FSet _; set s' : {fset T} := FSet.FSet _ => Ps.
  assert (x_min := allP (path.order_path_min (@Ord.lt_trans T) Pxs)).
  have x_nin_s : x \notin s.
  + by apply/negP=> /x_min; rewrite Ord.ltxx.
  assert (s'_eq: s' = x |: s).
  + by apply/eq_fset=> x'; rewrite in_fsetU1 !inE.
  rewrite s'_eq.
  apply PS.
  apply x_min.
  exact Ps.
Qed.

Lemma sepconj_eta_right P Q : P * [eta Q] = [eta P * Q].
Proof. auto. Qed.

Lemma filterm_key_neq_eq_remm {T:ordType} {U}
  (m : {fmap T -> U}) x :
  filterm (fun k => fun=> k != x) m = remm m x.
Proof.
apply/eq_fmap=> k.
case get_k : (m k)=> [v|] //=.
- rewrite filtermE.
  rewrite get_k //=.
  rewrite remmE.
  case H : (k == x) => [].
  simpl.
  reflexivity.
  simpl.
  rewrite get_k.
  reflexivity.
- rewrite filtermE.
  rewrite get_k //=.
  rewrite remmE.
  case H : (k == x) => [].
  reflexivity.
  rewrite get_k.
  reflexivity.
Qed.

Lemma mem_fsubset_mem {T : ordType} (A B: {fset T}) k :
  k \in A -> fsubset A B -> k \in B.
Proof.
move => kA fsubAB.
rewrite <- fsub1set in kA.
assert (H := fsubset_trans kA fsubAB).
rewrite <- fsub1set.
exact H.
Qed.

Lemma union_filterm_on_map
  (P Q : ptr -> value -> bool) (m : {fmap ptr -> value}) :
    (forall (k:ptr), (forall u, P k u) \/ (forall u, Q k u))
    -> unionm (filterm P m) (filterm Q m) = m.
Proof.
move => P_or_Q.
apply/eq_fmap=> k.
case get_k: (m k)=> [v|] //=.
- rewrite unionm_filterm.
  rewrite (eq_filterm (f2 := fun k x => true)).
  + rewrite filterm_true.
    exact get_k.
  move => ka va.
  specialize (P_or_Q ka).
  destruct P_or_Q as [Pka | Qka].
  + specialize (Pka va).
    rewrite Pka.
    apply orTb.
  + specialize (Qka va).
    rewrite Qka.
    apply orbT.
- apply /dommPn.
  move /dommPn in get_k.
  move /negP in get_k.
  apply /negP.
  move => contra.
  rewrite domm_union in contra.
  move /fsetUP in contra.
  destruct contra as [contraP| contraQ].
  + apply get_k.
    apply (@mem_fsubset_mem _ (domm (filterm P m)) (domm m) 
      k contraP (@domm_filter _ _ P m)).
  + apply get_k.
    apply (@mem_fsubset_mem _ (domm (filterm Q m)) (domm m) 
      k contraQ (@domm_filter _ _ Q m)).
Qed.

Lemma remm_unionm_distrib {T:ordType} {U} (m1 m2 : {fmap T -> U}) (x:T) :
  remm (unionm m1 m2) x = unionm (remm m1 x) (remm m2 x).
Proof.
apply/eq_fmap=> k.
rewrite remmE.
case ckx : (k == x) => [].
- rewrite unionmE.
  rewrite remmE.
  rewrite ckx //=.
  rewrite remmE.
  rewrite ckx //=.
- case get_k: (m1 k) => [v|] //=.
  + rewrite unionmE.
    rewrite get_k //=.
    rewrite unionmE.
    rewrite remmE.
    rewrite ckx get_k //=.
  + rewrite unionmE.
    rewrite get_k //=.
    rewrite unionmE.
    rewrite remmE.
    rewrite ckx get_k //=.
    rewrite remmE.
    rewrite ckx.
    reflexivity.
Qed.

Lemma remm_singleton x s :
  singleton x s 
  -> remm s.2 x = emptym.
Proof.
move => singletonh.
unfold singleton in singletonh.
apply /emptymP.
rewrite domm_rem.
rewrite singletonh.
rewrite fsetDv.
reflexivity.
Qed.


(*To do: This proof can be shortened*)
Lemma sepconj_singleton_left_iff_iff x P Q s :
  (separating_conjunction (singleton x) P s
    <-> separating_conjunction (singleton x) Q s)
  <-> (x \in domm s.2 -> (P (s.1, remm s.2 x) <-> Q (s.1, remm s.2 x))).
Proof.
unfold separating_conjunction. 
split.
- move => H s_in_domm_s2.
  destruct H as [exP_then_exQ exQ_then_exP].
  split.
  + move => Ps.
    assert (exP : exists (ls : locals) (h1 h2 : heap),
                  [/\ s = (ls, unionm h1 h2),
                      singleton x (ls, h1),
                      P (ls, h2)
                    & fdisjoint (domm h1) (domm h2)]).
    * exists s.1, (filterm (fun k v => k == x) s.2), (remm s.2 x).
      simpl.
      split.
      ** rewrite <- filterm_key_neq_eq_remm. 
         rewrite union_filterm_on_map.
          apply surjective_pairing.
         move => k. 
         case ck : (k == x).
         ++ left.
            move => v.
            apply is_true_true.
         ++ right.
            move => v.
            apply negbT.
            reflexivity.
      ** unfold singleton.
         simpl. 
         rewrite domm_filterm.
         apply eq_fset.
         move => y.
         rewrite in_fset_filter.
         rewrite in_fset1.
         apply andb_idr.
         move => y_eq_x.
         move /eqP in y_eq_x.
         rewrite y_eq_x.
         exact s_in_domm_s2.
      ** exact Ps.
      ** rewrite domm_filterm.
         rewrite domm_rem.
         unfold fset_filter.
         rewrite fdisjointC.
         apply /fsetDidPl.
         assert (fset1x : (fset [seq x0 <- domm s.2 | x0 == x]) = fset1 x).
          apply eq_fset.
          move => y.
          rewrite in_fset.
          rewrite mem_filter.
          apply /andP.
          case c_in : (y \in fset1 x).
            *** move /fset1P in c_in.
                split.
                apply /eqP.
                exact c_in.
                rewrite c_in.
                exact s_in_domm_s2.
            *** rewrite in_fset1 in c_in.
                move /eqP in c_in.
                move => contr.
                destruct contr as [contr1 contr2].
                move /eqP in contr1.
                contradiction.
         rewrite fset1x.
         rewrite fsetDDl. 
         rewrite fsetUid. 
         reflexivity.
    destruct (exP_then_exQ exP) as [ls [h1 [h2 [s_eq sing_x Qh2 dommdisj_h1_h2]]]].
    rewrite s_eq; simpl.
    rewrite remm_unionm_distrib.
      unfold singleton in sing_x.
      simpl in sing_x.
      assert (H1 : remm h1 x = emptym).
      -- apply /emptymP.
        rewrite domm_rem sing_x.
        apply /eqP.
        apply eq_fset.
        move => y.
        rewrite in_fsetD1 in_fset1 in_fset0.
        apply andNb.
      assert (H2 : remm h2 x = h2).
      -- rewrite sing_x in dommdisj_h1_h2.
        rewrite fdisjoint1s in dommdisj_h1_h2.
        apply (remmI dommdisj_h1_h2).
      rewrite H1 H2 union0m.
      exact Qh2.
  + move => Qs.
    assert (exQ : exists (ls : locals) (h1 h2 : heap),
      [/\ s = (ls, unionm h1 h2),
          singleton x (ls, h1),
          Q (ls, h2)
        & fdisjoint (domm h1) (domm h2)]).
    * exists s.1, (filterm (fun k v => k == x) s.2), (remm s.2 x).
      simpl.
      split.
      **rewrite <- filterm_key_neq_eq_remm. 
        rewrite union_filterm_on_map.
        apply surjective_pairing.
        move => k. 
        case ck : (k == x).
         ++ left.
            move => v.
            apply is_true_true.
         ++ right.
            move => v.
            apply negbT.
            reflexivity.
      **unfold singleton.
        simpl. 
        rewrite domm_filterm.
        apply eq_fset.
        move => y.
        rewrite in_fset_filter.
        rewrite in_fset1.
        apply andb_idr.
        move => y_eq_x.
        move /eqP in y_eq_x.
        rewrite y_eq_x.
        exact s_in_domm_s2.
      **exact Qs.
      **rewrite domm_filterm.
        rewrite domm_rem.
        unfold fset_filter.
        rewrite fdisjointC.
        apply /fsetDidPl.
        assert (fset1x : (fset [seq x0 <- domm s.2 | x0 == x]) = fset1 x).
          apply eq_fset.
          move => y.
          rewrite in_fset.
          rewrite mem_filter.
          apply /andP.
          case c_in : (y \in fset1 x).
          *** move /fset1P in c_in.
              split.
              apply /eqP.
              exact c_in.
              rewrite c_in.
              exact s_in_domm_s2.
          *** rewrite in_fset1 in c_in.
              move /eqP in c_in.
              move => contr.
              destruct contr as [contr1 contr2].
              move /eqP in contr1.
              contradiction.
              rewrite fset1x.
              rewrite fsetDDl. 
              rewrite fsetUid. 
              reflexivity.
      **destruct (exQ_then_exP exQ) as [ls [h1 [h2 [s_eq sing_x Ph2 dommdisj_h1_h2]]]].
        rewrite s_eq; simpl.
        rewrite remm_unionm_distrib.
        unfold singleton in sing_x.
        simpl in sing_x.
        assert (H1 : remm h1 x = emptym).
        --apply /emptymP.
          rewrite domm_rem sing_x.
          apply /eqP.
          apply eq_fset.
          move => y.
          rewrite in_fsetD1 in_fset1 in_fset0.
          apply andNb.
          assert (H2 : remm h2 x = h2).
        --rewrite sing_x in dommdisj_h1_h2.
          rewrite fdisjoint1s in dommdisj_h1_h2.
          apply (remmI dommdisj_h1_h2).
          rewrite H1 H2 union0m.
          exact Ph2.
- move => Ps_iff_Qs.
  split.
  + move => exSxP.
    destruct exSxP as [ls [h1 [h2 [s_eq sing_x Ph2 dommdisj_h1_h2]]]].
    exists ls, h1, h2.
    split.
    * exact s_eq.
    * exact sing_x.
    * rewrite s_eq in Ps_iff_Qs.
      simpl in Ps_iff_Qs.
      rewrite remm_unionm_distrib in Ps_iff_Qs.
      unfold singleton in sing_x.
      simpl in sing_x.
      assert (H1 : remm h1 x = emptym).
      -- apply /emptymP.
        rewrite domm_rem sing_x.
        apply /eqP.
        apply eq_fset.
        move => y.
        rewrite in_fsetD1 in_fset1 in_fset0.
        apply andNb.
      assert (H2 : remm h2 x = h2).
      -- rewrite sing_x in dommdisj_h1_h2.
        rewrite fdisjoint1s in dommdisj_h1_h2.
        apply (remmI dommdisj_h1_h2).
      rewrite H1 H2 union0m in Ps_iff_Qs.
      apply Ps_iff_Qs.
      -- rewrite domm_union.
         rewrite sing_x.
         rewrite in_fsetU1.
         apply /orP.
         left.
         apply /eqP.
         reflexivity.
      exact Ph2.
    * exact dommdisj_h1_h2.
  + move => exSxQ.
    destruct exSxQ as [ls [h1 [h2 [s_eq sing_x Qh2 dommdisj_h1_h2]]]].
    exists ls, h1, h2.
    split.
    * exact s_eq.
    * exact sing_x.
    * rewrite s_eq in Ps_iff_Qs.
      simpl in Ps_iff_Qs.
      rewrite remm_unionm_distrib in Ps_iff_Qs.
      assert (remmh1x: remm h1 x = emptym).
        apply (remm_singleton sing_x).
      rewrite remmh1x in Ps_iff_Qs.
      rewrite union0m in Ps_iff_Qs.
      assert (x_in_dommU : x \in domm (unionm h1 h2)).
        unfold singleton in sing_x.
        simpl in sing_x.
        rewrite domm_union.
        rewrite in_fsetU.
        apply /orP.
        left.
        rewrite sing_x.
        rewrite in_fset1.
        apply /eqP.
        reflexivity.
      specialize (Ps_iff_Qs x_in_dommU).
      rewrite remmI in Ps_iff_Qs.
      apply Ps_iff_Qs. 
      exact Qh2.
        rewrite domm_union in x_in_dommU.
        rewrite in_fsetU in x_in_dommU.
        move /orP in x_in_dommU.
        destruct x_in_dommU as [H1 | H2].
        move /fdisjointP in dommdisj_h1_h2.
        specialize (dommdisj_h1_h2 x H1).
        exact dommdisj_h1_h2.
        move /fdisjointP in dommdisj_h1_h2.
        specialize (dommdisj_h1_h2 x).
        unfold singleton in sing_x.
        simpl in sing_x.
        rewrite sing_x in dommdisj_h1_h2.
        rewrite in_fset1 in dommdisj_h1_h2.
        apply dommdisj_h1_h2.
        apply /eqxx.
    * exact dommdisj_h1_h2.
Qed.

Lemma fset_idem {T : ordType} (xs : seq T) :
  fset (fset xs) = fset xs.
Proof.
rewrite /fset unlock.
apply eq_fset.
simpl.
move => x.
rewrite path.mem_sort.
rewrite mem_undup.
reflexivity.
Qed.


(* Big-Sep as Domain Equation depends on this lemma *)
Lemma lift_sc_seq_ptr_in_heap_step ls v (P : {fset ptr}) :
  forall s x,
    x \notin P
    -> lift_sc_seq_ptr_in_heap (x |: P) s
      <-> separating_conjunction (singleton x) (lift_sc_seq_ptr_in_heap P) s.
Proof.
(*
  Strategy:
    foldr interprets `x |: A` as a seq. However, `x` is not necessarily at the head of this seq.
    Induct on the seq of `P`.
    1. If `P = [::]` then proving the lemma is fairly direct.
    2. If `P = y :: P'` test if `x < y \/ x > y` (`x <> y` as `x \notin P`).
        If `x < y` then `x |: (y :: P') = x :: (y :: P')`, and the proof is direct.
        If `x > y`, then we want to show
          `Sepconj (x :| (y :: P')) = x * Sepconj (y :: P')`
          = (by lemma: `y < x -> x :| (y :: A) = y :: (x :| A)`)
          `Sepconj (y :: (x :| P')) = x * y * Sepconj P'`
          = (by assoc-commute of `*`)
          `y * Sepconj (x :| P') = y * (x * Sepconj P')`
        of which the final eqn. is true by I.H.
*)
unfold lift_sc_seq_ptr_in_heap.
unfold lift_bop_seq.
unfold lift_pred_seq_ptr_in_heap.
elim /(@fset_ordered_ind ptr_ordType): P => [|p P p_notin_P IH].
- move => s x H.
  simpl.
  rewrite fsetU0.
  simpl.
  rewrite sepconj_eta_right.
  apply iff_refl.
- move => s x x_notpP.
  rewrite in_fsetU1 in x_notpP.
  move /norP in x_notpP.
  destruct x_notpP as [x_not_p x_notin_P].
  rewrite Ord.eq_op_leq in x_not_p.
  move /nandP in x_not_p.
  rewrite <- Ord.ltNge in x_not_p.
  rewrite <- Ord.ltNge in x_not_p.
  destruct x_not_p as [p_lt_x|x_lt_p].
  + rewrite fsetU_left_commute.
    rewrite (fset_first p_notin_P).
    rewrite (fset_first (x := p)).
    - simpl.
      rewrite (sepconj_eta_right (singleton x)).
      rewrite sepconj_left_commute.
      rewrite fsvalK.
      rewrite fsvalK.
      apply sepconj_singleton_left_iff_iff.
      move => p_in_domm_s2.
      specialize (IH (s.1, remm s.2 p) x x_notin_P).
      rewrite sepconj_eta_right in IH.
      apply IH.
    - move => a a_in_xP.
      simpl in a_in_xP.
      rewrite in_fsetU1 in a_in_xP.
      move /orP in a_in_xP.
      destruct a_in_xP as [a_eq_x|a_in_P].
      -- move /eqP in a_eq_x.
          rewrite a_eq_x.
          exact p_lt_x. 
      -- apply (p_notin_P _ a_in_P).
  + unfold fsetU.
    unfold fset1.
    simpl.
    rewrite fset_first.
    * simpl.
      rewrite fset_idem.
      rewrite sepconj_eta_right.
      apply iff_refl.
    * move => a a_in_pP.
      rewrite in_fsetU1 in a_in_pP.
      move /orP in a_in_pP.
      destruct a_in_pP as [a_eq_p|a_in_P].
      -- move /eqP in a_eq_p.
          rewrite a_eq_p.
          exact x_lt_p. 
      -- specialize (p_notin_P _ a_in_P).
        apply (Ord.lt_trans x_lt_p p_notin_P).
Qed.


(* Big-Sep as Domain Equation *)
Lemma fsubset_dom_impl_precond s w:
 (domm s.2) = w <-> lift_sc_seq_ptr_in_heap w s.
Proof.
split.
- destruct s. rename f into ls. rename f0 into h.
  apply (@fset_rect ptr_ordType (fun w => forall h,
                                          domm h = w 
                                          -> lift_sc_seq_ptr_in_heap w (ls,h))).
  + move => dommh_eq_fset0.
    rewrite /lift_sc_seq_ptr_in_heap /lift_bop_seq.
    unfold empty_heap.
    simpl.
    auto.
  + move => x P x_notin_P IH h0 dommh0.
    assert (exists h1 v, h0 = setm h1 x v /\ domm h1 = P).
      exists (remm h0 x).
      assert (exists v, getm h0 x = Some v).
        apply /dommP.
        rewrite dommh0.
        rewrite in_fsetU1.
        apply /orP.
        left.
        apply /eqxx.
      destruct H as [v H].
      exists v.
      split.
      rewrite setm_rem.
      rewrite (setmI H).
      reflexivity.
      rewrite domm_rem.
      rewrite dommh0.
      rewrite (fset_insert_remove_eq x_notin_P).
      reflexivity.
    destruct H as [h1 [v [h0_split domm_h1]]].
    assert (IH2 := IH h1 domm_h1).
    rewrite h0_split.
    rewrite (lift_sc_seq_ptr_in_heap_step ls v).
    unfold separating_conjunction.
    exists ls, (setm emptym x v), h1.
    split.
    reflexivity.
    unfold singleton.
    simpl.
    rewrite domm_set domm0.
    unfold fset1.
    apply fsetU0.
    apply IH2.
    rewrite domm_set domm0.
    rewrite fsetU0 fdisjoint1s.
    rewrite domm_h1.
    exact x_notin_P.
    exact x_notin_P.
- apply domm_sepconj_s.
Qed.


Lemma Precond_finsupp (wo : {fset ptr}): 
 {finsupp (names wo) lift_sc_seq_ptr_in_heap wo}.
Proof.
move => pi fp_nameswo_pi sx sy nomRsxsy.
rewrite <- nomRsxsy.
apply (fun s w => iff_trans (iff_sym (fsubset_dom_impl_precond s w))).
apply (fun s w X => iff_trans X (fsubset_dom_impl_precond s w)).
simpl.
rewrite domm_rename.
assert (Hy := iff_sym (rename_exchange_inv2 pi wo (domm sx.2))).
apply (fun Hx => iff_trans Hx Hy).
apply finsupp_perm_inv in fp_nameswo_pi.
rewrite (nomR_nominalJ fp_nameswo_pi).
apply iff_refl.
Qed.


Lemma domm_sepconj_rs :
forall wo (s' : {restr state}), 
  pbindr (names wo) (lift_sc_seq_ptr_in_heap wo) s'
  -> pbindr (names wo) (fun s' => domm s'.2 = wo)  s'.
move => wo s' sc_on_s'.
have H1 : {finsupp (names wo) (lift_sc_seq_ptr_in_heap wo)}.
  apply Precond_finsupp.
have H2 : {finsupp (names wo) (fun s' => domm s'.2 = wo)}.
  finsupp.
apply (pbindr_impl H1 H2 (@domm_sepconj_s wo)).
exact sc_on_s'. 
Qed.


Lemma valid_postcond_from_fctriple (c : com) (wi wo : {fset ptr}) : 
  forall k s1 (s1': {restr state}),
    fsubset (vars_c c) (domm s1.1)   
    -> fc_triple c wi wo
    -> lift_sc_seq_ptr_in_heap wi s1
    -> eval_com c s1 k = Done s1'
    -> pbindr (names wo) (lift_sc_seq_ptr_in_heap wo) s1'.
Proof.
move => k s1 s1' varsc_in_s1 cond_as_triple precond eval_com_c_s1.
unfold fc_triple in cond_as_triple.
unfold mem_safe_triple in cond_as_triple.
specialize (cond_as_triple s1 k).
rewrite eval_com_c_s1 in cond_as_triple.
apply cond_as_triple.
exact varsc_in_s1.
exact precond.
apply Precond_finsupp.
Qed.


Lemma domm_name_inclusive_subheap {S} (m : {fmap ptr -> S}) A :
  fsubset A (domm m)
  -> fdisjoint (names A) (names (domm m :\: A))
  -> domm (name_inclusive_submap m (names A)) = A.
Proof.
move => fsubset_A_domm_m fdisjoint_names.
rewrite domm_filterm.
apply /eq_fset => p.
apply bool_ext.
- move => p_in_filter.
  rewrite in_fset_filter in p_in_filter.
  move /andP in p_in_filter; destruct p_in_filter as [H2 H1].
  move /fset0Pn in H2; destruct H2 as [x H2].
  move /fsetIP in H2; destruct H2 as [H2 H3].
  rewrite names_ptr_eq in H2; move /fset1P in H2.
  rewrite H2 in H3.
  unfold fdisjoint in fdisjoint_names.
  move /eq_of_fset0_iff in fdisjoint_names.
  specialize (fdisjoint_names p.1).
  move /fsetInP in fdisjoint_names.
  case fdisjoint_names => [p1_nin_nA|p1_nin_ndommsubA].
  + move /negP in p1_nin_nA.
    contradiction.
  + rewrite -(fsetID (domm m) A) in H1.
    rewrite in_fsetU in H1.
    move /orP in H1.
    replace (domm m :&: A) with A in H1.
    2 : {move /fsetIidPr in fsubset_A_domm_m. 
        rewrite fsubset_A_domm_m. 
        reflexivity. }
    destruct H1.
    * exact H.  
    * apply ptr_namesin_in in H.
    move /negP in p1_nin_ndommsubA.
    contradiction.
- move => pinA.
  rewrite in_fset_filter.
  apply /andP.
  split.
    + apply namesin_subset in pinA.
      move /fsetIidPl in pinA.
      rewrite pinA.
      rewrite names_ptr_eq.
      apply /fset0Pn.
      exists p.1.
      apply /fset1P.
      reflexivity.
    + move /fsubsetP in fsubset_A_domm_m.
      specialize (fsubset_A_domm_m _ pinA).
      exact fsubset_A_domm_m.
Qed.


Lemma split_map {S : nominalType} {T : Type}
                (A : {fset name}) (m : {fmap S -> T}):
  fsubset A (names (domm m))
  -> (forall x, x \in domm m -> fsubset (names x) A \/ fdisjoint (names x) A)
  -> m = unionm (name_inclusive_submap m A) (name_avoiding_submap m A) /\ 
      names ( domm (name_inclusive_submap m A)) = A /\ 
      fdisjoint
        (names (domm (name_inclusive_submap m A)))
        (names (domm (name_avoiding_submap m A))) /\
      names (domm (name_avoiding_submap m A)) = names (domm m) :\: A.
Proof.
move => fsubsetAdomm A_partitions.
repeat split.
- rewrite unionm_filterm.
  apply/eq_fmap=> k.
  rewrite filtermE.
  rewrite orNb.
  case get_k: (m k)=> //=.
- rewrite domm_filterm.
  apply/eq_fset => k.
  apply /namesfsP.
  case ck_in_A : (k \in A).
  -- have H : k \in names (domm m).
      + move /fsubsetP in fsubsetAdomm.
        specialize (fsubsetAdomm k ck_in_A).
        exact fsubsetAdomm.
      move /namessP in H.
      destruct H as [x x_in_domm].
    apply (ex_intro2  _ _ x).
    + rewrite in_fset_filter.
      apply /andP.
      split.
      * apply /fset0Pn.
        exists k.
        rewrite in_fsetI.
        apply /andP; split.
        exact H.
        exact ck_in_A.
      * exact x_in_domm.
    + exact H.
  -- move => H.
    destruct H as [x H H1].
    rewrite in_fset_filter in H.
    move /andP in H.
    destruct H as [H2 H3].
    specialize (A_partitions x H3).
    assert (H5: names x != fset0).
    + apply /fset0Pn.
      exists k.
      exact H1.
    move /(names_subset_or_disjointP H5 A_partitions) in H2.
    move /fsubsetP in H2.
    specialize (H2 k H1).
    rewrite ck_in_A in H2.
    move /notF in H2.
    contradiction.
- apply /fdisjointP.
  rewrite domm_filterm.
  rewrite domm_filterm.
  move => k k_in_ovA. (* overlaps with A *)
  apply /negP.
  move => k_in_avA. (* avoids A *)
  move /namessP in k_in_ovA.
  destruct k_in_ovA as [x x_in_domm_ovA k_in_names_ovA].
  rewrite in_fset_filter in x_in_domm_ovA.
  case /andP : x_in_domm_ovA => Hov1 Hov2.
  move /namessP in k_in_avA.
  destruct k_in_avA as [y y_in_domm_avA k_in_names_avA].
  rewrite in_fset_filter in y_in_domm_avA.
  case /andP : y_in_domm_avA => Hav1 Hav2.
  assert (disjoint_namesy_A: fdisjoint (names y) A).
  -- unfold fdisjoint; exact Hav1.
  assert (namesx_nonempty: names x != fset0).
  -- apply /fset0Pn; exists k; exact k_in_names_ovA.
  move /(names_subset_or_disjointP namesx_nonempty (A_partitions _ Hov2)) in Hov1.
  move /fsubsetP in Hov1.
  assert (Hov3 := Hov1 _ k_in_names_ovA).
  move /fdisjointP in disjoint_namesy_A.
  assert (Hav3 := disjoint_namesy_A _ k_in_names_avA).
  move /negP in Hav3.
  contradiction.
- apply /eq_fset => k.
  apply /namessP.
  case H: (k \in names (domm m) :\: A).
  -- rewrite in_fsetD in H; move /andP in H.
    destruct H as [k_notin_A k_in_namesdommm].
    move /namessP in k_in_namesdommm.
    destruct k_in_namesdommm as [x x_in_domm k_in_namesx].
    apply (ex_intro2  _ _ x).
    rewrite domm_filterm.
    rewrite in_fset_filter.
    apply /andP; split.
    + destruct (A_partitions _ x_in_domm).
      * move /fsubsetP in H.
        specialize (H k k_in_namesx).
        move /negP in k_notin_A.
        contradiction.
      * exact H.
    + exact x_in_domm.
    exact k_in_namesx.
  -- move => H1.
    rewrite in_fsetD in H; move /nandP in H.
    destruct H1 as [x H1].
    rewrite domm_filterm in H1.
    rewrite in_fset_filter in H1.
    move /andP in H1; destruct H1.
    destruct H.
    + move /negPn in H.
      move /fdisjointP in H1.
      specialize (H1 k H0).
      move /negP in H1.
      contradiction.
    + move /namesfsPn in H.
      specialize (H x H2).
      move /negP in H.
      contradiction.
Qed.

Lemma split_heap {T : Type} (A : {fset name}) (m : {fmap ptr -> T}) :
  fsubset A (names (domm m))
  -> m = unionm (name_inclusive_submap m A) (name_avoiding_submap m A) /\ 
  names ( domm (name_inclusive_submap m A)) = A /\ 
  fdisjoint
    (names (domm (name_inclusive_submap m A)))
    (names (domm (name_avoiding_submap m A))) /\
  names (domm (name_avoiding_submap m A)) = names (domm m) :\: A.
Proof.
  move => H.
  assert (H1 := @split_map ptr_nominalType T _ _ H).
  assert (H2: forall x : ptr_nominalType,
          x \in domm m ->
          fsubset (names x) A \/
          fdisjoint (names x) A).
  move => x H3.
  apply (pointers_all_in_or_all_out  _ H3).
  specialize (H1 H2).
  exact H1.
Qed.



Lemma pbindr_mapr_comp {T S: nominalType} Df Dg  (g : S -> Prop) (f : T -> S) xx :
  {finsupp Dg g} -> {finsupp Df f} ->
  pbindr (Dg :|: Df) (g \o f) xx <-> pbindr Dg g (mapr Df f xx).
Proof.
move=> fs_g fs_f.
case: xx / (restrP (Dg :|: Df))=> [A x dis sub]. 
rewrite !maprE.
- rewrite pbindrE.
  apply pbindrE.
  + apply finsupp_app.
    apply finsupp_const.
    exact fs_g.
  + exact fs_f. 
  + exact dis. 
  rewrite fdisjointUl in dis.
  move /andP in dis.
  destruct dis as [disDg disDf].  
  exact disDg.
- rewrite fdisjointUl in dis.
  move /andP in dis.
  destruct dis as [disDg disDf].  
  exact disDf. 
Qed.


Lemma stateu_fold_strong sa1 sa2 sb1 sb2 :
  (unionm sa1 sb1, unionm sa2 sb2) =
    stateu (sa1,sa2) (sb1,sb2).
unfold stateu; auto.
Qed.


(********************************* MAIN THEOREMS **************************)

Lemma triple_impl_leak_freedom : 
forall (c : com) (fti fto: {fset ptr}),
  fc_triple c fti fto
  -> forall s k r1 r,
  fsubset (vars_c c) (domm s.1)
  -> fsubset fti (domm s.2)
  -> fdisjoint (names fti) (names (domm s.2 :\: fti))
  -> eval_com c (s.1, name_inclusive_submap s.2 (names fti)) k = Done r1
  -> eval_com c s k = Done r
  -> pbindr (names fto :|: names fti)
            (fun s' => leak_freedom fti fto (domm s'.2))
            r.
Proof.
move => c fti fto cond_as_triple s k r1 r vars_c_in_s fti_h2_subset
  fti_h2_names_disjoint eval_com_fti eval_com_s.
assert (s_split := split_map
    (namesfs_subset fti_h2_subset)
    (@pointers_all_in_or_all_out (names fti) (domm s.2))).
destruct s_split as [heap_eq_union [names_domm_incl [disj_incl_avoid
  names_domm_avoid]]].
rewrite (surjective_pairing s) in eval_com_s.
rewrite <- (unionmI s.1) in eval_com_s.
rewrite heap_eq_union in eval_com_s.
rewrite stateu_fold_strong in eval_com_s.
assert (ev_com_s_simpl := @frame_ok _
  (s.1,name_inclusive_submap s.2 (names fti))
  (s.1,name_avoiding_submap s.2 (names fti))
  _ _ vars_c_in_s disj_incl_avoid eval_com_fti
  ).
rewrite eval_com_s in ev_com_s_simpl.
injection ev_com_s_simpl.
move => r_eq_union.
destruct ev_com_s_simpl.
assert (fc_triple_postcond := cond_as_triple).
unfold fc_triple in fc_triple_postcond.
have fc_triple_precond : lift_sc_seq_ptr_in_heap fti (s.1,
  name_inclusive_submap s.2 (names fti)).
- rewrite <- fsubset_dom_impl_precond.
  simpl.
  rewrite domm_name_inclusive_subheap.
  + reflexivity.
  + exact fti_h2_subset.
  + exact fti_h2_names_disjoint.
unfold mem_safe_triple in fc_triple_postcond.
specialize (fc_triple_postcond (s.1, name_inclusive_submap s.2 (names fti)) k vars_c_in_s fc_triple_precond).
rewrite eval_com_fti in fc_triple_postcond.
specialize (fc_triple_postcond (names fto) (@Precond_finsupp fto)).
remember r1 as rx.
assert (rspec := restrP (names (s.1, name_inclusive_submap s.2 (names fti))) r1).
case: rspec => [A rs namesd namessub] in Heqrx.
rewrite Heqrx in r_eq_union.
rewrite r_eq_union.
rewrite <- pbindr_mapr_comp.
move => A' rs' r_eq disjoint_names_A'.
rewrite fdisjointUl in disjoint_names_A'.
rewrite fdisjointUl in disjoint_names_A'.
move /(andP) in disjoint_names_A'.
destruct disjoint_names_A' as [H1 disjoint_names_A'].
move /(andP) in H1.
destruct H1 as [H2 H3].
simpl.
unfold leak_freedom.
rewrite domm_union.
rewrite fsetIUr.
rewrite fsubUset.
apply /andP.
split. (*leak_freedom splits over union*)
rewrite Heqrx in fc_triple_postcond.
rewrite r_eq in fc_triple_postcond.
apply pbindrE in fc_triple_postcond.
rewrite <- fsubset_dom_impl_precond in fc_triple_postcond.
rewrite fc_triple_postcond.
apply fsubsetIr.
apply Precond_finsupp.
exact H2.
rewrite fdisjoint_fsetI0.
apply fsub0set.
rewrite fdisjointC.
apply fdisjoint_names_domm_set.
rewrite names_domm_incl in disj_incl_avoid.
rewrite fdisjointC.
exact disj_incl_avoid.
apply (finsupp_subset (A := names fti)).
- unfold leak_freedom.
  assert (H2 := @finsupp_fsetIl_heapdomm fti 
    (fun x => is_true (fsubset x fto))).
  simpl in H2.
  exact H2.
- apply fsubsetUr.
- apply finsupp_stateur.
Qed.


Lemma triple_impl_fresh_allocation (c : com) (fti fto: {fset ptr}): 
  fc_triple c fti fto 
  -> forall s k r1 (* r *),
    fsubset (vars_c c) (domm s.1) 
    -> fsubset fti (domm s.2)
    -> lift_sc_seq_ptr_in_heap fti (s.1, name_inclusive_submap s.2 (names fti))
    -> eval_com c (s.1, name_inclusive_submap s.2 (names fti)) k = Done r1
    -> fresh_allocation fti fto (domm s.2).
Proof.
move => cond_as_triple s k r1 (* r *) vars_c_in_s fti_h2_subset
  fc_triple_precond eval_com_fti (* eval_com_s *).
assert (s_split := split_map 
    (namesfs_subset fti_h2_subset)
    (@pointers_all_in_or_all_out (names fti) (domm s.2))).
destruct s_split as [heap_eq_union [names_domm_incl [disj_incl_avoid      
  names_domm_avoid]]].
assert (ev_com_s_simpl := @frame_ok _
  (s.1,name_inclusive_submap s.2 (names fti))
  (s.1,name_avoiding_submap s.2 (names fti))
  _ _ vars_c_in_s disj_incl_avoid eval_com_fti
  ).
destruct ev_com_s_simpl.
assert (fc_triple_postcond := cond_as_triple).
unfold fc_triple in fc_triple_postcond.
unfold mem_safe_triple in fc_triple_postcond.
specialize (fc_triple_postcond (s.1, name_inclusive_submap s.2 (names fti)) k   
  vars_c_in_s fc_triple_precond).
rewrite eval_com_fti in fc_triple_postcond.
specialize (fc_triple_postcond (names fto) (@Precond_finsupp fto)).
have disj_names_r1_avoiding : pbind_res 
  (names (names (domm (name_avoiding_submap s.2 (names fti)))))
  (fun st => fdisjoint (names (domm st.2)) 
      (names (domm (name_avoiding_submap s.2 (names fti)))))
  (Done r1).
  apply (@evalc_disj c (s.1, name_inclusive_submap s.2 (names fti)) k  (domm (name_avoiding_submap s.2 (names fti))) r1 disj_incl_avoid eval_com_fti).
apply pbind_resE in disj_names_r1_avoiding.
remember r1 as rx.
assert (rspec := restrP (names (s.1, name_inclusive_submap s.2 (names fti)) :|: 
  names (name_avoiding_submap s.2 (names fti)) :|: names fto) r1).
case: rspec => [A rs namesd namessub] in Heqrx.
simpl.
rewrite fdisjointUl fdisjointUl in namesd.
case /andP : namesd => namesd namesd_fto.
case /andP : namesd => namesd_inclusive namesd_avoiding.
rewrite namesmE fdisjointUl in namesd_avoiding.
case /andP : namesd_avoiding => namesd_avoid_domm namesd_avoid_codomm.
rewrite Heqrx in fc_triple_postcond disj_names_r1_avoiding.
apply pbindrE in fc_triple_postcond.
- apply fsubset_dom_impl_precond in fc_triple_postcond.
  apply pbindrE in disj_names_r1_avoiding.
  + assert (disj_r1_avoiding := fdisjoint_names_domm disj_names_r1_avoiding).
    rewrite fc_triple_postcond in disj_r1_avoiding.
    unfold fdisjoint in disj_r1_avoiding.
    move /eqP in disj_r1_avoiding.
    unfold fresh_allocation.
    rewrite heap_eq_union.
    rewrite domm_union fsetIUr.
    rewrite disj_r1_avoiding.
    rewrite fsetU0.
    apply fsubset_dom_impl_precond in fc_triple_precond.
    rewrite fc_triple_precond.
    apply fsubsetIr.
  + apply finsupp_fsetD.
  + rewrite names_names_eq.
    exact namesd_avoid_domm.
- apply Precond_finsupp.
- exact namesd_fto.
Qed.
  

Lemma triple_impl_inertia (c : com) (fti fto: {fset ptr}):
fc_triple c fti fto
-> forall s k r r',
fsubset (vars_c c) (domm s.1)
-> fsubset fti (domm s.2)
-> fdisjoint (names fti) (names (domm s.2 :\: fti))
-> eval_com c (s.1, name_inclusive_submap s.2 (names fti)) k = Done r
-> eval_com c s k = Done r'
-> pbindr (names fto :|: names s.2)
          (fun s' => inertia fti fto s.2 s'.2)
          r'.
Proof.
move => cond_as_triple s k r r' vars_c_in_s fti_h2_subset
  fti_h2_names_disjoint eval_com_fti eval_com_s.
assert (s_split := split_map
    (namesfs_subset fti_h2_subset)
    (@pointers_all_in_or_all_out (names fti) (domm s.2))).
destruct s_split as [heap_eq_union [names_domm_incl [disj_incl_avoid
  names_domm_avoid]]].
rewrite (surjective_pairing s) in eval_com_s.
rewrite <- (unionmI s.1) in eval_com_s.
rewrite heap_eq_union in eval_com_s.
rewrite stateu_fold_strong in eval_com_s.
assert (ev_com_s_simpl := @frame_ok _
  (s.1,name_inclusive_submap s.2 (names fti))
  (s.1,name_avoiding_submap s.2 (names fti))
  _ _ vars_c_in_s disj_incl_avoid eval_com_fti
  ).
rewrite eval_com_s in ev_com_s_simpl.
injection ev_com_s_simpl.
move => r'_eq_union.
destruct ev_com_s_simpl.
assert (fc_triple_postcond := cond_as_triple).
unfold fc_triple in fc_triple_postcond.
have fc_triple_precond : lift_sc_seq_ptr_in_heap fti (s.1,
  name_inclusive_submap s.2 (names fti)).
  rewrite <- fsubset_dom_impl_precond.
  simpl.
  rewrite domm_name_inclusive_subheap.
  + reflexivity.
  + exact fti_h2_subset.
  + exact fti_h2_names_disjoint.
unfold mem_safe_triple in fc_triple_postcond.
specialize (fc_triple_postcond (s.1, name_inclusive_submap s.2 (names fti)) k vars_c_in_s fc_triple_precond).
rewrite eval_com_fti in fc_triple_postcond.
specialize (fc_triple_postcond (names fto) (@Precond_finsupp fto)).
remember r as rx.
assert (rspec := restrP (names (s.1, name_inclusive_submap s.2 (names fti))) r).
case: rspec => [A rs namesd namessub] in Heqrx.
rewrite Heqrx in r'_eq_union.
rewrite r'_eq_union.
rewrite <- pbindr_mapr_comp.
- move => A' rs' r'_eq disjoint_names_A'.
  rewrite fdisjointUl in disjoint_names_A'.
  rewrite fdisjointUl in disjoint_names_A'.
  move /(andP) in disjoint_names_A'.
  destruct disjoint_names_A' as [H1 disjoint_names_A'].
  move /(andP) in H1.
  destruct H1 as [H2 H3].
  apply fsubset_dom_impl_precond in fc_triple_precond.
  rewrite Heqrx in fc_triple_postcond.
  rewrite r'_eq in fc_triple_postcond.
  apply pbindrE in fc_triple_postcond.
  rewrite <- fsubset_dom_impl_precond in fc_triple_postcond.
  simpl.
  unfold inertia.
  move => l l_notin_wi l_notin_wo.
  rewrite unionmE.
  rewrite <- fc_triple_postcond in l_notin_wo.
  move /dommPn in l_notin_wo.
  rewrite l_notin_wo /=. 
  rewrite {1} heap_eq_union.
  rewrite <- fc_triple_precond in l_notin_wi.
  move /dommPn in l_notin_wi.
  rewrite unionmE.
  rewrite l_notin_wi /=.
  reflexivity.
- apply Precond_finsupp.
  exact H2.
- unfold inertia.
  move => pi finsuppperm x y nomRxy.
  rewrite <- nomRxy.
  simpl.
  assert (finsuppperm_fti : finsupp_perm (names fti) pi).
  * apply (fsubset_finsupp_perm (finsupp_perm_unR finsuppperm)).
    rewrite namesmE.
    apply (fun p => fsubset_trans p (fsubsetUl _ _)).
    apply (namesfs_subset fti_h2_subset).
  split.
  * move => H l l_nin_fti l_nin_fto.
    rewrite renamemE.
    assert (H1 : rename (pi^-1)%fperm l \notin fti).
    ** apply finsupp_perm_inv in finsuppperm_fti.
       apply (finsupp_perm_notin_preserv finsuppperm_fti l_nin_fti).
    assert (H2 : rename (pi^-1)%fperm l \notin fto).
    ** apply finsupp_perm_inv in finsuppperm.
       apply (finsupp_perm_notin_preserv (finsupp_perm_unL finsuppperm) l_nin_fto).
    specialize (H (rename (pi^-1)%fperm l) H1 H2).
    apply rename_exchange_inv.
    apply (Logic.eq_trans (y := s.2 (rename (pi^-1)%fperm l))).
    ** rewrite (@finsupp_perm_map_lookup_val _ _ ((pi^-1)%fperm) s.2 l
                (finsupp_perm_inv (finsupp_perm_unR finsuppperm))).
       rewrite (@finsupp_perm_map_lookup_key _ _ s.2 l ((pi^-1)%fperm)
                (finsupp_perm_inv (finsupp_perm_unR finsuppperm))).
       reflexivity.
    ** exact H.
  * move => H l l_nin_fti l_nin_fto.
    assert (H1 := finsupp_perm_notin_preserv finsuppperm_fti l_nin_fti).
    assert (H2 := finsupp_perm_notin_preserv 
      (finsupp_perm_unL finsuppperm) l_nin_fto).
    specialize (H (rename pi l) H1 H2).
    rewrite renamemE in H.
    rewrite renameK in H.
    apply (rename_exchange_inv
            (T := option_nominalType value_nominalType)) in H.
    apply (Logic.eq_trans
            (y := rename (pi^-1)%fperm (s.2 (rename pi l)))).
    ** 2: exact H.
    rewrite <- (fperm_invK pi) at 2.
    rewrite <- (renamemE (pi^-1)%fperm s.2).
    assert (H4 := @rename_preserves_map ptr_nominalType _ (pi^-1)%fperm s.2 l).
    specialize (H4 (finsupp_perm_inv (finsupp_perm_unR finsuppperm))).
    rewrite H4.
    reflexivity.
- apply finsupp_stateur.
Qed.

End Frame_conditions.
