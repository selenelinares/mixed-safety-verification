Require Import Coq.Strings.String.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype choice seq ssrnum ssrint ssralg bigop.

From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun fperm.

From CoqUtils Require Import nominal.

From memsafe Require Import syntax semantics nominal_proj_extension nominal_extension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Structured.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.
Local Open Scope state_scope.

Notation locals := {fmap string -> value}.
Notation heap := {fmap ptr -> value}.

Implicit Types (ls : locals) (h : heap) (x : string) (s : locals * heap).
Implicit Types (A : {fset name}).


Lemma mod_vars_c_subset c : fsubset (mod_vars_c c) (vars_c c).
Proof.
elim: c=> [x e|x e|e e'|x e|e| |c1 IH1 c2 IH2|e c1 IH1 c2 IH2|e c IH] /=;
rewrite ?fsub0set ?fsub1set ?in_fsetU1 ?eqxx //.
- by rewrite fsetUSS.
- by rewrite -fsetUA; apply: fsubsetU; rewrite fsetUSS // orbT.
by rewrite fsubsetU // IH orbT.
Qed.


Lemma eval_expr_unionm cast ls1 ls2 e :
  fsubset (vars_e e) (domm ls1) ->
  eval_expr cast e (unionm ls1 ls2) =
  eval_expr cast e ls1.
Proof.
elim: e => [x|b|n|b e1 IH1 e2 IH2|e IH| |e IH|e IH|e IH] //=.
- by rewrite fsub1set unionmE => /dommP [v ->].
- by rewrite fsubUset=> /andP [/IH1 {IH1} -> /IH2 {IH2} ->].
- by case: cast IH=> // IH sub; rewrite IH.
- by case: cast IH=> // IH sub; rewrite IH.
- by case: cast IH=> // IH sub; rewrite IH.
by case: cast IH=> // IH sub; rewrite IH.
Qed.

(* NAMES *)

Lemma eval_binop_names b v1 v2 :
  fsubset (names (eval_binop b v1 v2)) (names (v1, v2)).
Proof.
case: b v1 v2=> [] [b1|n1|p1 sz1|] [b2|n2|p2 sz2|] //=;
  try by rewrite fsub0set.
- by rewrite fsubsetU //= !namesvE fsubsetxx orbT.
- by rewrite fsubsetU //= !namesvE fsubsetxx.
by rewrite fsubsetU //= !namesvE fsubsetxx.
Qed.


Lemma eval_expr_names cast ls e :
  fsubset (names (eval_expr cast e ls)) (names ls).
Proof.
elim: e=> [x|b|n|b e1 IH1 e2 IH2|e IH| |e IH|e IH|e IH] //=;
  try by rewrite fsub0set.
- case get_x: (ls x) => [[b|n|p|]|] //=; try by rewrite fsub0set.
  apply/fsubsetP=> i; rewrite namesvE => /fset1P -> {i}.
  apply/namesmP; eapply PMFreeNamesVal; eauto.
  by rewrite namesvE; apply/namesnP.
- by rewrite (fsubset_trans (eval_binop_names b _ _)) // fsubUset IH1 IH2.
- by case: eval_expr => // *; rewrite fsub0set.
- by case: eval_expr => // *; rewrite fsub0set.
- by case: eval_expr => // *; rewrite fsub0set.
case: cast IH=> //.
by case: (eval_expr _ _ _)=> [b|n|p|]; rewrite fsub0set.
Qed.

(*MBLOCK*)

Lemma domm_mkblock i vs :
  domm (mkblock i vs) = fset [seq (i, Posz n) | n <- iota 0 (size vs)].
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => /= - [i' n].
  move=> /dommP [v].
  rewrite mkblockE /= in_fset.
  have [-> {i'}|] //= := altP eqP.
  case: n=> [n|] //=.
  case: ifP=> [n_vs|] //= [e].
  apply/mapP; exists n=> //.
  by rewrite mem_iota.
rewrite in_fset=> /mapP /= [n'].
rewrite mem_iota /= add0n => n_vs [-> ->].
apply/dommP; exists (nth VNil vs n').
by rewrite mkblockE /= eqxx n_vs.
Qed.


Lemma names_domm_mkblock i vs :
  names (domm (mkblock i vs)) = if nilp vs then fset0 else fset1 i.
Proof.
case: ifP=> [/nilP ->|nnil_vs].
  rewrite (_ : mkblock i [::] = emptym) ?domm0 ?namesfs0 //.
  apply/eq_fmap=> p; rewrite mkblockE /= emptymE.
  by case: ifP=> //; case: p.2.
rewrite domm_mkblock names_fset.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> i'.
  case/namessP=> /= [[i'' n] /mapP [n' ?] [-> ?]].
  by rewrite in_fsetU /= namesT in_fset0 orbF namesnE.
move=> /fset1P ->.
apply/namessP; exists (i, Posz 0).
  apply/mapP; exists 0=> //.
  rewrite mem_iota /= add0n.
  by case: vs nnil_vs.
by rewrite in_fsetU /= namesT in_fset0 orbF namesnE in_fset1 eqxx.
Qed.

Lemma codomm_mkblock i vs : codomm (mkblock i vs) = fset vs.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> v.
  case/codommP=> /= - [i' n].
  rewrite mkblockE /=.
  have [_ {i'}|] //= := altP eqP.
  case: n=> [n|] //=.
  case: ifP=> [n_vs|] //= [<-].
  rewrite in_fset.
  by apply/mem_nth.
rewrite in_fset => v_vs.
apply/codommP.
exists (i, Posz (index v vs)).
by rewrite mkblockE /= eqxx index_mem v_vs nth_index.
Qed.

Lemma names_codomm_mkblock i vs :
  names (codomm (mkblock i vs)) = names vs.
Proof. by rewrite codomm_mkblock names_fset. Qed.

Lemma names_mkblock i vs :
  names (mkblock i vs) = if nilp vs then fset0 else i |: names vs.
Proof.
rewrite namesmE names_domm_mkblock names_codomm_mkblock.
case: vs=> //=.
by rewrite fset0U namessE.
Qed.

Lemma names_mkblock_fsubset i vs :
  fsubset (names (mkblock i vs)) (i |: names vs).
Proof.
by rewrite names_mkblock fun_if if_arg fsub0set fsubsetxx if_same.
Qed.

Lemma fdisjoint_names_domm h1 h2 :
  fdisjoint (names (domm h1)) (names (domm h2)) ->
  fdisjoint (domm h1) (domm h2).
Proof.
move=> /fdisjointP dis; apply/fdisjointP=> p Pp.
have /dis Pi: p.1 \in names (domm h1).
  by apply/namesfsP; exists p=> //=; apply/fsetUP; left; apply/namesnP.
apply: contra Pi=> Pi; apply/namesfsP; exists p=> //.
by apply/fsetUP; left; apply/namesnP.
Qed.

Lemma fdisjoint_names_domm_set h1 (A : {fset ptr}) :
  fdisjoint (names (domm h1)) (names A) ->
  fdisjoint (domm h1) A.
Proof.
move=> /fdisjointP dis; apply/fdisjointP=> p Pp.
have /dis Pi: p.1 \in names (domm h1).
  by apply/namesfsP; exists p=> //=; apply/fsetUP; left; apply/namesnP.
apply: contra Pi=> Pi; apply/namesfsP; exists p=> //.
by apply/fsetUP; left; apply/namesnP.
Qed.

Lemma eval_com_vars s c k :
  fsubset (mod_vars_c c) (domm s.1) ->
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
- by move=> Px _ [<-]; rewrite restrE0 domm_set sub.
- case: eval_expr => // p sz Px.
  case: getm=> [v|] //= _ [<-]; by rewrite restrE0 domm_set sub.
- case: eval_expr=> // p sz _.
  by rewrite /updm; case: getm=> [v|] //= _ [<-]; rewrite restrE0.
- case: eval_expr => [|[n|]| |] // Px _ [<-].
  by rewrite /new pbindrE ?fdisjoints1 ?freshP //= domm_set sub.
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
  by case/andP=> vars_c1 vars_c2; case: b; eapply IH; eauto.
case: eval_expr=> // - [] P; apply: IH; try by rewrite fsub0set.
by rewrite /= fsetUid.
Qed.

(* FIXME: Replacing [names A] by [A] below breaks typeclass inference. *)
Lemma eval_com_blocks A s c k :
  fdisjoint (names (domm s.2)) A ->
  pbind_res
    (names A)
    (fun s' => fdisjoint (names (domm s'.2)) A)
    (eval_com c s k).
Proof.
elim: k s c => [|k IH] /= s //.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=.
- by move=> dis _ [<-]; rewrite restrE0.
- case: eval_expr=> //= p sz; case: getm=> //= v dis _ [<-].
  by rewrite restrE0.
- case: eval_expr=> //= p sz; rewrite /updm.
  case get_p: getm=> [v|] //= dis _ [<-]; rewrite restrE0 /= domm_set.
  suff/fsetUidPr ->: fsubset (fset1 p) (domm s.2) by [].
  by rewrite fsub1set mem_domm get_p.
- case: eval_expr=> [| [n|] | |] //= dis _ [<-].
  eapply pbindr_new; try by finsupp.
  move=> i nin_A nin_s; rewrite restrE0 /=.
  have {dis} dis_i: fdisjoint (i |: names (domm s.2)) A.
    by rewrite fdisjointUl fdisjoint1s -{1}[A]namesfsnE nin_A.
  apply: fdisjoint_trans dis_i.
  rewrite domm_union namesfsU names_domm_mkblock !(fun_if, if_arg).
  by rewrite fset0U fsubsetxx fsubsetUr if_same.
- case: eval_expr=> //= p sz; case: ifP=> //= _ dis; case: ifP=> //= _ _ [<-].
  by rewrite restrE0 /=; apply: fdisjoint_trans dis; rewrite namesfs_subset // domm_filter.
- by move=> dis _ [<-]; rewrite restrE0 /=.
- move=> dis.
  have := IH _ c1 dis.
  by eapply pbind_res_bind; finsupp.
- by case: eval_expr=> // b; apply: IH.
- by case: eval_expr=> // b; apply: IH.
Qed.


Lemma frame_ok c s1 s2 k rs :
  fsubset (vars_c c) (domm s1.1) ->
  fdisjoint (names (domm s1.2)) (names (domm s2.2)) ->
  eval_com c s1 k = Done rs ->
  eval_com c (s1 ∪ s2) k =
  Done (mapr (names s2) (stateu ^~ s2) rs).
Proof.
elim: k c s1 rs => [|k IH] //= c s1 rs.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=;
rewrite ?fsubUset ?fsub1set.
- case/andP=> [x_in_vs sub] dis [<-] {rs}.
  by rewrite restrE0 eval_expr_unionm // setm_union.
- case/andP=> [x_in_vs sub] dis.
  rewrite eval_expr_unionm //; case: eval_expr=> //= p sz.
  rewrite unionmE; case get_p: getm=> [v|] //= [<-] {rs}.
  by rewrite maprE0 setm_union.
- case/andP=> [sub1 sub'] dis.
  rewrite !eval_expr_unionm //; case: eval_expr=> //= p sz.
  rewrite /updm unionmE; case: getm=> //= _ [<-] {rs}.
  by rewrite maprE0 setm_union.
- case/andP=> [x_in_vs sub] dis.
  rewrite eval_expr_unionm //; case: eval_expr=> [|[n|]| |] //= [<-] {rs}.
  move: (fresh _) (freshP (names s1 :|: names s2)) => i.
  rewrite in_fsetU !negb_or=> /andP [i1 i2].
  rewrite [in RHS](@newE _ _ _ i) //.
  rewrite namespE /=.
  move els: (unionm s1.1 s2.1) => ls; move eh: (unionm s1.2 s2.2)=> h.
  rewrite [in LHS](@newE _ _ _ i) -?{}els -?{}eh.
    by rewrite maprE ?setm_union ?unionmA // fdisjoints1.
  have: fsubset (names (s1 ∪ s2)) (names s1 :|: names s2).
    eapply nom_finsuppP; finsupp.
  by move=> /fsubsetP/(_ i)/contra; apply; rewrite in_fsetU negb_or i1.
- move=> sub dis.
  rewrite !eval_expr_unionm //; case: eval_expr=> //= p sz.
  case: ifP=> //= _; rewrite !domm_curry domm_union imfsetU in_fsetU.
  case: ifP=> //= /imfsetP [p' in_h1 e_p] [<-] {rs}.
  rewrite maprE0 filterm_union ?fdisjoint_names_domm // (_ : filterm _ s2.2 = s2.2) //.
  have {p' e_p in_h1} id_in_h1 : p.1 \in names (domm s1.2).
    by apply/namesfsP; exists p'=> //; rewrite e_p in_fsetU namesnE in_fset1 eqxx.
  apply/eq_fmap=> p'; rewrite filtermE.
  case get: (s2.2 p')=> [v|] //=.
  have [e_p|] //= := altP (_ =P _).
  suffices in_h2 : p.1 \in names (domm s2.2).
    by move/fdisjointP/(_ _ id_in_h1): dis; rewrite in_h2.
  apply/namesfsP; exists p'; first by apply/dommP; eauto.
  by rewrite -e_p in_fsetU namesnE in_fset1 eqxx.
- by move=> _ dis [<-] {rs}; rewrite maprE0.
- case/andP=> [sub1 sub2] dis.
  case ev_c1: eval_com => [rs1| |] //=.
  case/(restrP (names s1 :|: names s2)):
    rs1 ev_c1 => /= [A s' dis' sub] ev_c1.
  move: dis'; rewrite fdisjointUl => /andP [dis1 dis2].
  rewrite bindrE ?fdisjoint0s ?(IH _ _ (hide A (Restr s'))) //.
  case ev_c2: eval_com => [rs2|e|] //= [<-] {rs}.
  rewrite maprE // bindrE ?fdisjoint0s //=.
  rewrite (IH _ _ rs2) //= -?hide_mapr //.
    have:= @eval_com_vars _ _ k (fsubset_trans (mod_vars_c_subset c1) sub1).
    by rewrite ev_c1 pbind_resE hide_pbindr // restrE0 => ->.
  have := @eval_com_blocks _ s1 c1 k dis.
  rewrite ev_c1 pbind_resE.
  have: fdisjoint (names (domm s2.2)) A.
    by apply: fdisjoint_trans dis2; eapply nom_finsuppP; finsupp.
  move: (names (domm s2.2)) => A' dis2'.
  by rewrite pbindrE // namesfsnE.
  - rewrite -andbA=> /and3P [sub_e sub_c1 sub_c2] dis_h1h2.
  rewrite eval_expr_unionm //; case: eval_expr=> //= b ev_if.
  by rewrite (IH _ _ rs) //; case: (b).
case/andP=> [sub_e sub_c] dis_h1h2.
rewrite eval_expr_unionm //; case: eval_expr=> //= b ev_if.
rewrite (IH _ _ rs) //; case: (b)=> //=; rewrite ?fsub0set //.
by rewrite !fsubUset sub_c sub_e.
Qed.


Lemma frame_loop c s1 s2 k :
  fsubset (vars_c c) (domm s1.1) ->
  fdisjoint (names (domm s1.2)) (names (domm s2.2)) ->
  eval_com c s1 k = NotYet ->
  eval_com c (s1 ∪ s2) k = NotYet.
Proof.
elim: k c s1 => [|k IH] //= c s1.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=;
rewrite ?fsubUset ?fsub1set.
- by case: eval_expr=> //= p; case: getm.
- by case: eval_expr=> //= p; case: updm.
- by case: eval_expr=> [|[n|]| |].
- by case: eval_expr=> //= p; do 2![case: ifP=> //= _].
- case/andP=> [c1_ls1 c2_ls2] dis_h1_h2.
  case ev_c1: eval_com=> [rs'| |] //=; last by rewrite IH.
  case/(restrP (names s1 :|: names s2)): rs' ev_c1
    => /= A s1' disA subA ev_c1.
  move: disA; rewrite fdisjointUl=> /andP [disA1 disA2].
  rewrite bindrE ?fdisjoint0s // (frame_ok _ _ ev_c1) //.
  rewrite maprE //= ?bindrE ?fdisjoint0s //.
  case ev_c2: eval_com=> //= _; rewrite IH //.
    have:= @eval_com_vars _ _ k (fsubset_trans (mod_vars_c_subset c1) c1_ls1).
    by rewrite ev_c1 pbind_resE hide_pbindr // restrE0 => ->.
    have := @eval_com_blocks _ s1 c1 k dis_h1_h2.
    rewrite ev_c1 pbind_resE.
    have: fdisjoint (names (domm s2.2)) A.
    by apply: fdisjoint_trans disA2; eapply nom_finsuppP; finsupp.
  move: (names (domm s2.2)) => A' disA2'.
  by rewrite pbindrE // namesfsnE.
- rewrite -andbA => /and3P [e_ls1 c1_ls1 c2_ls2] dis_h1_h2.
  rewrite eval_expr_unionm //=; case: eval_expr=> //= b ev_if.
  by rewrite IH //; case: (b).
case/andP=> [e_ls1 c_ls1] dis_h1_h2; rewrite eval_expr_unionm //.
case: eval_expr=> //= b ev_while.
by rewrite IH //; case: (b)=> //=; rewrite ?fsub0set // !fsubUset e_ls1 c_ls1.
Qed.

Lemma get_mem_dis e s1 h2 p sz :
  fdisjoint (names s1) (names (domm h2)) ->
  eval_expr true e s1.1 = VPtr p sz ->
  h2 p = None.
Proof.
move=> dis eval_e; case get_p: (h2 p)=> [v|] //.
move: (eval_expr_names true s1.1 e); rewrite eval_e namesvE.
have inNh2: p.1 \in names (domm h2).
  apply/namesfsP; exists p; first by rewrite mem_domm get_p.
  by apply/fsetUP; left; apply/namesnP.
rewrite fsub1set=> inNls1.
have inNs1: p.1 \in names s1 by rewrite in_fsetU inNls1.
by move/fdisjointP/(_ _ inNs1): dis; rewrite inNh2.
Qed.

Lemma frame_error c s1 s2 k err:
  fsubset (vars_c c) (domm s1.1) ->
  fdisjoint (names s1) (names (domm s2.2)) ->
  eval_com c s1 k = Error err ->
  eval_com c (s1 ∪ s2) k = Error err.
Proof.
elim: k c s1 err => [|k IH] //= c s1 err.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=;
rewrite ?fsubUset ?fsub1set.
- case/andP=> [x_ls1 e_ls1] dis_s1_h2.
  rewrite eval_expr_unionm //; case ev_e: eval_expr=> [| |p|] //=.
  by rewrite unionmE (get_mem_dis dis_s1_h2 ev_e); case: getm.
- case/andP=> [e_ls1 e'_ls1] dis_s1_h2.
  rewrite eval_expr_unionm //; case ev_e: eval_expr=> [| |p|] //=.
  rewrite /updm unionmE (get_mem_dis dis_s1_h2 ev_e).
  by case: getm.
- case/andP=> [x_ls1 e_ls1] dis_s1_h2.
  by rewrite eval_expr_unionm //; case ev_e: eval_expr=> [|[n|]| |] //=.
- move=> e_ls1 dis_s1_h2.
  rewrite eval_expr_unionm //; case ev_e: eval_expr=> [| |p|] //=.
  case: ifP=> //= _; rewrite !domm_curry domm_union imfsetU in_fsetU.
  case: ifP=> //=; intros.
  case: ifP => //= /imfsetP /= [p' in_h2 e_p].
  move: (eval_expr_names true s1.1 e); rewrite ev_e namesvE fsub1set.
  move=> in_ls1; have in_Nh2 : p'.1 \in names (domm s2.2).
    apply/namesfsP; exists p'=> //.
    by rewrite in_fsetU namesnE in_fset1 eqxx.
  move: dis_s1_h2; rewrite fdisjointC=> /fdisjointP/(_ _ in_Nh2).
  by rewrite in_fsetU /= -e_p in_ls1.
- case/andP=> [c1_ls1 c2_ls2] dis_s1_h2.
  case ev_c1: eval_com=> [rs'| error1|] //=.
  + rewrite (@frame_ok _ _ _ _ rs') //.
      * case/(restrP (names s1 :|: names s2)): rs' ev_c1=> /= A s1' dis' sub.
        move: dis'; rewrite fdisjointUl=> /andP [dis_s1_A dis_s2_A].
        rewrite maprE ?bindrE ?fdisjoint0s //= => ev_c1.
        case ev_c2: eval_com=> //=.
        case.
        intro. Locate hide.
        rewrite (IH c2 s1' err).
        reflexivity.
        have:= @eval_com_vars _ _ k (fsubset_trans (mod_vars_c_subset c1) c1_ls1).
        by rewrite ev_c1 pbind_resE hide_pbindr // restrE0 => ->.
        have: fsubset (names (eval_com c1 s1 k)) (names s1).
        by eapply nom_finsuppP; finsupp.
        rewrite ev_c1 namesresE names_hider namesrE fsubDset => sub_s1'.
        apply: fdisjoint_trans; first by eauto.
        rewrite fdisjointUl dis_s1_h2 andbT fdisjointC.
        apply: fdisjoint_trans; last by exact: dis_s2_A.
        by eapply nom_finsuppP; finsupp.
        rewrite <- H.
        assumption.
        apply: fdisjoint_trans; last by exact: dis_s1_h2.
        by rewrite namespE /=; eapply nom_finsuppP; finsupp.
        intro.
        unfold bind_res.
        assert (eval_com c1 (s1 ∪ s2) k = Error err).
        rewrite (IH c1 s1 err).
        reflexivity.
        assumption.
        assumption.
        rewrite ev_c1.
        assumption.
        rewrite H0.
        reflexivity.
- case/andP=> [/andP [e_ls1 c1_ls1] c2_ls2] dis_s1_h2.
  rewrite eval_expr_unionm //; case: eval_expr=> //= b ev_if.
  rewrite (IH (if b then c1 else c2) s1 err) //.
  by case: (b).
- case/andP=> [e_ls1 c_ls1] dis_s1_h2.
  rewrite eval_expr_unionm //; case: eval_expr=> //= b ev_if.
  by rewrite (IH (if b then Seq c (While e c) else Skip) s1 err) // !fun_if if_arg /= !fsubUset c_ls1 e_ls1 fsub0set if_same.
Qed.

Corollary noninterference s1 s21 rs' s22 c k :
  fsubset (vars_c c) (domm s1.1) ->
  fdisjoint (names s1) (names (domm s21.2)) ->
  fdisjoint (names (domm s1.2)) (names (domm s22.2)) ->
  eval_com c (s1 ∪ s21) k = Done rs' ->
  exists rs1',
    [/\ eval_com c s1 k = Done rs1',
        rs' = mapr (names s21) (stateu ^~ s21) rs1' &
        eval_com c (s1 ∪ s22) k =
        Done (mapr (names s22) (stateu ^~ s22) rs1')].
Proof.
move=> sub dis1 dis2 eval_c.
case eval_c': (eval_com c s1 k) => [rs1'| |] //=.
- exists rs1'; split; eauto.
    move: eval_c; rewrite (frame_ok sub _ eval_c') => [[<-]//|] /=.
    apply/(fdisjoint_trans _ dis1); eapply nom_finsuppP; finsupp.
  by apply: frame_ok=> //.
- by rewrite (frame_error sub dis1 eval_c') in eval_c.
rewrite (frame_loop sub _ eval_c') // in eval_c.
apply/(fdisjoint_trans _ dis1); eapply nom_finsuppP; finsupp.
Qed.


Lemma mod_vars_cP s rs' c x k :
  eval_com c s k = Done rs' ->
  x \notin mod_vars_c c ->
  mapr fset0 (fun s => s.1 x) rs' = Restr (s.1 x).
Proof.
elim: k s c rs' => /= [|k IH] s c rs' //.
case: c => [x' e|x' e|e e'|x' e|e| |c1 c2|e c1 c2|e c] //=;
rewrite ?in_fset1.
- by move=> [<-]; rewrite maprE0 //= setmE => /negbTE ->.
- case: eval_expr=> //= p sz; case: getm=> //= v [<-].
  by rewrite maprE0 //= setmE => /negbTE ->.
- case: eval_expr=> //= p sz; case: updm=> //= h' [<-].
  by rewrite maprE0 //= setmE.
- case: eval_expr=> [|[n|]| |] //= [<-].
  rewrite /new; move: (fresh _) (freshP (names s)) => i nin_i.
  rewrite !maprE ?fdisjoint0s //= setmE => /negbTE ->.
  rewrite hideD // namesrE fdisjointC; apply: (@fdisjoint_trans _ _ (names s)).
    eapply nom_finsuppP; finsupp.
  by rewrite fdisjoints1.
- case: eval_expr=> // p sz; case: ifP => // _; case: ifP=> // _ [<-].
  by rewrite maprE0.
- by move=> [<-] _; rewrite maprE0.
- case ev1: eval_com=> [rs''| |] //=.
  case/(restrP fset0): rs'' ev1 => /= A s'' _ sub ev1.
  rewrite bindrE ?fdisjoint0s //.
  case ev2: eval_com=> [rs''| |] // [<-] {rs'}.
  rewrite in_fsetU => /norP [nin1 nin2].
  rewrite -hide_mapr ?fdisjoint0s // (IH _ _ _ ev2 nin2).
  by rewrite -(IH _ _ _ ev1 nin1) maprE ?fdisjoint0s.
- rewrite in_fsetU; case: eval_expr=> // b ev /norP [nin1 nin2].
  by apply: IH; eauto; case: (b).
- case: eval_expr=> // b ev nin.
  apply: IH; eauto.
  by case: (b); rewrite ?in_fset0 //= fsetUid.
Qed.

(******* Extension_lemmas. ******)

(*Weaken the assumption about names*)
Lemma frame_mem_safe_error c s1 s2 k err:
  fsubset (vars_c c) (domm s1.1) ->
  fdisjoint (names (domm s1.2)) (names (domm s2.2)) ->
  eval_com c s1 k = Error err ->
  err \notin mem_safety_errors ->
  eval_com c (s1 ∪ s2) k = Error err.
Proof. 
elim: k c s1 err => [|k IH] //= c s1 err.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=;
rewrite ?fsubUset ?fsub1set.
- case/andP=> [x_ls1 e_ls1] dis_s1_h2 . 
  rewrite eval_expr_unionm //; case ev_e: eval_expr=> [| |p|] //=.
  case cp : (s1.2 p).
  move => H; discriminate H.
  move => H.
  move/negP.
  injection H.
  move => H1 H2.
  rewrite <- H1 in H2.
  have H3 : OutofBoundsRead \in mem_safety_errors.
    unfold mem_safety_errors.
    apply in_cons.
  by contradiction. 
- case/andP=> [e_ls1 e'_ls1] dis_s1_h2.
  rewrite eval_expr_unionm //; case ev_e: eval_expr=> [| |p|] //=.
  case updmc : (updm s1.2 p (eval_expr true e' s1.1)).
  move => H; discriminate H.
  move => H.
  move/negP.
  injection H.
  move => H1 H2.
  rewrite <- H1 in H2.
  have H3 : OutofBoundsWrite \in mem_safety_errors.
    unfold mem_safety_errors.
    apply in_cons.
  by contradiction. 
- case/andP=> [x_ls1 e_ls1] dis_s1_h2.
  by rewrite eval_expr_unionm //; case ev_e: eval_expr=> [|[n|]| |] //=.
- move=> e_ls1 dis_s1_h2.
  rewrite eval_expr_unionm //; case ev_e: eval_expr=> [| |p|] //=.
  case: ifP=> //= _; rewrite !domm_curry domm_union imfsetU in_fsetU.
  case: ifP=> //=.
  move => H0 H1.
  move/negP.
  move => H2. 
  injection H1.
  move => err_eq_obf.
  rewrite <- err_eq_obf in H2.
  have H3 : OutofBoundsFree \in mem_safety_errors.
    unfold mem_safety_errors.
    apply in_cons.
  by contradiction.
- case/andP=> [c1_ls1 c2_ls2] dis_s1_h2.
  case ev_c1: eval_com=> [rs'| error1|] //=.
  + rewrite (@frame_ok _ _ _ _ rs') //.
    case/(restrP (names s1 :|: names s2)): rs' ev_c1=> /= A s1' dis' sub.
    move: dis'; rewrite fdisjointUl=> /andP [dis_s1_A dis_s2_A].
    rewrite maprE ?bindrE ?fdisjoint0s //= => ev_c1.
    case ev_c2: eval_com=> [rs''| err2 |] //=.
    case.
    move => H err_not_mem_safe.
    rewrite (IH c2 s1' err2).
      * rewrite H.
        reflexivity.
      * have:= @eval_com_vars _ _ k 
          (fsubset_trans (mod_vars_c_subset c1) c1_ls1).
          by rewrite ev_c1 pbind_resE hide_pbindr // restrE0 => ->.
      * have: pbind_res (names (names (domm s2.2)))
                  (fun s' => fdisjoint (names (domm s'.2)) (names (domm s2.2)))
                  (eval_com c1 s1 k).
          apply eval_com_blocks.
          exact dis_s1_h2.
        rewrite ev_c1.
        rewrite pbind_resE. (*There should be a shorter way to rewrite pbindrE *)
        have : fdisjoint (names (names (domm s2.2))) A.
          rewrite names_names_eq.
          apply: fdisjoint_trans; last by exact: dis_s2_A.
          rewrite namespE.
          apply fsubsetU.
          apply /orP.
          right.
          rewrite namesmE.
          apply fsubsetU.
          apply /orP.
          left.
          apply fsubsetxx.
        move => H2 H3.
        have : (pbindr (names (names (domm s2.2)))
        (fun s' : locals * heap =>
         fdisjoint (names (domm s'.2)) (names (domm s2.2)))
        (hide A (Restr s1'))) <-> ( (fun s' : locals * heap => fdisjoint (names (domm s'.2)) (names (domm s2.2)))
        (s1')).
          eapply pbindrE. 
          apply (@finsupp_fsetD (names (domm s2.2))).
          exact H2. 
        move => H4.
        apply H4 in H3.
        exact H3.
      * exact ev_c2.
      * rewrite H.
        exact err_not_mem_safe.
    + move => H H1.    
        unfold bind_res.
        assert (eval_com c1 (s1 ∪ s2) k = Error err).
        rewrite (IH c1 s1 err).
        reflexivity.
        assumption.
        assumption.
        rewrite ev_c1.
        assumption.
        assumption.
        rewrite H0.
        reflexivity.
- case/andP=> [/andP [e_ls1 c1_ls1] c2_ls2] dis_s1_h2.
  rewrite eval_expr_unionm //; case: eval_expr=> //= b ev_if.
  move => H.
  rewrite (IH (if b then c1 else c2) s1 err) //.
  by case: (b).
- case/andP=> [e_ls1 c_ls1] dis_s1_h2.
  rewrite eval_expr_unionm //; case: eval_expr=> //= b ev_if.
  move => H.
  by rewrite (IH (if b then Seq c (While e c) else Skip) s1 err) // !fun_if if_arg /= !fsubUset c_ls1 e_ls1 fsub0set if_same.
Qed.


Lemma evalc_disj: 
forall (c : com) s1 k (dommh2 : {fset ptr}) (s1' : {restr locals * heap}),
  fdisjoint (names (domm s1.2)) (names dommh2)
  -> eval_com c s1 k = Done s1' 
  -> (pbind_res (names (names dommh2))
                   (fun st => fdisjoint (names (domm st.2)) (names dommh2))
                   (Done s1')).
Proof.
move => c s1 k dommh2 s1' heaps_disjoint eval_com_c_s.
rewrite <- eval_com_c_s.
apply eval_com_blocks.
exact heaps_disjoint.
Qed.

Lemma domm_setm_eq h k v : k \in domm h -> domm (setm h k v) = domm h.
Proof.
move => k_in_domm.
rewrite domm_set.
apply /fsetUidPr.
rewrite fsub1set.
exact k_in_domm.
Qed.


End Structured.
