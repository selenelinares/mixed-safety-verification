Require Import Coq.Strings.String.

From Coq Require Import Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssrnum ssrint seq.
From mathcomp Require Import eqtype choice seq order. 
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun fperm.

From CoqUtils Require Import nominal.

From memsafe Require Import syntax semantics nominal_extension frame_conds_def
  separation_logic_def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Nominal_proj.

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

(*
Variable nT : nominalType.

Global Instance Done_eqvar : {eqvar @Done nT}.
Proof. by move=> s x _ <-. Qed.
*)

Section Fset_extension_lemmas.

Lemma intersection_mem_equiv {T : ordType} (A B C : {fset T}) x :
(x \in C -> (x \in A) = (x \in B))
-> (x \in A :&: C) = (x \in B :&: C).
Proof.
move => H. 
rewrite in_fsetI.
rewrite in_fsetI.
case c_c : (x \in C).
- rewrite andbT andbT.
  apply (H c_c).
- rewrite andbF andbF.
  reflexivity.
Qed.

End Fset_extension_lemmas.


Lemma renameresE pm {nT: nominalType} (r : result nT) :
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

Lemma namesresE {nT: nominalType}(r : result nT) :
  names r = if r is Done x then names x else fset0.
Proof.  
    case: r; simpl.
    reflexivity.
    (case; simpl; reflexivity).
    reflexivity.
Qed. 

(* lang_properties needed lemmas *)

(*frame_conditions needed lemmas*)
Lemma names_ptr_eq (p : ptr) :
  names p = fset1 p.1.
Proof.
rewrite namespE.
rewrite namesnE.
rewrite namesT.
rewrite fset1E.
rewrite fsetU0.
reflexivity.
Qed.

Lemma ptr_namesin_in (p : ptr) (A : {fset ptr}) :
  p \in A -> p.1 \in names A.
Proof.
move => H.
specialize (namesin_subset H).
rewrite names_ptr_eq.
rewrite fsub1set.
auto.
Qed.

Lemma names_subset_or_disjointP {T : nominalType} (x : T) (A : {fset name}):
  names x != fset0
  -> fsubset (names x) A \/ fdisjoint (names x) A
  -> reflect (names x :&: A != fset0) (fsubset (names x) A).
Proof.
move => H H1.
apply /(iffP idP).
- move => fsubsetxA.
  move /fset0Pn in H.
  apply /fset0Pn.
  destruct H as [x0 H].
  exists x0.
  move /fsetIidPl in fsubsetxA.
  rewrite fsubsetxA.
  exact H.
- move => H2.
  destruct H1 as [fsubsetxA | fdsjntxA].
  + exact fsubsetxA.
  + unfold fdisjoint in fdsjntxA.
    move /eqP in fdsjntxA.
    rewrite fdsjntxA in H2.
    auto.
Qed.

Lemma pointers_all_in_or_all_out (A : {fset name}) (D : {fset ptr}):
  forall x, x \in D -> fsubset (names x) A \/ fdisjoint (names x) A.
Proof.
move => x x_in_D.
rewrite names_ptr_eq.
rewrite fsub1set.
case H2: (x.1 \in A).
by left.
right.
apply /fdisjointP.
move => y y_is_x1.
rewrite in_fset1 in y_is_x1.
move /eqP in y_is_x1.
rewrite y_is_x1.
rewrite H2.
auto.
Qed.

(*Rename*)
Lemma rename_exchange_inv {T : nominalType}
  (pi : {fperm name}) (x y : T) :
  x = rename pi y <-> rename (pi^-1)%fperm x = y.
Proof.
split.
- move => x_rename_y.
  rewrite x_rename_y.
  rewrite renameK.
  reflexivity.
- move => rename_x_y.
  rewrite <- rename_x_y.
  rewrite renameKV.
  reflexivity.
Qed.

Lemma rename_exchange_inv2 {T : nominalType}
  (pi : {fperm name}) (x y : T) :
  rename pi y = x <-> y = rename (pi^-1)%fperm x.
Proof.
split.
- move => H.
  apply Logic.eq_sym.
  rewrite <- rename_exchange_inv.
  rewrite H; reflexivity.
- move => H.
  apply Logic.eq_sym.
  rewrite rename_exchange_inv.
  rewrite H; reflexivity.
Qed.

Lemma name_invariant_rename_eq
  {T : nominalType}
  (N : {fset name}) (pi : {fperm name}) (x : T) :
  finsupp_perm N pi ->
  fsubset (names x) N ->
  rename pi x = x.
Proof.
move => permNpi fsubxN.
have H := (fsubset_finsupp_perm permNpi fsubxN).
apply renameJ.
exact H.
Qed.

Lemma finsupp_perm_notin_preserv {T : nominalType} (A: {fset T}) x pi: 
  finsupp_perm (names A) pi -> 
  x \notin A ->
  rename pi x \notin A.
Proof. 
move => finsupperm x_notin_A.
apply /negP.
move /negP in x_notin_A.
move => pi_x_in_A.
rewrite <- (renameK pi x)  in x_notin_A.
rewrite renameJ in x_notin_A.
- contradiction.
- rewrite fdisjointC.
  rewrite supp_inv.
  unfold finsupp_perm in finsupperm.
  rewrite fdisjointC in finsupperm.
  apply (fun p => fdisjoint_trans p finsupperm).
  apply namesin_subset.
  exact pi_x_in_A.
Qed.
(*finsupp_perm*)

Lemma finsupp_perm_inv (N : {fset name}) (pi : {fperm name}) :
  finsupp_perm N pi -> finsupp_perm N ((pi^-1)%fperm).
Proof.
unfold finsupp_perm.
rewrite supp_inv.
auto.
Qed.

Lemma name_invariant_invpi_eq (pi : {fperm name}) x A :
  finsupp_perm A pi ->
  pi x \in A ->
  pi x = x.
Proof.
move => finsupp_perm_Api pi_x_in_A.
apply finsupp_perm_inv in finsupp_perm_Api.
have H := (@name_invariant_rename_eq _ _ _ (pi x) finsupp_perm_Api).
rewrite namesnE in H.
rewrite fsub1set in H.
specialize (H pi_x_in_A).
rewrite renameK in H.
rewrite <- H.
reflexivity.
Qed.


(*Finsupp lemmas*)

Lemma finsupp_fun_simple
  {S T : nominalType} (A : {fset name}) (f : S -> T) :
  (forall x, {finsupp A (f x)}) ->
  (forall pi, forall x y:S,
    finsupp_perm A pi -> nomR pi x y -> f x = f y) ->
  {finsupp A f}.
Proof.
move => finsupp_res f_pi_arg_eq pi finsuppperm y z nomRyz.
specialize (fun x => finsupp_res x pi finsuppperm).
specialize (f_pi_arg_eq _ _ _ finsuppperm nomRyz).
rewrite f_pi_arg_eq.
apply finsupp_res.
Qed.


Lemma finsupp_perm_name_in_renamed_names {T : nominalType}
  (pi : {fperm name}) (A : {fset name}) (D : T) a :
  finsupp_perm A pi ->
  a \in A ->
  (a \in names D) =
  (a \in names (rename pi D)).
Proof.
move => permApi a_in_A.
rewrite names_rename.
have H := (namesin_subset a_in_A).
rewrite namesfsnE in H.
apply bool_ext.
- move => a_in_namesD.
  apply (mem_imfset pi) in a_in_namesD.
  rewrite <- renamenE in a_in_namesD.
  rewrite (name_invariant_rename_eq permApi H) in a_in_namesD.
  exact a_in_namesD.
- move => a_in_imD.
  move /imfsetP in a_in_imD.
  destruct a_in_imD as [x H0 H1].
  rewrite H1 in a_in_A.
  have H2 := (name_invariant_invpi_eq permApi a_in_A).
  rewrite H1 H2.
  exact H0.
Qed.

Lemma finsupp_fsetD (A : {fset name}) : 
{finsupp (names A)
  fun s : locals * heap => (fdisjoint (names (domm s.2)) A : Prop)}.
Proof.
move => pi permApi x y nomRxy.
rewrite <- nomRxy.
rewrite domm_rename.
unfold fdisjoint.
rewrite namesfsnE in permApi.
have H: names (domm x.2) :&: A = names (rename pi (domm x.2)) :&: A.
- apply /eq_fset.
  move => a.
  apply intersection_mem_equiv.
  move => a_in_A.
  apply (finsupp_perm_name_in_renamed_names _ permApi a_in_A).
rewrite H.
split; auto.
Qed.

Lemma finsupp_fsetD_bool (A : {fset name}) : 
{finsupp (names A)
  fun s : locals * heap => (fdisjoint (names (domm s.2)) A)}.
Proof.
move => pi permApi x y nomRxy.
rewrite <- nomRxy.
rewrite domm_rename.
unfold fdisjoint.
rewrite namesfsnE in permApi.
have H: names (domm x.2) :&: A = names (rename pi (domm x.2)) :&: A.
- apply /eq_fset.
  move => a.
  apply intersection_mem_equiv.
  move => a_in_A.
  apply (finsupp_perm_name_in_renamed_names _ permApi a_in_A).
rewrite H.
apply nomR_nominalJ.
apply finsupp_permT.
Qed.

Lemma finsupp_fsetIl_heapdomm (* {T : nominalType} *)
  (A : {fset ptr}) (f : {fset ptr} -> Prop) :
  {finsupp (names A) fun s : state => f (A :&: domm s.2)}.
Proof.
move => pi permApi x y nomRxy.
rewrite <- nomRxy.
rewrite domm_rename.
assert (H1 : A :&: rename pi (domm x.2) = (A :&: domm x.2)).
- apply /eq_fset.
  move => a.
  rewrite <- (@name_invariant_rename_eq _ (names A) pi A).
  + rewrite <- (@rename_fsetI_distrib _ A).
    rewrite name_invariant_rename_eq.
    * rewrite name_invariant_rename_eq.
      ** reflexivity.
      ** apply fsubsetxx.
    * eapply fsubset_trans.
      apply namesfsI.
      apply fsubsetIl.
  + exact permApi.
  + apply fsubsetxx.
rewrite H1.
apply Prop_finsupp.
finsupp.
Qed.


(* Lemma finsupp_fsetIl_heapdomm_simplified (* {T : nominalType} *)
  (A : {fset ptr}) (f : {fset ptr} -> Prop) :
  {finsupp (names A) fun s : state => f (A :&: domm s.2)}.
Proof.
move => pi permApi x y nomRxy.
rewrite <- nomRxy.
rewrite domm_rename.
assert (H1 : A :&: rename pi (domm x.2) = (A :&: domm x.2)).
- apply /eq_fset.
  move => a.
  rewrite <- (@name_invariant_rename_eq _ (names A) pi A).
  + rewrite <- (@rename_fsetI_distrib _ A).
    rewrite renameJ.
    * rewrite renameJ.
      ** reflexivity.
      ** apply permApi.
    * unfold finsupp_perm in permApi.
      rewrite fdisjointC in permApi.
      rewrite fdisjointC.
      apply (@fdisjoint_trans _ _ (names A)).
      rewrite names_disj
      apply namesfsI.
      apply fsubsetIl.
  + exact permApi.
  + apply fsubsetxx.
rewrite H1.
apply Prop_finsupp.
finsupp.
Qed. *)

Lemma rename_distr_unionm {T S: nominalType} pi (m1 m2 : {fmap T -> S}):
  (rename pi (unionm m1 m2)) = (unionm (rename pi m1) (rename pi m2)).
Proof.
apply unionm_eqvar.
finsupp.
finsupp.
Qed. 

Lemma finsupp_stateur s: 
  {finsupp (names s) stateu^~ s}.
Proof.
unfold stateu.
move => pi H x y nomRxy.
rewrite <- nomRxy.
unfold nomR.
unfold nominalType_nominalRel.
unfold finsupp_perm in H.
rewrite (surjective_pairing s) in H.
rewrite namespE in H.
rewrite fdisjointUr in H.
case /andP : H => pi_disj_store pi_disj_heap.
replace (rename pi (unionm x.1 s.1, unionm x.2 s.2)) with 
  (rename pi (unionm x.1 s.1), rename pi (unionm x.2 s.2)).
- rewrite rename_distr_unionm rename_distr_unionm.
  rewrite (@renameJ _ pi s.1).
  rewrite (@renameJ _ pi s.2).
  reflexivity.
  exact pi_disj_heap.
  exact pi_disj_store.
- reflexivity.
Qed.

Lemma finsupp_domm_fst_eq {T S U: nominalType} (A : {fset T}) :
  {finsupp (names A) fun s'0 : {fmap T -> S} * U => domm s'0.1 = A}.
Proof.
move => pi finsupp_perm x y nomRxy.
rewrite <- nomRxy.
rewrite domm_rename.
assert (Hy := iff_sym (rename_exchange_inv2 pi A (domm x.1))).
apply (fun Hx => iff_trans (A := (domm x.1 = A)) Hx Hy).
apply finsupp_perm_inv in finsupp_perm.
rewrite (nomR_nominalJ finsupp_perm).
apply iff_refl.
Qed.


Lemma finsupp_domm_ls_eq (A : {fset string_nominalType}) :
  {finsupp (names A) fun s'0 : state => domm s'0.1 = A}.
apply (@finsupp_domm_fst_eq string_nominalType value_nominalType _ A).
Qed.

Lemma finsupp_conj {T : nominalType} AP AQ (P Q : T -> Prop) : 
  {finsupp AP P}
  -> {finsupp AQ Q}
  -> {finsupp (AP :|: AQ) fun x => P x /\ Q x}.
Proof.
move => finsuppP finsuppQ pi finsupp_perm x y nomRxy.
apply finsupp_perm_union in finsupp_perm.
destruct finsupp_perm as [fpAP fpAQ].
specialize (finsuppP pi fpAP _ _ nomRxy).
specialize (finsuppQ pi fpAQ _ _ nomRxy).
rewrite <- nomRxy in finsuppP.
rewrite <- nomRxy in finsuppQ.
split.
- move => PQx.
  destruct PQx as [Px Qx].
  rewrite <- nomRxy.
  split.
  + apply finsuppP; exact Px.
  + apply finsuppQ; exact Qx.
- move => PQy.
  destruct PQy as [Py Qy].
  rewrite <- nomRxy in Py, Qy.
  split.
  + apply finsuppP; exact Py.
  + apply finsuppQ; exact Qy.
Qed.



Lemma finsupp_eval_eq_bool_conj_prop b AP e P : 
  {finsupp AP P}
  -> {finsupp AP fun s1 : state =>
                 eval_expr true e s1.1 = VBool b /\ P s1}.
Proof.
move => finsuppAP.
rewrite <- (fset0U AP).
apply finsupp_conj.
- assert (H := finsupp_app
    (HT := @nominalType_nominalRel
            (prod_nominalType
              (fmap_nominalType string_nominalType value_nominalType)
              (fmap_nominalType ptr_nominalType value_nominalType)))
    (HS := @nominalType_nominalRel value_nominalType)
    (HR := Prop_nominalRel)
    (f := fun x gx => gx = VBool b)
    (Af := fset0)
    (g := fun x => eval_expr true e x.1)
    (Ag := fset0)).
  rewrite fset0U in H.
  apply H.
  + move => pi finsupp_perm_0pi sx sy nomRsxsy.
    move => x y nomRxy.
    rewrite <- nomRxy.
    assert (Hy := iff_sym (rename_exchange_inv2 pi (VBool b) x)).
    apply (fun Hx => iff_trans (A := (x = VBool b)) Hx Hy).
    apply finsupp_perm_inv in finsupp_perm_0pi.
    assert (names_vfalse : names (VBool b) = fset0).
    * rewrite namesvE.
      reflexivity.
    rewrite <- names_vfalse in finsupp_perm_0pi.
    rewrite (nomR_nominalJ finsupp_perm_0pi).
    apply iff_refl.
  + finsupp.
- exact finsuppAP.
Qed.


End Nominal_proj.