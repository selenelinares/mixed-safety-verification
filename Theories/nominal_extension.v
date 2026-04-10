Require Import Coq.Strings.String.

From Coq Require Import Program.Equality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssrnum ssrint seq.
From mathcomp Require Import eqtype choice seq order. 
From deriving Require Import deriving.
From extructures Require Import ord fset fmap ffun fperm.

From CoqUtils Require Import nominal.

From memsafe Require Import syntax semantics. (*We shouldn't need this*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Nominal.

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


              
Section Logic_utils.

Lemma bool_ext (A B : bool) :
  (A -> B) -> (B -> A) -> A = B.
Proof.
unfold is_true.
move => AB BA.
case_eq A => [ttA|ffA].
- rewrite AB.
  reflexivity.
  exact ttA.
- case_eq B => [ttB|ffB].
  + specialize (BA ttB).
    rewrite BA in ffA.
    discriminate ffA.
  + reflexivity.
Qed.

Lemma contrapos (A B : Prop) :
  (A -> B) -> ~ B -> ~ A.
Proof.
move => ab nb a.
apply (nb (ab a)).
Qed.


Lemma reflect_is_true_eq (P : Prop) (p : bool) :
  reflect P p -> is_true p <-> P.
Proof.
move => H.
split.
- move /H; auto.
- move /H; auto.
Qed.

End Logic_utils.


Lemma f_in_fs_shunt {S T : ordType} {f : S -> T} {g : T -> S}
  (A : {fset T})  (x : S) :
  cancel g f ->
  cancel f g ->
  (f x \in A) = (x \in g @: A).
Proof.
move => gf_cancel fg_cancel.
apply bool_ext.
- move => fx_in_A.
  rewrite <- fg_cancel.
  apply mem_imfset.
  exact fx_in_A.
- move => x_in_imA.
  move /imfsetP in x_in_imA.
  destruct x_in_imA as [y y_inA x_eq_gy].
  rewrite x_eq_gy.
  rewrite gf_cancel.
  exact y_inA.
Qed.


Lemma names_someE {T : nominalType} (v : T) : 
  names (Some v) = names v.
Proof. by []. 
Qed.

Lemma names_names_eq {T: nominalType}: 
forall n : {fset T}, names (names n) = names n.
Proof.
intro.
rewrite namesfsnE; reflexivity.
Qed.

Lemma names_fset1_eq {T : nominalType} (x : T) :
  names (fset1 x) = names x.
Proof.
rewrite fset1E.
rewrite names_fset.
rewrite namess1.
have names_seq0 : names [::] = fset0.
  move => t.  
  rewrite namessE.
  simpl.
  reflexivity.
rewrite names_seq0.
apply fsetU0.
Qed.

Lemma namesin_subset {T : nominalType} (x : T) (A : {fset T}):
  x \in A -> fsubset (names x) (names A).
move => H.
rewrite <- fsub1set in H.
apply namesfs_subset in H.
rewrite names_fset1_eq in H.
exact H.
Qed.

Lemma namesfsI {T : nominalType} (A B : {fset T}):
  fsubset (names (A :&: B)) (names A :&: names B).
Proof.
  apply /fsubsetP.
  move => x x_in_nAB.
  move /namesfsP in x_in_nAB.
  destruct x_in_nAB as [y y_in_AB x_in_ny].
  move /fsetIP in y_in_AB.
  destruct y_in_AB as [y_inA y_inB].
  apply /fsetIP.
  split.
  - apply /namesfsP.
    exists y.
    exact y_inA.
    exact x_in_ny.
  - apply /namesfsP.
    exists y.
    exact y_inB.
    exact x_in_ny.
Qed.

(*Rename*)


Lemma rename_fsetI_distrib
  {T : nominalType} (A B : {fset T}) pi :
  rename pi (A :&: B) = rename pi A :&: rename pi B.
Proof.
rewrite fsetI_eqvar.
reflexivity.
(* rewrite renamefsE renamefsE renamefsE.
apply /imfsetI.
move => x y x_in_A x_in_B.
apply rename_inj. *)
Qed.

Lemma isSome_rename_eq {T : nominalType} {pi : {fperm name}} {ox : option T} :
  isSome (rename pi ox) = rename pi (isSome ox).
Proof.
rewrite isSome_eqvar.
reflexivity.
(* rewrite renameoE.
case cox : ox => [x|].
- simpl.
  rewrite renameT.
  reflexivity.
- simpl.
  rewrite renameT.
  reflexivity. *)
Qed.



Lemma domm_rename {T S : nominalType} (m : {fmap T -> S}) pi:
  domm (rename pi m) = rename pi (domm m).
Proof.
rewrite domm_eqvar.
reflexivity.
(* apply /eq_fset=> k'.
rewrite mem_domm.
rewrite renamefsE.
rewrite renamemE.
rewrite isSome_rename_eq.
rewrite <- mem_domm.
rewrite renameT.
have shunt := f_in_fs_shunt _ _ (renameK pi) (renameKV pi).
rewrite shunt.
reflexivity.*)
Qed.

(*finsupp_perm*)
Lemma finsupp_perm_union A B pi:
  finsupp_perm (A :|: B) pi <-> finsupp_perm A pi /\ finsupp_perm B pi.
Proof.
unfold finsupp_perm.
rewrite fdisjointUr.
rewrite (reflect_is_true_eq andP).
reflexivity.
Qed.

Lemma finsupp_perm_unL A B pi:
  finsupp_perm (A :|: B) pi -> finsupp_perm A pi.
Proof.
move => H.
apply finsupp_perm_union in H.
destruct H as [H1 H2].
exact H1.
Qed.

Lemma finsupp_perm_unR A B pi:
  finsupp_perm (A :|: B) pi -> finsupp_perm B pi.
Proof.
move => H.
apply finsupp_perm_union in H.
destruct H as [H1 H2].
exact H2.
Qed.


Section Finsupp_lemmas.
(* forall s f g =>
  nomR s f g = (forall x y, nomR s x y -> nomR s (f x) (g y)). *)

(* x: nominalType => nomR pi x y = (rename pi x = y) *)

Lemma finsupp_app : 
  forall {T S R : Type} {HT : nominalRel T} {HS : nominalRel S} {HR : nominalRel R}
    (f : T -> S -> R) (g : T -> S) {Af : {fset name} } {Ag : {fset name} },
    {finsupp Af f} -> {finsupp Ag g} -> {finsupp (Af :|: Ag) (fun x:T => (f x) (g x))}.
Proof. 
move => T S R HT HS HR f g Af Ag finsuppAf finsuppAg pi finsupp_perm  x y nomRxy.
assert (H1 := fsubset_finsupp_perm finsupp_perm (fsubsetUr Af Ag)).
specialize (finsuppAg pi H1 x y nomRxy).
assert (H := fsubset_finsupp_perm finsupp_perm (fsubsetUl Af Ag)).
specialize (finsuppAf pi H x y nomRxy (g x) (g y) finsuppAg).
exact finsuppAf.
Qed.

Lemma finsupp_const : 
  forall {T S : Type} {HT : nominalRel T} {HS : nominalRel S} {x : S}
   {A : {fset name} },
    {finsupp A x} -> {finsupp A (fun _:T => x)}.
Proof. 
move => T S HT HS x A finsuppAx s finsupp_permAs y z nomRsyz.
specialize (finsuppAx s finsupp_permAs).
exact finsuppAx. 
Qed.

Lemma finsupp_base : 
  forall {T : nominalType} {x : T},
    {finsupp (names x) x}.
Proof. 
intros T x.
apply /nom_finsuppP.
by rewrite fsubsetxx.
Qed. 

Lemma finsupp_subset : 
  forall {T : Type} {HT : nominalRel T} {x : T} {A A' : {fset name} },
  {finsupp A x} -> fsubset A A' -> {finsupp A' x}.
Proof. 
move => T HT x A A' finsuppAx fsubsetAA' pi finsupp_perm.
specialize (finsuppAx pi (fsubset_finsupp_perm finsupp_perm fsubsetAA')).
exact finsuppAx.
Qed.

(*unused lemma*)
Lemma pbindr_conj' A1 A2 P1 P2 rx :
  {finsupp A1 P1} ->
  {finsupp A2 P2} ->
  pbindr A1 P1 rx ->
  pbindr A2 P2 rx ->
  pbindr (A1 :|: A2) (fun x => P1 x /\ P2 x) rx.
Proof.
intros.
unfold pbindr.
intros.
rewrite fdisjointUl in H4.
case /andP : H4 => H4' H4''.
unfold pbindr in H1.
specialize (H1 A' x H3 H4').
unfold pbindr in H2.
specialize (H2 A' x H3 H4'').
auto. 
Qed.

Lemma finsupp_eq_var : 
 forall {T : Type} {H : nominalRel T} {x : T},
  {eqvar x} -> {finsupp fset0 x}.
Proof.
by auto.
Qed.

Arguments finsupp_app {_ _ _ _ _ _ } f g. 

End Finsupp_lemmas.

End Nominal.