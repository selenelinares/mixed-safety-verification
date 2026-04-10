Require Import Coq.Strings.String.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype choice seq ssrnum ssrint ssralg bigop.

From deriving Require Import deriving.
From extructures Require Import ord fset fmap fperm.

From CoqUtils Require Import nominal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Basic.

Local Open Scope fset_scope.

Definition int_ordMixin :=
  @PcanOrdMixin int _ _ _ pickleK.

Canonical int_ordType :=
  Eval hnf in OrdType int int_ordMixin.
Canonical int_nominalType :=
  Eval hnf in [nominalType for int by //].
Canonical int_trivialNominalType :=
  Eval hnf in [trivialNominalType for int].

Inductive binop : Type :=
| Add | Mul | Sub | Eq | Leq | And | Or.

Definition nat_of_binop b :=
  match b with
  | Add => 0
  | Mul => 1
  | Sub => 2
  | Eq  => 3
  | Leq => 4
  | And => 5
  | Or  => 6
  end.

Definition binop_of_nat n :=
  match n with
  | 0 => Add
  | 1 => Mul
  | 2 => Sub
  | 3 => Eq
  | 4 => Leq
  | 5 => And
  | _ => Or
  end.

Lemma nat_of_binopK : cancel nat_of_binop binop_of_nat.
Proof. by case. Qed.

Definition binop_eqMixin := CanEqMixin nat_of_binopK.
Canonical binop_eqType := Eval hnf in EqType binop binop_eqMixin.
Definition binop_choiceMixin := CanChoiceMixin nat_of_binopK.
Canonical binop_choiceType := Eval hnf in ChoiceType binop binop_choiceMixin.
Definition binop_countMixin := CanCountMixin nat_of_binopK.
Canonical binop_countType := Eval hnf in CountType binop binop_countMixin.
Definition binop_ordMixin := CanOrdMixin nat_of_binopK.
Canonical binop_ordType := Eval hnf in OrdType binop binop_ordMixin.

(*FIX ME: it seems ENil isn't used*)
Inductive expr :=
| Var of string
| Bool of bool
| Num of int
| Binop of binop & expr & expr
| Neg of expr
| ENil
| Offset of expr
| Size of expr
| Cast of expr.

Fixpoint tree_of_expr e :=
  match e with
  | Var x => GenTree.Node 0 [:: GenTree.Leaf (pickle x)]
  | Bool b => GenTree.Node 1 [:: GenTree.Leaf (pickle b)]
  | Num n => GenTree.Node 2 [:: GenTree.Leaf (pickle n)]
  | Binop b e1 e2 => GenTree.Node 3 [:: GenTree.Leaf (pickle b);
                                        tree_of_expr e1; tree_of_expr e2]
  | Neg e => GenTree.Node 4 [:: tree_of_expr e]
  | ENil => GenTree.Node 5 [::]
  | Offset e => GenTree.Node 6 [:: tree_of_expr e]
  | Size e => GenTree.Node 7 [:: tree_of_expr e]
  | Cast e => GenTree.Node 8 [:: tree_of_expr e]
  end.

Fixpoint expr_of_tree t :=
  match t with
  | GenTree.Node 0 [:: GenTree.Leaf x & _] => Var (odflt String.EmptyString (unpickle x))
  | GenTree.Node 1 [:: GenTree.Leaf b & _] => Bool (odflt true (unpickle b))
  | GenTree.Node 2 [:: GenTree.Leaf n & _ ] => Num (odflt (0 : int) (unpickle n))
  | GenTree.Node 3 [:: GenTree.Leaf b, e1, e2 & _ ] =>
    Binop (odflt Add (unpickle b)) (expr_of_tree e1) (expr_of_tree e2)
  | GenTree.Node 4 [:: e & _] => Neg (expr_of_tree e)
  | GenTree.Node 5 _ => ENil
  | GenTree.Node 6 [:: e & _] => Offset (expr_of_tree e)
  | GenTree.Node 7 [:: e & _] => Size (expr_of_tree e)
  | GenTree.Node 8 [:: e & _] => Cast (expr_of_tree e)
  | _ => Var String.EmptyString
  end.

Lemma tree_of_exprK : cancel tree_of_expr expr_of_tree.
Proof.
rewrite /expr_of_tree [@unpickle]lock.
by elim=> /= [x|b|n|b e1 -> e2 ->|e -> | |e ->|e ->|e ->] //;
rewrite -lock pickleK.
Qed.

Definition expr_eqMixin := CanEqMixin tree_of_exprK.
Canonical expr_eqType := Eval hnf in EqType expr expr_eqMixin.
Definition expr_choiceMixin := CanChoiceMixin tree_of_exprK.
Canonical expr_choiceType := Eval hnf in ChoiceType expr expr_choiceMixin.
Definition expr_countMixin := CanCountMixin tree_of_exprK.
Canonical expr_countType := Eval hnf in CountType expr expr_countMixin.
Definition expr_ordMixin := PcanOrdMixin (@pickleK expr_countType).
Canonical expr_ordType := Eval hnf in OrdType expr expr_ordMixin.
Canonical expr_nominalType := Eval hnf in [nominalType for expr by //].
Canonical expr_trivialNominalType := Eval hnf in [trivialNominalType for expr].

Inductive com : Type :=
| Assn of string & expr
| Load of string & expr
| Store of expr & expr
| Alloc of string & expr
| Free of expr
| Skip
| Seq of com & com
| If of expr & com & com
| While of expr & com.

Fixpoint tree_of_com c :=
  match c with
  | Assn x e => GenTree.Node 0 [:: GenTree.Leaf (pickle x); GenTree.Leaf (pickle e)]
  | Load x e => GenTree.Node 1 [:: GenTree.Leaf (pickle x); GenTree.Leaf (pickle e)]
  | Store e1 e2 => GenTree.Node 2 [:: GenTree.Leaf (pickle e1); GenTree.Leaf (pickle e2)]
  | Alloc x e => GenTree.Node 3 [:: GenTree.Leaf (pickle x); GenTree.Leaf (pickle e)]
  | Free e => GenTree.Node 4 [:: GenTree.Leaf (pickle e)]
  | Skip => GenTree.Node 5 [::]
  | Seq c1 c2 => GenTree.Node 6 [:: tree_of_com c1; tree_of_com c2]
  | If e c1 c2 => GenTree.Node 7 [:: GenTree.Leaf (pickle e);
                                     tree_of_com c1;
                                     tree_of_com c2]
  | While e c => GenTree.Node 8 [:: GenTree.Leaf (pickle e); tree_of_com c]
  end.

Fixpoint com_of_tree t :=
  let var x := odflt String.EmptyString (unpickle x) in
  let exp e := odflt (Num 0) (unpickle e) in
  match t with
  | GenTree.Node 0 [:: GenTree.Leaf x; GenTree.Leaf e] => Assn (var x) (exp e)
  | GenTree.Node 1 [:: GenTree.Leaf x; GenTree.Leaf e] => Load (var x) (exp e)
  | GenTree.Node 2 [:: GenTree.Leaf e1; GenTree.Leaf e2] => Store (exp e1) (exp e2)
  | GenTree.Node 3 [:: GenTree.Leaf x; GenTree.Leaf e] => Alloc (var x) (exp e)
  | GenTree.Node 4 [:: GenTree.Leaf e] => Free (exp e)
  | GenTree.Node 5 [::] => Skip
  | GenTree.Node 6 [:: c1; c2] => Seq (com_of_tree c1) (com_of_tree c2)
  | GenTree.Node 7 [:: GenTree.Leaf e; c1; c2] => If (exp e) (com_of_tree c1) (com_of_tree c2)
  | GenTree.Node 8 [:: GenTree.Leaf e; c] => While (exp e) (com_of_tree c)
  | _ => Skip
  end.

Lemma tree_of_comK : cancel tree_of_com com_of_tree.
Proof.
elim=> [x e|x e|e1 e2|x e|e| |c1 IH1 c2 IH2|e c1 IH1 c2 IH2|e c IH] //=;
rewrite ?pickleK ?IH ?IH1 ?IH2 //; f_equal;
by apply: Some_inj; rewrite -[RHS]pickleK.
Qed.

Definition com_eqMixin := CanEqMixin tree_of_comK.
Canonical com_eqType := Eval hnf in EqType com com_eqMixin.
Definition com_choiceMixin := CanChoiceMixin tree_of_comK.
Canonical com_choiceType := Eval hnf in ChoiceType com com_choiceMixin.
Definition com_countMixin := CanCountMixin tree_of_comK.
Canonical com_countType := Eval hnf in CountType com com_countMixin.
Definition com_ordMixin := PcanOrdMixin (@pickleK com_countType).
Canonical com_ordType := Eval hnf in OrdType com com_ordMixin.
Canonical com_nominalType := Eval hnf in [nominalType for com by //].
Canonical com_trivialNominalType := Eval hnf in [trivialNominalType for com].

Definition ptr := (name * int)%type.

Canonical ptr_eqType := Eval hnf in [eqType of ptr].
Canonical ptr_choiceType := Eval hnf in [choiceType of ptr].
Canonical ptr_ordType := Eval hnf in [ordType of ptr].
Canonical ptr_nominalType := Eval hnf in [nominalType of ptr].

Inductive value :=
| VBool of bool
| VNum  of int
| VPtr  of ptr & int
| VNil.

Definition sum_of_value v :=
  match v with
  | VBool b => inl b
  | VNum n => inr (inl n)
  | VPtr p sz => inr (inr (inl (p, sz)))
  | VNil => inr (inr (inr tt))
  end.

Definition value_of_sum v :=
  match v with
  | inl b => VBool b
  | inr (inl n) => VNum n
  | inr (inr (inl (p, sz))) => VPtr p sz
  | inr (inr (inr tt)) => VNil
  end.

Lemma sum_of_valueK : cancel sum_of_value value_of_sum.
Proof. by case. Qed.
Lemma value_of_sumK : cancel value_of_sum sum_of_value.
Proof. by do ![case=>//]. Qed.
Definition value_eqMixin := CanEqMixin sum_of_valueK.
Canonical value_eqType := Eval hnf in EqType value value_eqMixin.
Definition value_choiceMixin := CanChoiceMixin sum_of_valueK.
Canonical value_choiceType := Eval hnf in ChoiceType value value_choiceMixin.
Definition value_ordMixin := CanOrdMixin sum_of_valueK.
Canonical value_ordType := Eval hnf in OrdType value value_ordMixin.
Definition value_nominalMixin := BijNominalMixin sum_of_valueK value_of_sumK.
Canonical value_nominalType :=
  Eval hnf in NominalType value value_nominalMixin.

Global Instance VBool_eqvar : {eqvar VBool}.
Proof. by move=> s b _ <-. Qed.

Global Instance VNum_eqvar : {eqvar VNum}.
Proof. by move=> s n _ <-. Qed.

Global Instance VPtr_eqvar : {eqvar VPtr}.
Proof. by move=> s p _ <-; finsupp. Qed.

Global Instance VNil_eqvar : {eqvar VNil}.
Proof. by []. Qed.


End Basic.
