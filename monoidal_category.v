From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import monae_lib category.

(*
In this file:
M1. monoidal cateogories
M2. monoidal closed categories
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module ProductCategory.
Section def.
Variable C D : category.
Definition obj := (C * D)%type.
Definition el (XY : obj) : Type := (El XY.1 + El XY.2)%type.
(* naturality of f, seen as a transformation from 2 -> Cat *)
Definition separated (XY UV : obj) (f : el XY -> el UV) : Prop :=
  (forall x : El XY.1, exists u : El UV.1, f (inl x) = inl u) /\
  (forall y : El XY.2, exists v : El UV.2, f (inr y) = inr v).

Section homfstsnd.
Let _homfst (XY UV : obj) (f : el XY -> el UV) : separated f -> El XY.1 -> El UV.1.
case=> H _ x.
move/cid: (H x)=> [] u _.
exact u.
Defined.
Definition homfst := Eval hnf in _homfst.
Let _homsnd (XY UV : obj) (f : el XY -> el UV) : separated f -> El XY.2 -> El UV.2.
case=> _ H y.
move/cid: (H y)=> [] v _.
exact v.
Defined.
Definition homsnd := Eval hnf in _homsnd.
End homfstsnd.

Definition inhom (A B : obj) (f : el A -> el B) : Prop :=
  exists H : separated f, InHom (homfst H) /\ InHom (homsnd H).
Lemma idfun_separated (X : obj) : @separated X X idfun.
Admitted.
Lemma comp_separated (X Y Z : obj) (f :el X -> el Y) (g : el Y -> el Z) :
  separated f -> separated g -> separated (g \o f).
Admitted.
Lemma homfst_idfun X : homfst (idfun_separated X) = idfun.
Admitted.
Lemma homsnd_idfun X : homsnd (idfun_separated X) = idfun.
Admitted.
Lemma homfst_comp X Y Z (f : el X -> el Y) (g : el Y -> el Z)
      (Hf : separated f) (Hg : separated g) :
  homfst (comp_separated Hf Hg) = homfst Hg \o homfst Hf.
Admitted.
Lemma homsnd_comp X Y Z (f : el X -> el Y) (g : el Y -> el Z)
      (Hf : separated f) (Hg : separated g) :
  homsnd (comp_separated Hf Hg) = homsnd Hg \o homsnd Hf.
Admitted.
Definition mixin : Category.mixin_of (C * D).
refine (@Category.Mixin obj el inhom _ _).
- by move=> X; exists (idfun_separated X); rewrite homfst_idfun homsnd_idfun; split; apply id_in_hom.
- by move=> X Y Z f g [] sf [] homfl homfr [] sg [] homgl homgr ; exists (comp_separated sf sg); rewrite homfst_comp homsnd_comp; split; apply funcomp_in_hom.
Defined.  
End def.
End ProductCategory.
Canonical productCategory (C D : category) := Category.Pack (ProductCategory.mixin C D).
