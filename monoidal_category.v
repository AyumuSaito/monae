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
Let _homfst (X Y : obj) (f : el X -> el Y) : separated f -> El X.1 -> El Y.1.
case=> H _ x.
move/cid: (H x)=> [] y _.
exact y.
Defined.
Definition homfst := Eval hnf in _homfst.
Let _homsnd (X Y : obj) (f : el X -> el Y) : separated f -> El X.2 -> El Y.2.
case=> _ H x.
move/cid: (H x)=> [] y _.
exact y.
Defined.
Definition homsnd := Eval hnf in _homsnd.
End homfstsnd.

Lemma homfstK X Y (f : el X -> el Y) (Hf : separated f) (x : El X.1) :
  inl (homfst Hf x) = f (inl x).
Proof.
move: f Hf x.
case: X=> X1 X2; case:Y=> Y1 Y2 /= f [] /= Hf1 Hf2 x.
by case: (cid (Hf1 x))=> y ->.
Qed.
Lemma homsndK X Y (f : el X -> el Y) (Hf : separated f) (x : El X.2) :
  inr (homsnd Hf x) = f (inr x).
Proof.
move: f Hf x.
case: X=> X1 X2; case:Y=> Y1 Y2 /= f [] /= Hf1 Hf2 x.
by case: (cid (Hf2 x))=> y ->.
Qed.
Definition inhom (A B : obj) (f : el A -> el B) : Prop :=
  exists H : separated f, InHom (homfst H) /\ InHom (homsnd H).
Lemma idfun_separated (X : obj) : @separated X X idfun.
Proof. by split; move=> x; exists x. Qed.
Lemma comp_separated (X Y Z : obj) (f :el X -> el Y) (g : el Y -> el Z) :
  separated f -> separated g -> separated (g \o f).
Proof.
move: f g.
case: X=> X1 X2; case: Y=> Y1 Y2; case: Z=> Z1 Z2 f g [] /= Hf1 Hf2 [] /= Hg1 Hg2; split.
- by move=> x; case/cid: (Hf1 x)=> y /= ->; case/cid: (Hg1 y)=> z /= ->; exists z.
- by move=> x; case/cid: (Hf2 x)=> y /= ->; case/cid: (Hg2 y)=> z /= ->; exists z.
Qed.
Lemma homfst_idfun X : homfst (idfun_separated X) = idfun.
Proof.
apply funext=> x /=.
suff: inl (B:=El X.2) (homfst (idfun_separated X) x) = inl x by move=> [=].
by rewrite homfstK.
Qed.
Lemma homsnd_idfun X : homsnd (idfun_separated X) = idfun.
Proof.
apply funext=> x /=.
suff: inr (A:=El X.1) (homsnd (idfun_separated X) x) = inr x by move=> [=].
by rewrite homsndK.
Qed.
Lemma homfst_comp X Y Z (f : el X -> el Y) (g : el Y -> el Z)
      (Hf : separated f) (Hg : separated g) :
  homfst (comp_separated Hf Hg) = homfst Hg \o homfst Hf.
Proof.
apply funext=> x /=.
suff: inl (B:=El Z.2) (homfst (comp_separated Hf Hg) x) = inl (homfst Hg (homfst Hf x))
  by move => [=].
by rewrite 3!homfstK.
Qed.
Lemma homsnd_comp X Y Z (f : el X -> el Y) (g : el Y -> el Z)
      (Hf : separated f) (Hg : separated g) :
  homsnd (comp_separated Hf Hg) = homsnd Hg \o homsnd Hf.
Proof.
apply funext=> x /=.
suff: inr (A:=El Z.1) (homsnd (comp_separated Hf Hg) x) = inr (homsnd Hg (homsnd Hf x))
  by move => [=].
by rewrite 3!homsndK.
Qed.
Definition mixin : Category.mixin_of (C * D).
refine (@Category.Mixin obj el inhom _ _).
- by move=> X; exists (idfun_separated X); rewrite homfst_idfun homsnd_idfun; split; apply id_in_hom.
- by move=> X Y Z f g [] sf [] homfl homfr [] sg [] homgl homgr ; exists (comp_separated sf sg); rewrite homfst_comp homsnd_comp; split; apply funcomp_in_hom.
Defined.  
End def.
End ProductCategory.
Canonical productCategory (C D : category) := Category.Pack (ProductCategory.mixin C D).
