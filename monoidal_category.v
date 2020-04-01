From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import monae_lib category.

(*
In this file:

- product category (product of two categories)

M1. monoidal cateogories
M2. monoidal closed categories
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* A concrete category isomorphic to the product category of C and D *)
(* sum version *)
Module ProductCategory.
Section def.
Variable C D : category.
Definition obj := (C * D)%type.
Definition el (X : obj) : Type := (El X.1 + El X.2)%type.
Definition separated (X Y : obj) (f : el X -> el Y) : Prop :=
  (forall x : El X.1, exists y : El Y.1, f (inl x) = inl y) /\
  (forall x : El X.2, exists y : El Y.2, f (inr x) = inr y).

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
Definition productCategory (C D : category) := Category.Pack (ProductCategory.mixin C D).

(*
(* A similar construction.
   Related to another tensor product in Cat, like the funny tensor? *)
Module WeirdProductCategory.
Section def.
Variable C D : category.
Definition obj := (C * D)%type.
Definition el (X : obj) : Type := (El X.1 * El X.2)%type.
Definition independent (X Y : obj) (f : el X -> el Y) : Prop :=
  (forall (x : El X.1) (y y' : El X.2), fst (f (x,y)) = fst (f (x,y'))) /\
  (forall (x x': El X.1) (y : El X.2), snd (f (x,y)) = snd (f (x',y))).

Section homfstsnd.
Let _homfst (X Y : obj) (f : el X -> el Y) : independent f -> El X.1 -> El Y.1.
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
End WeirdProductCategory.
*)


Canonical productCategory.

Section prodCat_pairhom.
Variables A B : category.  
Variables a1 a2 : A.
Variables b1 b2 : B.
Variables (f : {hom a1,a2}) (g : {hom b1,b2}).
Let C := productCategory A B.
Definition pairhom' (ab : El a1 + El b1) : El a2 + El b2 :=
  match ab with
  | inl a => inl (f a)
  | inr b => inr (g b)
  end.
Lemma pairhom'_in_hom : @InHom C _ _ (pairhom' : El (a1,b1).1 + El (a1,b1).2 -> El (a2,b2).1 + El (a2,b2).2).
rewrite /InHom /= /ProductCategory.inhom /=.
Admitted.
Definition pairhom : {hom (a1,b1),(a2,b2)} := Hom.Pack _ pairhom'_in_hom.
End prodCat_pairhom.

Module curry_left.
Section def.
Variables A B C : category.
Variable F' : functor (productCategory A B) C.
Variable a : A.
Definition F_obj : B -> C := fun b => F' (a,b).
Definition F_mor (b1 b2 : B) (f : {hom b1, b2}) : {hom F_obj b1, F_obj b2} :=
  F' # pairhom (idfun_hom a) f.
Program Definition mixin_of := @Functor.Mixin _ _ F_obj F_mor _ _.
Obligation 1.
Admitted.
Obligation 2.
Admitted.
Definition F := Functor.Pack mixin_of.
End def.
End curry_left.

Module MonoidalCategory.
Section def.
Record mixin_of (C : category) : Type := Mixin {
 I : C;
 prod : functor (productCategory C C) C;
 lambda : (curry_left.F prod I) ~> FId ;
 rho : forall A : C, El (prod (A, I)) -> El A ;
}.
Record class_of (T : Type) : Type := Class {
 base : Category.mixin_of T;
 mixin : mixin_of (Category.Pack base);
}.
Structure t : Type := Pack { T : Type; class : class_of T }.
End def.
Module Exports.
End Exports.
End MonoidalCategory.
Export MonoidalCategory.Exports.

