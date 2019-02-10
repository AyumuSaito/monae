Ltac typeof X := type of X.
Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Contents:
- generic Haskell-like functions and notations
- Module Functor
- Module Laws.
    definition of algebraic laws to be used with monads
- Module Monad.
    definition of standard notations
- Section fmap_and_join.
- Section rep.
    simple effect of counting
- Module MonadFail.
    definition of guard
- Module MonadAlt.
    non-deterministic choice
  Section subsequences_of_a_list.
  Section permutation_and_insertion.
    examples of non-deterministic programs
- Module MonadAltCI.
- Module MonadNondet
  Section permutations.
- Module MonadExcept.
    example of the fast product
*)

Reserved Notation "A `2" (format "A `2", at level 3).
Reserved Notation "f ^`2" (format "f ^`2", at level 3).
Reserved Notation "l \\ p" (at level 50).
Reserved Notation "m >>= f" (at level 50).
Reserved Notation "f =<< m" (at level 50).
Reserved Notation "'do' x <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "'do' x : T <- m ; e"
  (at level 60, x ident, m at level 200, e at level 60).
Reserved Notation "m >=> n" (at level 50).
Reserved Notation "n <=< m" (at level 50).
Reserved Notation "x '[~]' y" (at level 50).
Reserved Notation "'[~p]'".
Reserved Notation "f ($) m" (at level 11).
Reserved Notation "f (o) g" (at level 11).

Notation "l \\ p" := ([seq x <- l | x \notin p]).

(* some Haskell-like functions *)
Definition foldr1 (A : Type) (def : A) (f : A -> A -> A) (s : seq A) :=
  match s with
    | [::] => def
    | [:: h] => h
    | h :: h' :: t => foldr f h [:: h' & t]
  end.

Definition cp {A B} (x : seq A) (y : seq B) := [seq (x', y') | x' <- x, y' <- y].

Lemma cp1 A B (a : A) (s : seq B) : cp [:: a] s = map (fun b => (a, b)) s.
Proof. elim: s => // h t /= <-; by rewrite cats0. Qed.

Definition zipWith {A B C} (op : A -> B -> C) a b : seq C :=
  map (fun x => op x.1 x.2) (zip a b).

Section fold.
Variables (T R : Type) (f : T -> R -> R) (r : R).

Section universal.
Variable (g : seq T -> R).
Hypothesis H1 : g nil = r.
Hypothesis H2 : forall h t, g (h :: t) = f h (g t).
Lemma foldr_universal : g = foldr f r.
Proof.
apply functional_extensionality; elim => // h t ih /=; by rewrite H2 ih.
Qed.
Lemma foldr_universal_ext x : g x = foldr f r x.
Proof. by rewrite -(foldr_universal). Qed.
End universal.

Section fusion_law.
Variables (U : Type) (h : U -> R) (w : U) (g : T -> U -> U).
Hypothesis H1 : h w = r.
Hypothesis H2 : forall x y, h (g x y) = f x (h y).
Lemma foldr_fusion : h \o foldr g w = foldr f r.
Proof.
apply functional_extensionality; elim => // a b /= ih; by rewrite H2 ih.
Qed.
Lemma foldr_fusion_ext x : (h \o foldr g w) x = foldr f r x.
Proof. by rewrite -foldr_fusion. Qed.
End fusion_law.

End fold.

Section curry.
Variables A B C : Type.
Implicit Types f : A -> B -> C.

(*Definition uncurry f : A * B -> C := fun x => f x.1 x.2.*)
Definition uncurry f := prod_curry f.

Lemma uncurryE f a b : (uncurry f) (a, b) = f a b. Proof. by []. Qed.

Definition curry (g : A * B -> C) : A -> B -> C := fun a b => g (a, b).

Lemma curryK : cancel curry uncurry.
Proof. by move=> f; apply functional_extensionality; case. Qed.

Lemma uncurryK f : cancel uncurry curry.
Proof. by []. Qed.
End curry.

Definition ucat {A} := uncurry (@cat A).

Definition uaddn := uncurry addn.

Lemma uaddnE n m : uaddn (n, m) = n + m. Proof. by rewrite /uaddn uncurryE. Qed.

Definition const A B (b : B) := fun _ : A => b.

Definition wrap {A} (a : A) := [:: a].

Fixpoint scanl A B (op : B -> A -> B) (b : B) (s : seq A) : seq B :=
  if s isn't x :: xs then [::] else (op b x) :: scanl op (op b x) xs.

Lemma compA {A B C D} (f : C -> D) (g : B -> C) (h : A -> B) : f \o (g \o h) = (f \o g) \o h.
Proof. by []. Qed.

Lemma compfid A B (f : A -> B) : f \o id = f. Proof. by []. Qed.

Lemma compidf A B (f : A -> B) : id \o f = f. Proof. by []. Qed.

Lemma compE A B C (g : B -> C) (f : A -> B) a : (g \o f) a = g (f a).
Proof. by []. Qed.

(* map laws of a functor *)
Module FunctorLaws.
Section def.
Variable (M : Type -> Type) (f : forall A B, (A -> B) -> M A -> M B).
Definition id := forall A, f id = id :> (M A -> M A).
Definition comp := forall A B C (g : B -> C) (h : A -> B),
  f (g \o h) = f g \o f h :> (M A -> M C).
End def.
End FunctorLaws.

Module Functor.
Record class_of (m : Type -> Type) : Type := Class {
  f : forall A B, (A -> B) -> m A -> m B ;
  _ : FunctorLaws.id f ;
  _ : FunctorLaws.comp f
}.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Module Exports.
Notation functor := t.
Definition Fun (F : functor) : forall A B, (A -> B) -> m F A -> m F B :=
  let: Pack _ (Class f _ _) := F return forall A B, (A -> B) -> m F A -> m F B in f.
Arguments Fun _ [A] [B].
Coercion m : functor >-> Funclass.
End Exports.
End Functor.
Export Functor.Exports.
Notation "F # f" := (Fun F f) (at level 11).

Section functor_lemmas.
Lemma functor_id (F : functor) : FunctorLaws.id (Fun F).
Proof. by case: F => [? []]. Qed.
Lemma functor_o (F : functor) : FunctorLaws.comp (Fun F).
Proof. by case: F => [? []]. Qed.
(*Lemma functor_ext (F G : functor) : Fun F = Fun G -> F = G.
Proof.
move: F G => [[F f1 f2]] [[G g1 g2]] /= ?; subst G; congr Functor.Pack.
have {g2}<- : f2 = g2 by exact/ProofIrrelevance.proof_irrelevance.
congr Functor.Class; exact/ProofIrrelevance.proof_irrelevance.
Qed.*)
End functor_lemmas.

Definition Squaring (A : Type) := (A * A)%type.
Notation "A `2" := (Squaring A).
Definition squaring_f A B (f : A -> B) : A`2 -> B`2 := fun x => (f x.1, f x.2).
Lemma squaring_f_id : FunctorLaws.id squaring_f.
Proof. by move=> A /=; apply functional_extensionality => -[x1 x2]. Qed.
Lemma squaring_f_comp : FunctorLaws.comp squaring_f.
Proof. by move=> A B C g h /=; apply functional_extensionality => -[x1 x2]. Qed.
Definition squaring : functor (*Squaring*) :=
  Functor.Pack (Functor.Class squaring_f_id squaring_f_comp).
Notation "f ^`2" := (squaring # f).

Section functorid.
Definition id_f A B (f : A -> B) := f.
Lemma id_id : FunctorLaws.id id_f. Proof. by []. Qed.
Lemma id_comp : FunctorLaws.comp id_f. Proof. by []. Qed.
Definition FId : functor (*id*) := Functor.Pack (Functor.Class id_id id_comp).
End functorid.

Section functorcomposition.
Variables (*(M N : Type -> Type)*) (f : functor) (g : functor).
Definition functorcomposition A B := fun h : A -> B => f # (g # h).
Lemma functorcomposition_id : FunctorLaws.id functorcomposition.
Proof.
by rewrite /FunctorLaws.id => A; rewrite /functorcomposition 2!functor_id.
Qed.
Lemma functorcomposition_comp : FunctorLaws.comp functorcomposition.
Proof.
rewrite /FunctorLaws.comp => A B C g' h; rewrite /functorcomposition.
apply functional_extensionality => m; by rewrite [in RHS]compE 2!functor_o.
Qed.
Definition FComp : functor (*(M \o N)*) :=
  Functor.Pack (Functor.Class functorcomposition_id functorcomposition_comp).
End functorcomposition.

Section functorcomposition_lemmas.
Variables (*(M : Type -> Type)*) (f : functor).
Lemma FCompId : FComp f FId = f.
Proof.
destruct f as [m [f0 f1 f2]]; congr Functor.Pack; congr Functor.Class => //;
  exact/ProofIrrelevance.proof_irrelevance.
Qed.
Lemma FIdComp : FComp FId f = f.
Proof.
destruct f as [m [f0 f1 f2]]; congr Functor.Pack; congr Functor.Class => //;
  exact/ProofIrrelevance.proof_irrelevance.
Qed.
End functorcomposition_lemmas.

Section functorcomposition_lemmas'.
Variables (f : functor) (g : functor) (h : functor).
Lemma FCompA : FComp (FComp f g) h = FComp f (FComp g h).
Proof.
destruct f as [m [f0 f1 f2]].
destruct g as [n [g0 g1 g2]].
destruct h as [o [h0 h1 h2]].
congr Functor.Pack; congr Functor.Class => //;
  exact/ProofIrrelevance.proof_irrelevance.
Qed.
Lemma FCompE A B (k:A->B) : (FComp f g) # k = f # (g # k).
Proof. by []. Qed.
End functorcomposition_lemmas'.

Section curry_functor.
Definition curry_M X : Type -> Type := fun B => (X * B)%type.
Definition curry_f X A B (f : A -> B) : curry_M X A -> curry_M X B :=
  fun x : X * A => (x.1, f x.2).
Lemma curry_f_id X : FunctorLaws.id (@curry_f X).
Proof.
rewrite /FunctorLaws.id => A.
by rewrite /curry_f; apply functional_extensionality => -[].
Qed.
Lemma curry_f_comp X : FunctorLaws.comp (@curry_f X).
Proof.
rewrite /FunctorLaws.comp => A B C g h.
by rewrite /curry_f; apply functional_extensionality => -[].
Qed.
Definition curry_F X : functor (*(curry_M X)*) :=
  Functor.Pack (Functor.Class (curry_f_id X) (curry_f_comp X)).
End curry_functor.

Section uncurry_functor.
Definition uncurry_M X : Type -> Type := fun B => X -> B.
Definition uncurry_f X A B (f : A -> B) : uncurry_M X A -> uncurry_M X B :=
  fun g : X -> A => f \o g.
Lemma uncurry_f_id X : FunctorLaws.id (@uncurry_f X).
Proof.
rewrite /FunctorLaws.id => A; rewrite /uncurry_f.
apply functional_extensionality => x; by rewrite compidf.
Qed.
Lemma uncurry_f_comp X : FunctorLaws.comp (@uncurry_f X).
Proof.
rewrite /FunctorLaws.comp => A B C g h; rewrite /uncurry_f.
apply functional_extensionality => x; by rewrite compE compA.
Qed.
Definition uncurry_F X : functor (*(uncurry_M X)*) :=
  Functor.Pack (Functor.Class (uncurry_f_id X) (uncurry_f_comp X)).
End uncurry_functor.

Section natural_transformation.
Variables (*(M N : Type -> Type)*) (f : functor) (g : functor).
Definition transformation_type := forall A, f A -> g A.
Definition naturalP (phi : transformation_type) :=
  forall A B (h : A -> B), (g # h) \o (phi A) = (phi B) \o (f # h).
End natural_transformation.
Arguments naturalP : clear implicits.

Section natural_transformation_example.
Definition fork A (a : A) := (a, a).
(* fork is a natural transformation Fid -> squaring *)
Lemma fork_natural : naturalP FId squaring fork.
Proof. by []. Qed.
End natural_transformation_example.

Section adjoint_functors.
Variables (*(M N : Type -> Type)*) (f : functor) (g : functor).
Definition eta_type := forall A, A -> (g \o f) A.
Definition eps_type := forall A, (f \o g) A -> A.
Definition adjointP (eps : eps_type) (eta : eta_type) :=
  naturalP (FComp f g) FId eps /\ naturalP FId (FComp g f) eta.
Definition triangular_law1 (eps : eps_type) (eta : eta_type) A :=
  (eps (f A)) \o (f # eta A) = @id (f A).
Definition triangular_law2 (eps : eps_type) (eta : eta_type) A :=
  (g # eps A) \o (eta (g A)) = @id (g A).
Definition phi A B (eta : eta_type) : (f A -> B) -> A -> g B :=
  fun h => (g # h) \o (@eta A).
Definition psi A B (eps : eps_type) : (A -> g B) -> f A -> B :=
  fun h => (@eps B) \o (f # h).
End adjoint_functors.

Section adjoint_example.
Variable (X : Type).
Definition curry_eps : eps_type (curry_F X) (uncurry_F X) :=
  fun A (af : X * (X -> A)) => af.2 af.1.
Definition curry_eta : eta_type (curry_F X) (uncurry_F X) :=
  fun A (a : A) => fun x : X => (x, a).
Lemma adjoint_currry : adjointP curry_eps curry_eta.
Proof.
split; rewrite /naturalP => A B h /=.
- rewrite /id_f /curry_eps /curry_f /= /uncurry_M /uncurry_f /=.
  by apply functional_extensionality => -[].
- rewrite /uncurry_f /curry_f /curry_eta /id_f /=.
  apply functional_extensionality => a /=.
  by apply functional_extensionality.
Qed.
Lemma curry_triangular_law1 A : triangular_law1 curry_eps curry_eta A.
Proof.
rewrite /triangular_law1.
apply functional_extensionality => -[a b].
by rewrite /= /curry_eta.
Qed.
Lemma curry_triangular_law2 A : triangular_law2 curry_eps curry_eta A.
Proof.
rewrite /triangular_law2.
rewrite /uncurry_F /curry_eps /curry_eta /uncurry_M /=.
rewrite /uncurry_f /= /comp /=.
apply functional_extensionality => f.
by apply functional_extensionality => x.
Qed.
End adjoint_example.

Module BindLaws.
Section laws.
Variable M : Type -> Type.

Variable b : forall A B, M A -> (A -> M B) -> M B.

Local Notation "m >>= f" := (b m f).

Definition associative := forall A B C (m : M A) (f : A -> M B) (g : B -> M C),
  (m >>= f) >>= g = m >>= (fun x => (f x >>= g)).

Definition bind_right_distributive (add : forall B, M B -> M B -> M B) :=
  forall A B (m : M A) (k1 k2 : A -> M B),
    m >>= (fun x => add _ (k1 x) (k2 x)) = add _ (m >>= k1) (m >>= k2).

Definition bind_left_distributive (add : forall B, M B -> M B -> M B) :=
  forall A B (m1 m2 : M A) (k : A -> M B),
    (add _ m1 m2) >>= k = add _ (m1 >>= k) (m2 >>= k).

Definition right_zero (f : forall A, M A) :=
  forall A B (g : M B), g >>= (fun _ => f A) = f A.

Definition left_zero (f : forall A, M A) := forall A B g, f A >>= g = f B.

Definition left_neutral (r : forall A, A -> M A) :=
  forall A B (x : A) (f : A -> M B), r _ x >>= f = f x.

Definition right_neutral (r : forall A, A -> M A) :=
  forall A (m : M A), m >>= r _ = m.

Definition left_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) :=
  forall A (m : M A), add _ (r _) m = m.

Definition right_id (r : forall A, M A) (add : forall B, M B -> M B -> M B) :=
  forall A (m : M A), add _ m (r _) = m.

End laws.
End BindLaws.

Section monad_of_adjoint.
Section def.
Variables (*(F G : Type -> Type)*) (f : functor) (g : functor).
Variables (eps : eps_type f g) (eta : eta_type f g).
Definition M := g \o f.
Definition m : functor := FComp g f.
Definition muM A : M (M A) -> M A := g # (@eps (f A)).
Definition etaM A : A -> M A := @eta A.
Definition bind A B : M A -> (A -> M B) -> M B :=
  fun x c => muM (((FComp g f) # c) x).
End def.
Section prop.
Variables (*(F G : Type -> Type)*) (f : functor) (g : functor).
Variables (eps : eps_type f g) (eta : eta_type f g).
Hypothesis Had : adjointP eps eta.
Hypothesis Ht1 : forall A, triangular_law1 eps eta A.
Hypothesis Ht2 : forall A, triangular_law2 eps eta A.
Section muM_natural.
Let M := M f g.
Let m := m f g.
Let muM := muM eps.
Let mE : m = FComp g f.
Proof. done. Qed.
Let muME : muM = fun A => g # (@eps (f A)).
Proof. done. Qed.
Lemma muM_natural : naturalP (FComp m m) m muM.
Proof.
move: Had => [] Heps _; move: Heps; rewrite/naturalP => Heps.
rewrite !muME => A B h.
rewrite(_:FComp (FComp g f) (FComp g f) # h = g # ((FComp f g) # (f # h))) //.
rewrite(_:g # eps (A:=f B) \o g # (FComp f g # (f # h))
        = g # (eps (A:=f B) \o (FComp f g # (f # h)))); last by rewrite -functor_o.
rewrite -Heps.
rewrite !FCompE /FId /id_f /=.
by rewrite functor_o.
Qed.
Lemma epsC A : eps (A:=A) \o eps (A:=(f \o g)A) = eps (A:=A) \o f # (g # eps (A:=A)).
Proof.
move:Had=>[];rewrite/naturalP=>Heps _.
by move:(Heps _ _ (eps (A:=A))) => <-.
Qed.
Lemma muMA A : muM (A:=A) \o muM (A:=M A) = muM (A:=A) \o (m # muM (A:=A)).
Proof.
rewrite muME.
have->: g # eps (A:=f A) \o g # eps (A:=f (M A)) =
        g # (eps (A:=f A) \o eps (A:=f (M A))) by rewrite functor_o.
by rewrite epsC functor_o.
Qed.
End muM_natural.
Lemma law1 : BindLaws.left_neutral (bind eps) (etaM eta).
Proof.
rewrite /BindLaws.left_neutral => A B a h.
case: Had; rewrite /naturalP => _ /(_ _ _ h) Had2.
rewrite /bind /muM /etaM.
(*rewrite /= /functorcomposition /= in Had2. *)
rewrite -(compE (FComp g f # h)).
rewrite Had2.
move: Ht2; rewrite /triangular_law2 => Ht2'.
rewrite -(compE (g # _)) compA.
by rewrite Ht2'.
Qed.
Lemma law2 : BindLaws.right_neutral (bind eps) (etaM eta).
Proof.
rewrite /BindLaws.right_neutral => A m.
rewrite /bind /muM /etaM.
rewrite -(compE (g # _)).
rewrite -(functor_o g).
(* NB: simple "rewrite -functor_o" does not work. Notation issue? *)
by rewrite Ht1 functor_id.
Qed.
Lemma law3 : BindLaws.associative (bind eps).
Proof.
rewrite /BindLaws.associative => A B C x ab bc.
rewrite /bind.
set T := FComp g f.
(*congr (muM g eps).*)
have -> : (T # (fun x : A => muM eps ((T # bc) (ab x)))) x
            = (T # (muM eps (A:=C))) ((T # (T # bc)) ((T # ab) x)).
- rewrite functor_o /funcomp.
  congr (T # muM eps (A:=C)).
    by rewrite functor_o /funcomp.
move: (muM_natural bc).
move: muMA.
set M := M f g.
set muM := muM eps.
change (monad_of_adjoint.m f g) with T.
move=>muMA.
rewrite FCompE.
have->:(T # bc) (muM B ((T # ab) x)) = (T # bc \o muM B) ((T # ab) x) by done.
move->.
rewrite compE.
change (muM C (muM (M C) ((T # (T # bc)) ((T # ab) x)))) with
    ((muM C \o muM (M C)) ((T # (T # bc)) ((T # ab) x))).
by rewrite muMA.
Qed.
End prop.

End monad_of_adjoint.

Module JoinLaws.
Section join_laws.
Context {M : functor}.
Variables (ret : forall A, A -> M A) (join : forall A, M (M A) -> M A).
Arguments join {A}.
Arguments ret {A}.

Definition join_left_unit := forall A, join \o ret = id :> (M A -> M A).

Definition join_right_unit := forall A, join \o M # ret = id :> (M A -> M A).

Definition join_associativity :=
  forall A, join \o M # join = join \o join :> (M (M (M A)) -> M A).

(* join commutes with F *)
Definition join_functor_commutativity :=
  forall A B (f : A -> B), M # f \o join = join \o M # (M # f) :> (M (M A) -> M B).
End join_laws.
End JoinLaws.

Section from_join_laws_to_bind_laws.

Variable M : functor.
Variable (ret : forall A, A -> M A) (join : forall A, M (M A) -> M A).

Hypothesis fmap_ret : forall (A B : Type) (f : A -> B), M # f \o (@ret _) = (@ret _) \o f.
Hypothesis join_ret : JoinLaws.join_left_unit ret join.
Hypothesis join_fmap_ret : JoinLaws.join_right_unit ret join.
Hypothesis join_naturality : JoinLaws.join_functor_commutativity join.
Hypothesis join_fmap_join : JoinLaws.join_associativity join.

Let bind (A B : Type) (m : M A) (f : A -> M B) : M B := join ((M # f) m).

Lemma bindretf_derived : BindLaws.left_neutral bind ret.
Proof.
move=> A B a f; rewrite /bind -(compE (@join _)) -(compE _ (@ret _)) -compA.
by rewrite fmap_ret compA join_ret compidf.
Qed.

Lemma bindmret_derived : BindLaws.right_neutral bind ret.
Proof. by move=> A m; rewrite /bind -(compE (@join _)) join_fmap_ret. Qed.

Lemma bindA_derived : BindLaws.associative bind.
Proof.
move=> A B C m f g; rewrite /bind /=.
rewrite [LHS](_ : _ = ((@join _ \o (M # g \o @join _) \o M # f) m)) //.
rewrite join_naturality compA -join_fmap_join -(compE (@join _)).
transitivity ((@join _ \o M # (@join _ \o (M # g \o f))) m) => //.
by rewrite -2!compA 2!functor_o.
Qed.

End from_join_laws_to_bind_laws.

Module Monad.
Record mixin_of (M : functor) : Type := Mixin {
  ret : forall A, A -> M A ;
  join : forall A, M (M A) -> M A ;
  _ : naturalP FId M ret ; (* ret is natural *)
  _ : naturalP (FComp M M) M join ; (* join is natural *)
  _ : JoinLaws.join_left_unit ret join ;
  _ : JoinLaws.join_right_unit ret join ;
  _ : JoinLaws.join_associativity join;
  }.
Record class_of (M : Type -> Type) := Class {
  base : Functor.class_of M ; mixin : mixin_of (Functor.Pack base) }.
Structure t : Type := Pack { car : Type -> Type ; class : class_of car }.
Definition baseType (M : t) := Functor.Pack (base (class M)).
Module Exports.
Definition Ret (M : t) A : A -> baseType M A :=
  let: Pack _ (Class _ (Mixin ret _ _ _ _ _ _) ) := M in ret A.
Arguments Ret {M A} : simpl never.
Definition Join (M : t) A : baseType M (baseType M A) -> baseType M A :=
  let: Pack _ (Class _ (Mixin _ join _ _ _ _ _)) := M in join A.
Arguments Join {M A} : simpl never.
Definition Bind (M : t) A B (x : baseType M A) (f : A -> baseType M B) : baseType M B :=
  let: Pack _ (Class M' (Mixin _ _ _ _ _ _ _)) := M in
  Join ((baseType M # f) x).
Arguments Bind {M A B} : simpl never.
Notation "m >>= f" := (Bind m f).
Notation monad := t.
Coercion baseType : monad >-> functor.
Canonical baseType.
End Exports.
End Monad.
Export Monad.Exports.

Section monad_interface.
Variable M : monad.
Lemma ret_naturality : naturalP FId M (@Ret M).
Proof. by case: M => ? [? []]. Qed.
Lemma join_naturality : naturalP (FComp M M) M (@Join M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinretM : JoinLaws.join_left_unit (@Ret M) (@Join M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinMret : JoinLaws.join_right_unit (@Ret M) (@Join M).
Proof. by case: M => ? [? []]. Qed.
Lemma joinA : JoinLaws.join_associativity (@Join M).
Proof. by case: M => ? [? []]. Qed.
Lemma bindE (A B:Type) : forall x (f : A -> M B), Bind x f = Join ((M # f) x).
Proof. by case: M => ? [? []]. Qed.
End monad_interface.

Section monad_lemmas.
Variable M : monad.
Lemma bindretf : BindLaws.left_neutral (@Bind M) (@Ret M).
Proof.
move=> A B a f.
rewrite bindE  -(compE Join _) -(compE _ Ret) -compA.
rewrite ret_naturality compA.
by rewrite joinretM compidf.
Qed.
Lemma bindmret : BindLaws.right_neutral (@Bind M) (@Ret _).
Proof.
move=> A m.
by rewrite bindE -(compE Join) joinMret.
Qed.
Lemma bindA : BindLaws.associative (@Bind M).
Proof.
rewrite /BindLaws.associative => A B C x ab bc.
rewrite !bindE.
have -> : (fun x0 : A => ab x0 >>= bc) = Join \o (fun y => (M # bc) (ab y))
  by apply functional_extensionality => y; rewrite bindE; congr Join.
have -> : Join ((M # (Join \o (fun y : A => (M # bc) (ab y)))) x) =
          ((Join \o (M # Join)) \o (M # (fun y : A => (M # bc) (ab y)))) x
  by rewrite functor_o.
rewrite  joinA.
change (Join ((M # bc) (Join ((M # ab) x)))) with
    (Join ((M # bc \o Join) ((M # ab) x))).
rewrite join_naturality.
do 2 congr Join.
by rewrite [in X in _ = X]functor_o.
Qed.
End monad_lemmas.
(*Module Monad.
Record class_of (m : Type -> Type) : Type := Class {
  ret : forall A, A -> m A ;
  bind : forall A B, m A -> (A -> m B) -> m B ;
  _ : BindLaws.left_neutral bind ret ;
  _ : BindLaws.right_neutral bind ret ;
  _ : BindLaws.associative bind }.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Module Exports.
Definition Ret (M : t) A : A -> m M A :=
  let: Pack _ (Class x _ _ _ _) := M in x A.
Arguments Ret {M A} : simpl never.
Definition Bind (M : t) A B : m M A -> (A -> m M B) -> m M B :=
  let: Pack _ (Class _ x _ _ _) := M in x A B.
Arguments Bind {M A B} : simpl never.
Notation "m >>= f" := (Bind m f).
Notation monad := t.
Coercion m : monad >-> Funclass.
End Exports.
End Monad.
Export Monad.Exports.

Section monad_lemmas.
Variable M : monad.
Lemma bindretf : BindLaws.left_neutral (@Bind M) (@Ret _).
Proof. by case: M => m []. Qed.
Lemma bindmret : BindLaws.right_neutral (@Bind M) (@Ret _).
Proof. by case: M => m []. Qed.
Lemma bindA : BindLaws.associative (@Bind M).
Proof. by case: M => m []. Qed.
End monad_lemmas.*)

Notation "'do' x <- m ; e" := (m >>= (fun x => e)).
Notation "'do' x : T <- m ; e" := (m >>= (fun x : T => e)) (only parsing).
Notation "m >> f" := (m >>= fun _ => f) (at level 50).
Definition skip M := @Ret M _ tt.
Arguments skip {M} : simpl never.

Ltac bind_ext :=
  let congr_ext m := ltac:(congr (Bind m); apply functional_extensionality) in
  match goal with
    | |- @Bind _ _ _ ?m ?f1 = @Bind _ _ _ ?m ?f2 =>
      congr_ext m
    | |- @Bind _ _ _ ?m1 ?f1 = @Bind _ _ _ ?m2 ?f2 =>
      first[ simpl m1; congr_ext m1 | simpl m2; congr_ext m2 ]
  end.

(* experimental *)
Tactic Notation "With" tactic(tac) "Open" ssrpatternarg(pat) :=
  ssrpattern pat;
  let f := fresh "f" in
  intro f;
  let g := fresh "g" in
  let typ := typeof f in
  let x := fresh "x" in
  evar (g : typ);
  rewrite (_ : f = g);
  [rewrite {}/f {}/g|
   apply functional_extensionality => x; rewrite {}/g {}/f; tac]; last first.

Tactic Notation "Open" ssrpatternarg(pat) :=
  With (idtac) Open pat.

Tactic Notation "Inf" tactic(tac) :=
  (With (tac; reflexivity) Open (X in @Bind _ _ _ _ X = _ )) ||
  (With (tac; reflexivity) Open (X in _ = @Bind _ _ _ _ X)).

Tactic Notation "rewrite_" constr(lem) :=
  (With (rewrite lem; reflexivity) Open (X in @Bind _ _ _ _ X = _ )) ||
  (With (rewrite lem; reflexivity) Open (X in _ = @Bind _ _ _ _ X)).

Lemma bindmskip (M : monad) (m : M unit) : m >> skip = m.
Proof. rewrite -[RHS]bindmret; bind_ext; by case. Qed.

Lemma bindskipf (M : monad) A (m : M A) : skip >> m = m.
Proof. exact: bindretf. Qed.

Fixpoint sequence (M : monad) A (s : seq (M A)) : M (seq A) :=
  if s isn't h :: t then Ret [::] else
  do v <- h; do vs <- sequence t; Ret (v :: vs).

Lemma sequence_nil (M : monad) A : sequence [::] = Ret [::] :> M (seq A).
Proof. by []. Qed.

Lemma sequence_cons (M : monad) A h (t : seq (M A)) :
  sequence (h :: t) = do x <- h ; do vs <- sequence t ; Ret (x :: vs).
Proof. by []. Qed.

Module Monad_of_bind_ret.
Section monad_of_bind_ret.
Variable M : Type -> Type.
Variable bind : forall (A B : Type), M A -> (A -> M B) -> M B.
Variable ret : forall A, A -> M A.
Hypothesis bindretf : BindLaws.left_neutral bind ret.
Hypothesis bindmret : BindLaws.right_neutral bind ret.
Hypothesis bindA : BindLaws.associative bind.

Definition fmap A B (f : A -> B) (m : M A) := bind m (ret (A:=B) \o f).
Lemma fmap_id : FunctorLaws.id fmap.
Proof.
move=> A; apply functional_extensionality => m; by rewrite /fmap bindmret.
Qed.
Lemma fmap_o : FunctorLaws.comp fmap.
Proof.
move=> A B C g h; apply functional_extensionality => m.
rewrite /fmap compE bindA.
congr bind.
apply functional_extensionality => a.
by rewrite bindretf.
Qed.

Definition functor_mixin := Functor.Class fmap_id fmap_o.
(*Notation "f ($) m" := ((fmap _ # f) m).*)

Lemma bind_fmap A B C (f : A -> B) (m : M A) (g : B -> M C) :
  bind (fmap f m) g = bind m (g \o f).
Proof.
rewrite /fmap bindA.
congr bind.
apply functional_extensionality => a.
by rewrite bindretf.
Qed.

Let M' := Functor.Pack functor_mixin.
Let ret' : forall A, A -> M' A := ret.
Definition join A (pp : M' (M' A)) := bind pp id.

Lemma ret_naturality : naturalP FId M' ret.
Proof.
move => A B h.
rewrite /FId /id_f /=.
apply functional_extensionality => a.
rewrite /fmap.
rewrite !compE.
by rewrite bindretf.
Qed.

Lemma bindE A B m (f : A -> M' B) : bind m f = join ((M' # f) m).
Proof. by rewrite /join bind_fmap. Qed.

Lemma fmap_bind A B C (f : A -> B) m (g : C -> M A) :
  (fmap f) (bind m g) = bind m (fmap f \o g).
Proof. by rewrite /fmap bindA bindE. Qed.

Lemma joinretM : JoinLaws.join_left_unit ret' join.
Proof.
rewrite /join => A; apply functional_extensionality => ma.
by rewrite compE bindretf.
Qed.
Lemma joinMret : JoinLaws.join_right_unit ret' join.
Proof.
rewrite /join => A; apply functional_extensionality => ma.
by rewrite compE bind_fmap compidf bindmret.
Qed.

Lemma join_naturality : naturalP (FComp M' M') M' join.
Proof.
move => A B h.
apply functional_extensionality => mma.
rewrite /Fun 2!compE /fmap [in RHS]/join bind_fmap [in LHS]/join.
by rewrite bindA.
Qed.

Lemma joinA : JoinLaws.join_associativity join.
Proof.
move => A; apply functional_extensionality => mmma.
rewrite /join /Fun /fmap !compE.
by rewrite bind_fmap compidf bindA.
Qed.

Definition monad_mixin := Monad.Mixin ret_naturality join_naturality joinretM joinMret joinA.
End monad_of_bind_ret.
Module Exports.
Definition Monad_of_bind_ret M bind ret a b c := Monad.Pack (Monad.Class (@monad_mixin M bind ret a b c)).
End Exports.
End Monad_of_bind_ret.
Export Monad_of_bind_ret.Exports.

Section fmap_def.
Variable M : monad.
Definition fmap' := fun A B (f : A -> B) (m : M _) => locked (m >>= (Ret \o f)).
Lemma fmap'_def A B (f : A -> B) (m : M _) : (fmap' f) m = m >>= (Ret \o f).
Proof. by rewrite /fmap'; unlock. Qed.
Lemma fmap'_id : FunctorLaws.id fmap'.
Proof.
move=> A; apply functional_extensionality => m; by rewrite fmap'_def bindmret.
Qed.
Lemma fmap'_o : FunctorLaws.comp fmap'.
Proof.
move=> A B C g h; apply functional_extensionality => m.
by rewrite !fmap'_def compE !fmap'_def bindA; rewrite_ bindretf.
Qed.
(* monadic counterpart of function application: applies a pure function to a monad *)
(* aka liftM in gibbons2011icfp, notation ($) in mu2017 *)
(*Definition fmap : functor := Functor.Pack (Functor.Class fmap'_id fmap'_o).*)
End fmap_def.
Notation "f ($) m" := ((_ # f) m).

Section fmap_and_join.

Variable M : monad.

Lemma fmap_def A B (f : A -> B) (m : M _) : f ($) m = m >>= (Ret \o f).
Proof.
rewrite bindE.
rewrite functor_o.
rewrite compE.
rewrite -(compE Join).
by rewrite joinMret.
Qed.

Lemma fmap_ret A B (f : A -> B) : (M # f) \o Ret = Ret \o f.
Proof.
by apply functional_extensionality => a; rewrite compE fmap_def bindretf.
Qed.

Lemma fmap_retE A B (f : A -> B) a : f ($) Ret a = (Ret \o f) a :> M _.
Proof. by rewrite -fmap_ret. Qed.

Lemma bind_fmap A B C (f : A -> B) (m : M A) (g : B -> M C) :
  f ($) m >>= g = m >>= (g \o f).
Proof. by rewrite fmap_def bindA; rewrite_ bindretf. Qed.

Lemma fmap_if A B (f : A -> B) b (m : M A) a :
  f ($) (if b then m else Ret a) = if b then f ($) m else Ret (f a).
Proof. case: ifPn => Hb //; by rewrite fmap_def bindretf. Qed.

(* monadic counterpart of function composition:
   composes a pure function after a monadic function *)
Definition fcomp A B C (f : A -> B) (g : C -> M A) := locked ((M # f) \o g).
Arguments fcomp : simpl never.
Local Notation "f (o) g" := (fcomp f g).

Lemma fcomp_def A B C (f : A -> B) (g : C -> M A) : f (o) g = (M # f) \o g.
Proof. by rewrite /fcomp; unlock. Qed.

Lemma fcompE A B C (f : A -> B) (g : C -> M A) c : (f (o) g) c = f ($) g c.
Proof. by rewrite /fcomp; unlock. Qed.

Lemma fmap_comp A B C (f : A -> B) (g : C -> A) (m : M C) :
  (f \o g) ($) m = f ($) (g ($) m).
Proof. by rewrite 3!fmap_def bindA; rewrite_ bindretf. Qed.

Lemma fcomp_comp A B C D (f : A -> B) (g : C -> A) (m : D -> M C) :
  (f \o g) (o) m = f (o) (g (o) m).
Proof. by rewrite 3!fcomp_def functor_o compA. Qed.

Lemma fmap_bind A B C (f : A -> B) m (g : C -> M A) :
  f ($) (m >>= g) = m >>= (f (o) g).
Proof.
rewrite fcomp_def fmap_def bindA; bind_ext => c; by rewrite compE fmap_def.
Qed.

Lemma skip_fmap A B (f : A -> B) (mb : M B) ma :
  mb >> (f ($) ma) = f ($) (mb >> ma).
Proof. by rewrite fmap_bind fcomp_def. Qed.

(*Lemma rev_map A B (f : A -> B) : rev \o map f = map f \o rev.
Proof.
apply functional_extensionality.
by elim=> // h t /= IH; rewrite !rev_cons IH map_rcons.
Qed.*)

Lemma mfoldl_rev (T R : Type) (f : R -> T -> R) (z : R) (s : seq T -> M (seq T)) :
  foldl f z (o) (rev (o) s) = foldr (fun x => f^~ x) z (o) s.
Proof.
apply functional_extensionality => x; rewrite !fcompE 3!fmap_def !bindA.
bind_ext => ?; by rewrite bindretf /= -foldl_rev.
Qed.

Lemma foldl_revE (T R : Type) (f : R -> T -> R) (z : R) :
  foldl f z \o rev = foldr (fun x : T => f^~ x) z.
Proof. by apply functional_extensionality => s; rewrite -foldl_rev. Qed.

Definition join A (pp : M (M A)) := locked (pp >>= id).

Lemma join_def A (pp : M (M A)) : Join pp = pp >>= id.
Proof.
rewrite bindE.
congr Join.
by rewrite functor_id.
Qed.

(*Lemma join_def A (pp : M (M A)) : join pp = pp >>= id.
Proof. by rewrite /join; unlock. Qed.*)

Lemma join_fmap A B (f : A -> M B) m : Join (f ($) m) = m >>= f.
Proof. by rewrite bindE. Qed.

(* join \o Ret = id *)
(*Lemma join_ret : JoinLaws.join_left_unit (@Ret _) join.
Proof.
move=> A; apply functional_extensionality => ?.
by rewrite compE join_def bindretf.
Qed.

(* join \o fmap Ret = id *)
Lemma join_fmap_ret : JoinLaws.join_right_unit (@Ret _) join (fmap M).
Proof.
move=> A; apply functional_extensionality => ?.
by rewrite compE join_fmap bindmret.
Qed.

(* join \o fmap join = join \o join *)
Lemma join_fmap_join : JoinLaws.join_associativity join (fmap M).
Proof.
move=> A; apply functional_extensionality => mx.
by rewrite 2!compE join_fmap ![in RHS]join_def bindA; rewrite_ join_def.
Qed.*)

(* fmap f \o join = join \o fmap (fmap f) *)
(*Lemma join_naturality_old : JoinLaws.join_functor_commutativity join.
Proof.
move=> A B f; apply functional_extensionality => mma.
rewrite 2!compE fmap_def. [in RHS]join_def bind_fmap. [in LHS]join_def bindA.
by rewrite_ compidf; rewrite_ fmap_def.
Qed.*)

Definition kleisli A B C (m : B -> M C) (n : A -> M B) : A -> M C :=
  (Join) \o (M # m) \o n.
Local Notation "m >=> n" := (kleisli m n).

Lemma fcomp_kleisli A B C D (f : A -> B) (g : C -> M A) (h : D -> M C) :
  f (o) (g >=> h) = (f (o) g) >=> h.
Proof.
by rewrite /kleisli 2!fcomp_def 2!compA join_naturality functor_o compA.
Qed.

Lemma kleisli_fcomp A B C (f : A -> M B) (g : B -> A) (h : C -> M B) :
  ((f \o g) >=> h) = f >=> (g (o) h).
Proof. by rewrite /kleisli fcomp_def functor_o 2!compA. Qed.
Local Notation "m >=> n" := (kleisli m n).

Lemma bind_kleisli A B C m (f : B -> M C) (g : A -> M B) :
  m >>= (f >=> g) = (m >>= g) >>= f.
Proof. by rewrite bindA; bind_ext => a; rewrite /kleisli !compE join_fmap. Qed.

Definition rbind A B (f : A -> M B) (m : M A) : M B := m >>= f.
Local Notation "f =<< m" := (rbind f m).

Definition rkleisli A B C (f : A -> M B) (g : B -> M C) : A -> M C := g >=> f.
Local Notation "n <=< m" := (rkleisli n m).

End fmap_and_join.
Notation "f ($) m" := ((_ # f) m) : mu_scope.
(*Arguments fmap : simpl never.*)
Notation "f (o) g" := (fcomp f g) : mu_scope.
Arguments fcomp : simpl never.
Arguments join {M} {A} : simpl never.
Notation "m >=> n" := (kleisli m n).
Notation "f =<< m" := (rbind f m) : mu_scope.
Notation "n <=< m" := (rkleisli n m) : mu_scope.

Definition mpair {M : monad} {A} (xy : (M A * M A)%type) : M (A * A)%type :=
  let (mx, my) := xy in
  mx >>= (fun x => my >>= fun y => Ret (x, y)).

Lemma naturality_mpair (M : monad) A B (f : A -> B) (g : A -> M A):
  (M # f^`2) \o (mpair \o g^`2) = mpair \o ((M # f) \o g)^`2.
Proof.
apply functional_extensionality => -[a0 a1].
rewrite compE fmap_bind compE [in RHS]/= bind_fmap; bind_ext => a2.
rewrite fcompE fmap_bind compE bind_fmap; bind_ext => a3.
by rewrite fcompE -(compE (M # f^`2)) fmap_ret.
Qed.

Section rep.

Variable M : monad.

Fixpoint rep (n : nat) (mx : M unit) : M unit :=
  if n is n.+1 then mx >> rep n mx else skip.

Lemma repS mx n : rep n.+1 mx = rep n mx >> mx.
Proof.
elim: n => /= [|n IH]; first by rewrite bindmskip bindskipf.
by rewrite bindA IH.
Qed.

Lemma rep1 mx : rep 1 mx = mx. Proof. by rewrite repS bindskipf. Qed.

Lemma rep_addn m n mx : rep (m + n) mx = rep m mx >> rep n mx.
Proof.
elim: m n => [|m IH /=] n; by
  [rewrite bindskipf add0n | rewrite -addnE IH bindA].
Qed.

End rep.

Section MonadCount.

Variable M : monad.
Variable tick : M unit.

Fixpoint hanoi n : M unit :=
  if n is n.+1 then hanoi n >> tick >> hanoi n else skip.

Lemma hanoi_rep n : hanoi n = rep (2 ^ n).-1 tick.
Proof.
elim: n => // n IH /=.
rewrite IH -repS prednK ?expn_gt0 // -rep_addn.
by rewrite -subn1 addnBA ?expn_gt0 // addnn -muln2 -expnSr subn1.
Qed.

End MonadCount.

Module MonadFail.
Record mixin_of (M : monad) : Type := Mixin {
  fail : forall A, M A ;
  (* exceptions are left-zeros of sequential composition *)
  _ : BindLaws.left_zero (@Bind M) fail (* fail A >>= f = fail B *)
}.
Record class_of (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := Monad.Pack (base (class M)).
Module Exports.
Definition Fail (M : t) : forall A, m M A :=
  let: Pack _ (Class _ (Mixin x _)) := M return forall A, m M A in x.
Arguments Fail {M A} : simpl never.
Notation failMonad := t.
Coercion baseType : failMonad >-> monad.
Canonical baseType.
End Exports.
End MonadFail.
Export MonadFail.Exports.

Section fail_lemmas.
Variable (M : failMonad).
Lemma bindfailf : BindLaws.left_zero (@Bind M) (@Fail _).
Proof. by case : M => m [? []]. Qed.
End fail_lemmas.

Lemma fmap_fail {A B} (M : failMonad) (f : A -> B) : (M # f) Fail = Fail :> M _.
Proof. by rewrite fmap_def bindfailf. Qed.

Section guard_assert.

Variable M : failMonad.

Definition guard (b : bool) : M unit := if b then skip else Fail.

(* guard distributes over conjunction *)
Lemma guard_and a b : guard (a && b) = guard a >> guard b.
Proof. move: a b => -[b|b]; by [rewrite bindskipf| rewrite bindfailf]. Qed.

Definition assert {A} (p : pred A) (a : A) : M A :=
  guard (p a) >> Ret a.

Definition bassert {A} (p : pred A) (m : M A) : M A := m >>= assert p.

(* follows from guards commuting with anything *)
Lemma commutativity_of_assertions A q :
  Join \o (M # bassert q) = bassert q \o Join :> (_ -> M A).
Proof.
apply functional_extensionality => x.
by rewrite !compE join_fmap /bassert join_def bindA.
Qed.

(* guards commute with anything *)
Lemma guardsC (HM : BindLaws.right_zero (@Bind M) (@Fail _)) b B (m : M B) :
  (guard b >> m) = (m >>= fun x => guard b >> Ret x).
Proof.
rewrite /guard; case: ifPn => Hb.
  rewrite bindskipf.
  rewrite_ bindskipf.
  by rewrite bindmret.
rewrite_ bindfailf.
by rewrite bindfailf HM.
Qed.

End guard_assert.
Arguments assert {M} {A}.
Arguments guard {M}.

Lemma well_founded_size A : well_founded (fun x y : seq A => size x < size y).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ size) => ? ? /ltP. Qed.

Definition bassert_hylo {M : failMonad} A B
  (f : B -> M (A * B)%type) (p : pred B) (r : forall p f, B -> B -> bool) :=
  forall b, f b = bassert (fun z => r p f z.2 b) (f b).

Definition bassert_size {M : failMonad} A B
  (f : seq B -> M (A * seq B)%type) :=
  @bassert_hylo M _ _ f predT (fun _ _ x y => size x < size y).

(* section 4.3, mu2017 *)
Section unfoldM.

Local Open Scope mu_scope.

Section unfoldM_monad.
Variables (M : monad) (A B : Type).
Variable (r : B -> B -> bool).
Hypothesis wfr : well_founded r.
Variables (p : pred B) (f : B -> M (A * B)%type).

Definition unfoldM' (y : B) (g : forall y' : B, r y' y -> M (seq A)) : M (seq A) :=
  if p y then Ret [::] else f y >>=
    (fun xz => match Bool.bool_dec (r xz.2 y) true with
            | left H => cons xz.1 ($) g xz.2 H
            | right H => Ret [::]
            end).
(* superfluous match to define the "recursive" call,
   to be removed by unfoldME under hypo. *)

Definition unfoldM := Fix wfr (fun _ => _ _) unfoldM'.

End unfoldM_monad.

Section unfoldM_failMonad.
Variables (M : failMonad) (A B' : Type).
Let B := seq B'.
Notation unfoldM := (@unfoldM M A _ _ (@well_founded_size B')).
Variables (p : pred B) (f : B -> M (A * B)%type).

Hypothesis decr_size : bassert_size f.

Lemma unfoldME y : unfoldM p f y =
  if p y then Ret [::]
  else f y >>= (fun xz => cons xz.1 ($) unfoldM p f xz.2).
Proof.
rewrite /unfoldM Fix_eq; last first.
  move => b g g' H; rewrite /unfoldM'; case: ifPn => // pb.
  bind_ext => -[a' b'] /=.
  destruct Bool.bool_dec => //; by rewrite H.
rewrite /unfoldM'; case: ifPn => // py.
rewrite decr_size /bassert 2!bindA; bind_ext => -[a' b'].
rewrite /assert /guard /=; case: ifPn => b'y; last by rewrite !bindfailf.
by rewrite bindskipf 2!bindretf /= b'y.
Qed.

End unfoldM_failMonad.

End unfoldM.
Arguments unfoldM : simpl never.

(* section 4.4, mu2017 *)
Section hyloM.
Variables (M : failMonad) (A B C : Type).
Variables (op : A -> M C -> M C) (e : C) (p : pred B) (f : B -> M (A * B)%type).
Variable seed : forall (p : pred B) (f : B -> M (A * B)%type), B -> B -> bool.

Definition hyloM' (y : B) (g : forall y', seed p f y' y -> M C) : M C :=
  if p y then Ret e else f y >>=
    (fun xz => match Bool.bool_dec (seed p f xz.2 y) true with
            | left H => op xz.1 (g xz.2 H)
            | right H => Ret e
            end).

Hypothesis well_founded_seed : well_founded (seed p f).

Definition hyloM := Fix well_founded_seed (fun _ => M _) hyloM'.

Hypothesis Hdecr_seed : bassert_hylo f p seed.

Lemma hyloME y : hyloM y = if p y then
                             Ret e
                           else
                             f y >>= (fun xz => op xz.1 (hyloM xz.2)).
Proof.
rewrite /hyloM Fix_eq; last first.
  move => b g g' K; rewrite /hyloM'; case: ifPn => // pb.
  bind_ext => -[a' b'] /=.
  destruct Bool.bool_dec => //.
  by rewrite K.
rewrite {1}/hyloM'; case: ifPn => // py.
rewrite Hdecr_seed /bassert !bindA /assert /guard; bind_ext => -[b' a'].
case: ifPn => Hseed; last by rewrite !bindfailf.
by rewrite !bindskipf !bindretf Hseed.
Qed.

End hyloM.
Arguments hyloM {M} {A} {B} {C} _ _ _ _ _.

Module MonadAlt.
Record mixin_of (M : monad) : Type := Mixin {
  alt : forall A, M A -> M A -> M A ;
  _ : forall A, associative (@alt A) ;
  (* composition distributes leftwards over choice *)
  _ : BindLaws.bind_left_distributive (@Bind M) alt
  (* in general, composition does not distribute rightwards over choice *)
  (* NB: no bindDr to accommodate both angelic and demonic interpretations of nondeterminism *)
}.
Record class_of (m : Type -> Type) : Type := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := Monad.Pack (base (class M)).
Module Exports.
Definition Alt M : forall A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _)) := M
  return forall A, m M A -> m M A -> m M A in x.
Arguments Alt {M A} : simpl never.
Notation "'[~p]'" := (@Alt _). (* postfix notation *)
Notation "x '[~]' y" := (Alt x y). (* infix notation *)
Notation altMonad := t.
Coercion baseType : altMonad >-> monad.
Canonical baseType.
End Exports.
End MonadAlt.
Export MonadAlt.Exports.

Section monadalt_lemmas.
Variable (M : altMonad).
Lemma alt_bindDl : BindLaws.bind_left_distributive (@Bind M) [~p].
Proof. by case: M => m [? []]. Qed.
Lemma altA : forall A, associative (@Alt M A).
Proof. by case: M => m [? []]. Qed.

(* TODO: name ok? *)
Lemma naturality_nondeter A B (f : A -> B) p q :
  (M # f) (p [~] q) = (M # f) p [~] (M # f) q :> M _.
Proof. by rewrite 3!fmap_def alt_bindDl. Qed.

Local Open Scope mu_scope.

Lemma alt_fmapDl A B (f : A -> B) (m1 m2 : M A) :
  (M # f) (m1 [~] m2) = f ($) m1 [~] f ($) m2.
Proof. by rewrite 3!fmap_def alt_bindDl. Qed.

End monadalt_lemmas.

Section arbitrary.

Variables (M : altMonad) (A : Type) (def : A).

Definition arbitrary : seq A -> M A :=
  foldr1 (Ret def) (fun x y => x [~] y) \o map Ret.

End arbitrary.
Arguments arbitrary {M} {A}.

(* Sect. 3.1, gibbons2012utp *)
Section subsequences_of_a_list.

Variables (M : altMonad) (A : Type).

Fixpoint subs (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else
  let t' := subs t in
  (cons h) ($) t' [~] t'.

Fixpoint SUBS (s : seq A) : Functor.m (Monad.baseType (MonadAlt.baseType M)) _ :=
  if s isn't h :: t then @Ret (MonadAlt.baseType M) _ [::] else
  let t' : Functor.m (Monad.baseType (MonadAlt.baseType M)) _ := SUBS t in
  Alt (((MonadAlt.baseType M) # (cons h)) t') t'.

Goal subs = SUBS. by []. Abort.

Lemma subs_cons x (xs : seq A) :
  subs (x :: xs) = let t' := subs xs in (cons x ($) t') [~] t'.
Proof. by []. Qed.

Lemma subs_cat (xs ys : seq A) :
  subs (xs ++ ys) = do us <- subs xs; do vs <- subs ys; Ret (us ++ vs).
Proof.
elim: xs ys => [ys |x xs IH ys].
  by rewrite cat0s /= bindretf bindmret.
rewrite {1}[in RHS]/subs fmap_def -/(subs _) alt_bindDl bindA.
Open (X in subs xs >>= X).
  rewrite bindretf.
  rewrite_ cat_cons.
  reflexivity.
rewrite [X in _ = X [~] _](_ : _ = (cons x) ($) (do x0 <- subs xs; do x1 <- subs ys; Ret (x0 ++ x1))); last first.
  rewrite fmap_def bindA.
  bind_ext => x0.
  rewrite bindA.
  by rewrite_ bindretf.
by rewrite -IH cat_cons subs_cons.
Qed.

End subsequences_of_a_list.

(* mu2017, Sect. 3.1 *)
Section permutation_and_insertion.

Variable M : altMonad.

Local Open Scope mu_scope.

Fixpoint insert {A} (a : A) (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [:: a] else
  Ret (a :: h :: t) [~] (cons h ($) insert a t).
Arguments insert : simpl never.

Lemma insertE A (a : A) s :
  insert a s = if s isn't h :: t then Ret [:: a] else
  Ret (a :: h :: t) [~] (cons h ($) insert a t).
Proof. by case: s. Qed.

Fixpoint perm {A} (s : seq A) : M (seq A) :=
  if s isn't h :: t then Ret [::] else perm t >>= insert h.

(* see also netys2017 *)
Lemma insert_map A B (f : A -> B) (a : A) :
  insert (f a) \o map f = map f (o) insert a :> (_ -> M _).
Proof.
apply functional_extensionality; elim => [|y xs IH].
  by rewrite fcompE insertE -(compE (M # map f)) fmap_ret compE insertE.
apply/esym.
rewrite fcompE insertE alt_fmapDl.
(* first branch *)
rewrite -(compE (M # map f)) fmap_ret [ in X in X [~] _ ]/=.
(* second branch *)
rewrite -fmap_comp (_ : map f \o cons y = cons (f y) \o map f) //.
by rewrite fmap_comp -(fcompE (map f)) -IH [RHS]/= insertE.
Qed.

(* see also netys2017 *)
Lemma perm_map A B (f : A -> B) :
  perm \o map f = map f (o) perm :> (seq A -> M (seq B)).
Proof.
apply functional_extensionality; elim => [/=|x xs IH].
  by rewrite fcompE [perm _]/= -(compE (M # map f)) fmap_ret.
by rewrite fcompE [in perm _]/= fmap_bind -insert_map -bind_fmap -fcompE -IH.
Qed.

End permutation_and_insertion.
Arguments insert {M} {A} : simpl never.
Arguments perm {M} {A}.

Section perm_filter.
Variable M : altMonad.
Hypothesis altmm : forall A, idempotent (@Alt _ A : M A -> M A -> M A).

Local Open Scope mu_scope.

Variables (A : Type) (p : pred A).

Lemma filter_insertN a : ~~ p a ->
  forall s, (filter p (o) insert a) s = Ret (filter p s) :> M _.
Proof.
move=> pa; elim => [|h t IH].
  by rewrite fcompE insertE -(compE (M # _)) fmap_ret /= (negbTE pa).
rewrite fcompE insertE alt_fmapDl.
rewrite -(compE (M # _)) fmap_ret [in X in X [~] _]/= (negbTE pa).
case: ifPn => ph.
- rewrite -fmap_comp (_ : filter p \o cons h = cons h \o filter p); last first.
    apply functional_extensionality => x /=; by rewrite ph.
  rewrite fmap_comp.
  move: (IH); rewrite fcompE => ->.
  by rewrite fmap_retE altmm /= ph.
- rewrite -fmap_comp (_ : filter p \o cons h = filter p); last first.
    apply functional_extensionality => x /=; by rewrite (negbTE ph).
  move: (IH); rewrite fcompE => -> /=; by rewrite (negbTE ph) altmm.
Qed.

Lemma filter_insertT a : p a ->
  filter p (o) insert a = insert a \o filter p :> (_ -> M _).
Proof.
move=> pa; apply functional_extensionality => s; elim: s => [|h t IH].
  by rewrite fcompE !insertE fmap_retE /= pa.
rewrite fcompE [in RHS]/=; case: ifPn => ph.
- rewrite [in RHS]insertE.
  move: (IH); rewrite [in X in X -> _]/= => <-.
  rewrite [in LHS]insertE alt_fmapDl; congr (_ [~] _).
    by rewrite fmap_retE /= pa ph.
  rewrite !fmap_def /= fcompE bind_fmap bindA.
  rewrite_ bindretf.
  by rewrite /= ph.
- rewrite [in LHS]insertE alt_fmapDl.
  rewrite -[in X in _ [~] X = _]fmap_comp.
    rewrite (_ : (filter p \o cons h) = filter p); last first.
    apply functional_extensionality => x /=; by rewrite (negbTE ph).
  move: (IH); rewrite fcompE => ->.
  rewrite fmap_retE /= pa (negbTE ph) [in RHS]insertE; case: (filter _ _) => [|h' t'].
    by rewrite insertE altmm.
  by rewrite !insertE altA altmm.
Qed.

(* netys2017 *)
Lemma perm_filter : perm \o filter p = filter p (o) perm :> (_ -> M _).
Proof.
apply functional_extensionality; elim=> [|h t /= IH].
  by rewrite fcompE fmap_retE.
case: ifPn => ph.
  rewrite [in LHS]/= IH [in LHS]fcomp_def compE [in LHS]bind_fmap.
  rewrite [in RHS]fcomp_def compE [in RHS]fmap_bind; bind_ext => s.
  by rewrite filter_insertT.
rewrite fcompE fmap_bind IH fcompE fmap_def; bind_ext => s.
by rewrite filter_insertN.
Qed.

End perm_filter.

Module MonadAltCI.
Record mixin_of (M : Type -> Type) (op : forall A, M A -> M A -> M A) : Type := Mixin {
  _ : forall A, idempotent (op A) ;
  _ : forall A, commutative (op A)
}.
Record class_of (m : Type -> Type) : Type := Class {
  base : MonadAlt.class_of m ;
  mixin : mixin_of (@Alt (MonadAlt.Pack base)) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := MonadAlt.Pack (base (class M)).
Module Exports.
Notation altCIMonad := t.
Coercion baseType : altCIMonad >-> altMonad.
Canonical baseType.
End Exports.
End MonadAltCI.
Export MonadAltCI.Exports.

Section altci_lemmas.
Variable (M : altCIMonad).
Lemma altmm : forall A, idempotent (@Alt _ A : M A -> M A -> M A).
Proof. by case: M => m [? []]. Qed.
Lemma altC : forall A, commutative (@Alt _ A : M A -> M A -> M A).
Proof. by case: M => m [? []]. Qed.
Lemma altCA A : @left_commutative (M A) (M A) (fun x y => x [~] y).
Proof. move=> x y z. by rewrite altA altC altA altC (altC z). Qed.
Lemma altAC A : @right_commutative (M A) (M A) (fun x y => x [~] y).
Proof. move=> x y z; by rewrite altC altA (altC x). Qed.
Lemma altACA A : @interchange (M A) (fun x y => x [~] y) (fun x y => x [~] y).
Proof. move=> x y z t; rewrite !altA; congr (_ [~] _); by rewrite altAC. Qed.
End altci_lemmas.

(* mu2017, Sect. 3.2, see also netsys2017 *)
Section altci_insert.
Variables (M : altCIMonad) (A : Type) (a : A).

Local Open Scope mu_scope.

Lemma insert_rcons a' s :
  insert a (rcons s a') =
    Ret (s ++ [:: a'; a]) [~] (rcons^~ a' ($) insert a s) :> M _.
Proof.
elim: s a' => [a'|s1 s2 IH a'].
  rewrite cat0s fmap_retE insertE altC; congr (_ [~] _).
  by rewrite insertE fmap_retE.
rewrite [in LHS]/= insertE IH.
rewrite naturality_nondeter fmap_retE.
rewrite naturality_nondeter fmap_retE.
by rewrite -!fmap_comp altCA.
Qed.

Lemma rev_insert : rev (o) insert a = insert a \o rev :> (_ -> M _).
Proof.
apply functional_extensionality; elim => [|h t IH].
  by rewrite fcompE insertE fmap_retE.
rewrite fcompE insertE compE alt_fmapDl fmap_retE compE [in RHS]rev_cons insert_rcons.
rewrite rev_cons -cats1 rev_cons -cats1 -catA; congr (_ [~] _).
move: IH; rewrite fcompE [X in X -> _]/= => <-.
rewrite -!fmap_comp; congr (_ ($) insert a t).
apply functional_extensionality => s; by rewrite /= -rev_cons.
Qed.

End altci_insert.

Module MonadNondet.
Record mixin_of (M : failMonad) (a : forall A, M A -> M A -> M A) : Type :=
  Mixin { _ : BindLaws.left_id (@Fail M) a ;
          _ : BindLaws.right_id (@Fail M) a
}.
Record class_of (m : Type -> Type) : Type := Class {
  base : MonadFail.class_of m ;
  base2 : MonadAlt.mixin_of (Monad.Pack (MonadFail.base base)) ;
  mixin : @mixin_of (MonadFail.Pack base) (MonadAlt.alt base2)
}.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := MonadFail.Pack (base (class M)).
Module Exports.
Notation nondetMonad := t.
Coercion baseType : nondetMonad >-> failMonad.
Canonical baseType.
Definition alt_of_nondet (M : nondetMonad) : altMonad :=
  MonadAlt.Pack (MonadAlt.Class (base2 (class M))).
Canonical alt_of_nondet.
End Exports.
End MonadNondet.
Export MonadNondet.Exports.

Section nondet_lemmas.
Variable (M : nondetMonad).
Lemma altmfail : BindLaws.right_id (@Fail M) [~p].
Proof. by case: M => m [[? ?] [? ? ?] [? ?]]. Qed.
Lemma altfailm : BindLaws.left_id (@Fail M) [~p]. (* NB: not used? *)
Proof. by case: M => m [[? ?] [? ? ?] [? ?]]. Qed.
End nondet_lemmas.

Lemma test_canonical (M : nondetMonad) A (a : M A) (b : A -> M A) :
  a [~] (Fail >>= b) = a [~] Fail.
Proof.
Set Printing All.
Unset Printing All.
by rewrite bindfailf.
Abort.

Section nondet_big.
Variables (M : nondetMonad) (A : Type).
Canonical alt_monoid :=
  Monoid.Law (@altA (alt_of_nondet M) A) (@altfailm _ _) (@altmfail _ _).

Lemma test_bigop n : \big[Alt/Fail]_(i < n) (Fail : M A) = Fail.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= IH altmfail.
Qed.

End nondet_big.

(* gibbons2011icfp, Sect. 4.4 *)

Section select.
Variables (M : nondetMonad) (A : Type).
Implicit Types s : seq A.

Fixpoint select s : M (A * seq A)%type :=
  if s isn't h :: t then Fail else
  (Ret (h, t) [~] do x <- select t; Ret (x.1, h :: x.2)).

Local Obligation Tactic := idtac.
(* variant of select that keeps track of the length, useful to write perms *)
Program Fixpoint tselect s : M (A * (size s).-1.-tuple A)%type :=
  if s isn't h :: t then Fail else
  (Ret (h, @Tuple (size t) A t _) [~]
  do x <- tselect t; Ret (x.1, @Tuple (size t) A _ _ (* h :: x.2 *))).
Next Obligation. by []. Defined.
Next Obligation.
move=> s h [|h' t] hts [x1 x2]; [exact: [::] | exact: (h :: x2)].
Defined.
Next Obligation.
move=> s h [|h' t] hts [x1 x2] //=; by rewrite size_tuple.
Defined.
Next Obligation. by []. Defined.

Lemma tselect_nil : tselect [::] = Fail. Proof. by []. Qed.

Lemma tselect1 a : tselect [:: a] = Ret (a, [tuple]).
Proof.
rewrite /= bindfailf altmfail /tselect_obligation_1 /= tupleE /nil_tuple.
do 3 f_equal; exact: proof_irrelevance.
Qed.

Program Definition tselect_cons_statement a t (_ : t <> nil) :=
  tselect (a :: t) = Ret (a, @Tuple _ _ t _) [~]
                    do x <- tselect t; Ret (x.1, @Tuple _ _ (a :: x.2) _).
Next Obligation. by []. Defined.
Next Obligation.
move=> a t t0 [x1 x2].
rewrite /= size_tuple prednK //; by destruct t.
Defined.

Program Lemma tselect_cons a t (Ht : t <> nil) : tselect_cons_statement a Ht.
Proof.
rewrite /tselect_cons_statement [in LHS]/=; congr (_ [~] _).
bind_ext; case=> x1 x2 /=.
do 2 f_equal; apply val_inj => /=; by destruct t.
Qed.

Local Open Scope mu_scope.

Lemma selectE s : select s =
  (fun xy => (xy.1, tval xy.2)) ($) tselect s :> M (A * seq A)%type.
Proof.
elim: s => [|h [|h' t] IH].
- by rewrite fmap_def bindfailf.
- by rewrite tselect1 fmap_retE /= bindfailf altmfail.
- rewrite {1}/select -/(select (h' :: t)) IH [in RHS]alt_fmapDl fmap_retE; congr (_ [~] _).
  rewrite bind_fmap fmap_bind; bind_ext => -[x1 x2].
  by rewrite fcompE fmap_retE.
Qed.

Lemma decr_size_select : bassert_size select.
Proof.
case => [|h t]; first by rewrite !selectE fmap_fail /bassert bindfailf.
rewrite /bassert selectE bind_fmap fmap_def; bind_ext => -[x y].
by rewrite /assert /guard /= size_tuple ltnS leqnn bindskipf.
Qed.

End select.
Arguments select {M} {A}.
Arguments tselect {M} {A}.

Section permutations.
Variables (M : nondetMonad) (A : Type).
Implicit Types s : seq A.

Local Obligation Tactic := idtac.
Program Definition perms' s
  (f : forall s', size s' < size s -> M (seq A)) : M (seq A) :=
  if s isn't h :: t then Ret [::] else
    do x <- tselect (h :: t); do y <- f x.2 _; Ret (x.1 :: y).
Next Obligation.
move=> s H h t hts [y ys]; by rewrite size_tuple -hts ltnS leqnn.
Qed.
Next Obligation. by []. Qed.

Definition perms : seq A -> M (seq A) :=
  Fix (@well_founded_size _) (fun _ => M _) perms'.

Lemma tpermsE s : perms s = if s isn't h :: t then Ret [::] else
  do x <- tselect (h :: t); do y <- perms x.2; Ret (x.1 :: y).
Proof.
rewrite {1}/perms Fix_eq //; [by case: s|move=> s' f g H].
by rewrite /perms'; destruct s' => //; bind_ext=> x; rewrite H.
Qed.

Lemma permsE s : perms s = if s isn't h :: t then Ret [::] else
  do x <- select (h :: t); do y <- perms x.2; Ret (x.1 :: y).
Proof.
rewrite tpermsE; case: s => // h t.
by rewrite selectE bind_fmap.
Qed.

End permutations.
Arguments perms {M} {A}.

(* from section 4.3 of mu2017, definition of perms using unfoldM *)
Section mu_perm.
Variables (A : Type) (M : nondetMonad).

Definition mu_perm : seq A -> M (seq A) :=
  unfoldM (@well_founded_size _) (@nilp _) select.

Lemma mu_permE s : mu_perm s = if s isn't h :: t then Ret [::]
  else do a <- select (h :: t) ; do b <- mu_perm a.2; Ret (a.1 :: b).
Proof.
rewrite /mu_perm unfoldME; last exact: decr_size_select.
case: s => // h t; rewrite (_ : nilp _ = false) //.
by bind_ext => -[x1 x2] ; rewrite fmap_def.
Qed.

Lemma perms_mu_perm s : perms s = mu_perm s.
Proof.
move Hn : (size s) => n.
elim: n s Hn => [|n IH [//|h t] /= [tn]].
  case => //; by rewrite permsE mu_permE.
rewrite tpermsE mu_permE selectE bind_fmap; bind_ext => -[a b].
by rewrite IH // size_tuple.
Qed.

End mu_perm.
Arguments mu_perm {A} {M}.

Module SyntaxNondet.

Inductive t : Type -> Type :=
| ret : forall A, A -> t A
| bind : forall B A, t B -> (B -> t A) -> t A
| fail : forall A, t A
| alt : forall A, t A -> t A -> t A.

Fixpoint denote {M : nondetMonad} {A} (m : t A) : M A :=
  match m with
  | ret A a => Ret a
  | bind A B m f => denote m >>= (fun x => denote (f x))
  | fail A => Fail
  | alt A m1 m2 => denote m1 [~] denote m2
  end.

Module Exports.
Notation nondetSyntax := t.
Notation ndAlt := alt.
Notation ndRet := ret.
Notation ndBind := bind.
Notation ndFail := fail.
Notation ndDenote := denote.
End Exports.
End SyntaxNondet.
Export SyntaxNondet.Exports.

Module MonadExcept.
Record mixin_of (M : failMonad) : Type := Mixin {
  catch : forall A, M A -> M A -> M A ;
  (* monoid *)
  _ : forall A, right_id Fail (@catch A) ;
  _ : forall A, left_id Fail (@catch A) ;
  _ : forall A, associative (@catch A) ;
  (* unexceptional bodies need no handler *)
  _ : forall A x, left_zero (Ret x) (@catch A)
  (* NB: left-zero of sequential composition inherited from failMonad *)
}.
Record class_of (m : Type -> Type) := Class {
  base : MonadFail.class_of m ;
  mixin : mixin_of (MonadFail.Pack base) }.
Record t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType M := MonadFail.Pack (base (class M)).
Definition monadType M := Monad.Pack (MonadFail.base (base (class M))).
Module Exports.
Definition Catch (M : t) : forall A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _)) := M
  return forall A, m M A -> m M A -> m M A in x.
Arguments Catch {M A} : simpl never.
Notation exceptMonad := t.
Coercion baseType : exceptMonad >-> failMonad.
Canonical baseType.
Canonical monadType.
End Exports.
End MonadExcept.
Export MonadExcept.Exports.

Section except_lemmas.
Variables (M : exceptMonad).
Lemma catchfailm : forall A, left_id Fail (@Catch M A).
Proof. by case: M => m [? []]. Qed.
Lemma catchmfail : forall A, right_id Fail (@Catch M A). (* NB: not used? *)
Proof. by case: M => m [? []]. Qed.
Lemma catchret : forall A x, left_zero (Ret x) (@Catch M A).
Proof. by case: M => m [? []]. Qed.
Lemma catchA : forall A, associative (@Catch M A). (* NB: not used? *)
Proof. by case: M => m [? []]. Qed.
End except_lemmas.

Section fastproduct.

Definition product (s : seq nat) := foldr muln 1 s.

Lemma product0 s : O \in s -> product s = O.
Proof.
elim: s => //= h t ih; rewrite inE => /orP[/eqP <-|/ih ->];
  by rewrite ?muln0 ?mul0n.
Qed.

Section work.

Variable M : failMonad.

Definition work s : M nat :=
  if O \in s then Fail else Ret (product s).

(* work refined to eliminate multiple traversals *)
Lemma workE :
  let next := fun n mx => if n == 0 then Fail else (*muln n ($) mx*) (M # muln n) mx in
  work = foldr next (Ret 1).
Proof.
apply foldr_universal => // h t; case: ifPn => [/eqP -> //| h0].
by rewrite /work inE eq_sym (negbTE h0) [_ || _]/= fmap_if fmap_fail.
Qed.

End work.
Arguments work {M}.

Variable M : exceptMonad.

Definition fastprod s : M _ := Catch (work s) (Ret O).

(* fastprod is pure, never throwing an unhandled exception *)
Lemma fastprodE s : fastprod s = Ret (product s).
Proof.
rewrite /fastprod /work fun_if if_arg catchfailm.
by rewrite catchret; case: ifPn => // /product0 <-.
Qed.

End fastproduct.
