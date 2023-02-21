Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.Bicategories.Core.Bicat.

Require Import UniMath.Bicategories.DaggerCategories.Core.
Require Import UniMath.Bicategories.DaggerCategories.BicatOfDaggerCats.

Local Open Scope cat.

Section Lemmas.

  Definition dagger_injective
             {C : category} (dag : dagger C)
             {x y : C}
             (f g : C⟦x,y⟧)
    : pr1 dag _ _ f = pr1 dag _ _ g -> f = g.
  Proof.
    intro p.
    refine (_ @ maponpaths (pr1 dag y x) p @ _).
    - apply pathsinv0, dagger_to_law_idemp.
    - apply dagger_to_law_idemp.
  Qed.

  Lemma dagger_transformation_equality
        {C D : category}
        {F G : functor C D}
        {dagC : dagger C} {dagD : dagger D}
        {dagF : is_dagger_functor dagC dagD F}
        {dagG : is_dagger_functor dagC dagD G}
        (α β : (hom _ _)⟦make_dagger_functor dagF, make_dagger_functor dagG⟧)
    : (∏ x : C, pr11 α x = pr11 β x) -> α = β.
  Proof.
    intro p.
    use total2_paths_f.
    2: apply isapropunit.
    apply (nat_trans_eq D).
    exact p.
  Qed.

End Lemmas.
