Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalAdjunction.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Import DispBicat.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrows.core.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section MakeDisplayedLeftUniversalArrowIfPropositional.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          (LUR : left_universal_arrow R)
          {D1 : disp_bicat B1} {D2 : disp_bicat B2}
          (RR : disp_psfunctor D1 D2 R)
          (D1_2cells_prop : disp_2cells_isaprop D1)
          (D2_2cells_prop : disp_2cells_isaprop D2).

  Let L : B2 -> B1 := pr1 LUR.
  Let η : ∏ x : B2, B2 ⟦ x, R (L x) ⟧ := pr12 LUR.
  Let adj :  ∏ (x : B2) (y : B1), adj_equivalence_of_cats (left_universal_arrow_functor R x y η)
      := pr22 LUR.

  Context (LL : ∏ x : B2, D2 x → D1 (L x))
    (ηη : ∏ (x : B2) (xx : D2 x),  xx -->[η x] (RR _ (LL _ xx))).

  Context (LL_mor : ∏ x xx y yy f (ff : xx -->[ f] RR y yy),
              LL x xx -->[ right_adjoint ((pr22 LUR) x y) f] yy).
  Context (LL_2cell : ∏ x xx y yy (f1 f2 : B2 ⟦ x, R y ⟧)
                      (ff1 : xx -->[ f1] RR y yy) (ff2 : xx -->[ f2] RR y yy)
                      (α : f1 ==> f2),
              ff1 ==>[α] ff2
              → (LL_mor x xx y yy f1 ff1) ==>[(# (right_adjoint ((pr22 LUR) x y)))%cat α]
                  (LL_mor x xx y yy f2 ff2)).
  Context (LL_unit : ∏ x xx y yy f ff,
              ff ==>[adjunit (adj x y) f]
                (LL_mor x xx y yy (η x · (# R)%cat f) (ηη x xx ;; disp_psfunctor_mor D1 D2 R RR ff))).

  Context (LL_unit_inv : ∏ x xx y yy f ff,
        (LL_mor x xx y yy ((pr12 LUR) x · (# R)%cat f) (ηη x xx ;; disp_psfunctor_mor D1 D2 R RR ff))
          ==>[inv_from_z_iso (unit_pointwise_z_iso_from_adj_equivalence (adj x y) _)] ff).

  Context (LL_counit : ∏ x xx y yy f ff,
              (ηη x xx ;; disp_psfunctor_mor D1 D2 R RR (LL_mor x xx y yy f ff))
                ==>[adjcounit (adj x y) f] ff).

  Context (LL_counit_inv : ∏ x xx y yy f ff,
              ff ==>[inv_from_z_iso (counit_pointwise_z_iso_from_adj_equivalence (adj x y) _)]
                (ηη x xx ;; disp_psfunctor_mor D1 D2 R RR (LL_mor x xx y yy f ff))).

  Definition make_disp_functor_data_if_prop
             {x : B2}
             (xx : D2 x)
             {y : B1}
             (yy : D1 y)
    : disp_functor_data
        (right_adjoint ((pr22 LUR) x y))
        (disp_hom xx (RR y yy))
        (disp_hom (LL x xx) yy).
  Proof.
    simple refine (_ ,, _).
    - exact (LL_mor x xx y yy).
    - exact (LL_2cell x xx y yy).
  Defined.

  Definition make_disp_functor_if_prop
             {x : B2}
             (xx : D2 x)
             {y : B1}
             (yy : D1 y)
    : disp_functor
        (right_adjoint ((pr22 LUR) x y))
        (disp_hom xx (RR y yy))
        (disp_hom (LL x xx) yy).
  Proof.
    simple refine (make_disp_functor_data_if_prop xx yy ,, _).
    abstract (split ; intros ; apply D1_2cells_prop).
  Defined.

  Definition make_disp_univ_arrow_if_prop_equiv
             {x : B2}
             (xx : D2 x)
             {y : B1}
             (yy : D1 y)
    : is_equiv_over
        (left_universal_arrow_functor R x y (pr12 LUR),, (pr22 LUR) x y)
        (disp_left_universal_arrow_functor LUR RR (LL,, ηη) xx yy).
  Proof.
    simple refine (((_ ,, (_,,_)) ,, _) ,, (_ ,, _)).
    - exact (make_disp_functor_if_prop xx yy).
    - simple refine (_ ,, _).
      + exact (LL_unit x xx y yy).
      + abstract (intro ; intros ; apply D1_2cells_prop).
    - simple refine (_ ,, _).
      + exact (LL_counit x xx y yy).
      + abstract (
            intro ; intros ;
            apply D2_2cells_prop).
    - abstract (split ; intro ; intros;
                [ apply D2_2cells_prop
                | apply D1_2cells_prop ]).
    - intros f ff.
      simple refine (_ ,, (_ ,, _)).
      + exact (LL_unit_inv x xx y yy f ff).
      + abstract (apply D1_2cells_prop).
      + abstract (apply D1_2cells_prop).
    - intros f ff.
      simple refine (_ ,, (_ ,, _)).
      + exact (LL_counit_inv x xx y yy f ff).
      + abstract (apply D2_2cells_prop).
      + abstract (apply D2_2cells_prop).
  Defined.

  Definition make_disp_univ_arrow_if_prop
    : disp_left_universal_arrow LUR RR.
  Proof.
    refine (LL ,, ηη ,, _).
    intros x xx y yy.
    exact (make_disp_univ_arrow_if_prop_equiv xx yy).
  Defined.

End MakeDisplayedLeftUniversalArrowIfPropositional.
