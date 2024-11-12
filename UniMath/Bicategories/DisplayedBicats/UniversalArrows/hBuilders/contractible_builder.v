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
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrows.propositional_builder.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrows.groupoidal_and_propositional_builder.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section MakeDisplayedLeftUniversalArrowIfContractible.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          (LUR : left_universal_arrow R)
          {D1 : disp_bicat B1} {D2 : disp_bicat B2}
          (RR : disp_psfunctor D1 D2 R)
          (D1_2cells_contr : disp_2cells_iscontr D1)
          (D2_2cells_contr : disp_2cells_iscontr D2).

  Let L : B2 -> B1 := pr1 LUR.
  Let η : ∏ x : B2, B2 ⟦ x, R (L x) ⟧ := pr12 LUR.
  Let adj :  ∏ (x : B2) (y : B1), adj_equivalence_of_cats (left_universal_arrow_functor R x y η)
      := pr22 LUR.

  Context (LL : ∏ x : B2, D2 x → D1 (L x))
    (ηη : ∏ (x : B2) (xx : D2 x),  xx -->[η x] (RR _ (LL _ xx))).

  Context (LL_mor : ∏ x xx y yy f (ff : xx -->[ f] RR y yy),
              LL x xx -->[ right_adjoint ((pr22 LUR) x y) f] yy).

  Definition make_disp_univ_arrow_if_contr
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_univ_arrow_if_groupoid_and_prop.
    - exact (disp_2cells_isgroupoid_from_disp_2cells_iscontr _ D1_2cells_contr).
    - exact (disp_2cells_isgroupoid_from_disp_2cells_iscontr _ D2_2cells_contr).
    - exact (disp_2cells_isaprop_from_disp_2cells_iscontr _ D1_2cells_contr).
    - exact (disp_2cells_isaprop_from_disp_2cells_iscontr _ D2_2cells_contr).
    - exact LL.
    - exact ηη.
    - exact LL_mor.
    - abstract (intro ; intros ; apply D1_2cells_contr).
    - abstract (intro ; intros ; apply D1_2cells_contr).
    - abstract (intro ; intros ; apply D2_2cells_contr).
  Defined.

End MakeDisplayedLeftUniversalArrowIfContractible.
