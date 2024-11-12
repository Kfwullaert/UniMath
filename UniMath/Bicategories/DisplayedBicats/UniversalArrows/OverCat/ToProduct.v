Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.FunctorCategory.

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

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
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
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrows.contractible_builder.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.

Local Open Scope cat.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

Section LocallyContrDirProd.

  Context (LUR : left_universal_arrow univ_cats_to_cats).
  Context {D₁ D₂ : disp_bicat bicat_of_cats}
    (D_contr₁ : disp_2cells_iscontr D₁)
    (D_contr₂ : disp_2cells_iscontr D₂).

  Let D_contr : disp_2cells_iscontr (disp_dirprod_bicat D₁ D₂).
  Proof.
  Admitted.

  Context (LUR₁ : disp_left_universal_arrow LUR (disp_psfunctor_on_cat_to_univ_cat _ (disp_2cells_isaprop_from_disp_2cells_iscontr _ D_contr₁))).
  Context (LUR₂ : disp_left_universal_arrow LUR (disp_psfunctor_on_cat_to_univ_cat _ (disp_2cells_isaprop_from_disp_2cells_iscontr _ D_contr₂))).

  Definition make_disp_left_universal_arrow_if_contr_CAT_on_dirprod
    : disp_left_universal_arrow
        LUR
        (disp_psfunctor_on_cat_to_univ_cat _ (disp_2cells_isaprop_from_disp_2cells_iscontr _ D_contr)).
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT.
    - exact (λ _ d, pr1 LUR₁ _ (pr1 d) ,, pr1 LUR₂ _ (pr2 d)).
    - exact (λ _ d, pr12 LUR₁ _ (pr1 d) ,, pr12 LUR₂ _ (pr2 d)).
    - intros C₁ d₁ C₂ d₂ f ff ; split ; simpl.
      + apply LUR₁, ff.
      + apply LUR₂, ff.
  Defined.

End LocallyContrDirProd.
