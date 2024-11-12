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

Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

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

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Lemma dirprod_iscontr {A₁ A₂ : UU}
  (c₁ : iscontr A₁) (c₂ : iscontr A₂)
  : iscontr (dirprod A₁ A₂).
Proof.
  exists (pr1 c₁ ,, pr1 c₂).
  intro ; use total2_paths2.
  - apply c₁.
  - apply c₂.
Qed.

Section MakeDisplayedLeftUniversalArrowOfBinProductIfContractible.

  Context {B1 B2 : bicat}
          {R : psfunctor B1 B2}
          (LUR : left_universal_arrow R)
          {D1 E1 : disp_bicat B1} {D2 E2 : disp_bicat B2}
          (RR_D : disp_psfunctor D1 D2 R)
          (RR_E : disp_psfunctor E1 E2 R).


  Let DE_1 := disp_dirprod_bicat D1 E1.
  Let DE_2 := disp_dirprod_bicat D2 E2.

  Require Import UniMath.Bicategories.DisplayedBicats.ProductDispBiequiv.
  Context
    (D1_2cells_contr : disp_2cells_iscontr D1)
      (D2_2cells_contr : disp_2cells_iscontr D2)
      (E1_2cells_contr : disp_2cells_iscontr E1)
      (E2_2cells_contr : disp_2cells_iscontr E2).

  Let RR : disp_psfunctor DE_1 DE_2 R.
  Proof.
    use prod_disp_psfunctor.
    - exact (disp_2cells_isaprop_from_disp_2cells_iscontr _ D2_2cells_contr).
    - exact (disp_2cells_isgroupoid_from_disp_2cells_iscontr _ D2_2cells_contr).
    - exact (disp_2cells_isaprop_from_disp_2cells_iscontr _ E2_2cells_contr).
    - exact (disp_2cells_isgroupoid_from_disp_2cells_iscontr _ E2_2cells_contr).
    - exact RR_D.
    - exact RR_E.
  Defined.

  Definition make_disp_univ_arrow_of_binprod_if_contr
    (dlur₁ : disp_left_universal_arrow LUR RR_D)
    (dlur₂ : disp_left_universal_arrow LUR RR_E)
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_univ_arrow_if_contr.
    - intro ; intros ; apply dirprod_iscontr.
      + apply D1_2cells_contr.
      + apply E1_2cells_contr.
    - intro ; intros ; apply dirprod_iscontr.
      + apply D2_2cells_contr.
      + apply E2_2cells_contr.
    - intro ; apply dirprodf.
      + apply dlur₁.
      + apply dlur₂.
    - intro ; intros ; split.
      + apply dlur₁.
      + apply dlur₂.
    - intro ; intros ; split.
      + apply dlur₁, ff.
      + apply dlur₂, ff.
  Defined.

End MakeDisplayedLeftUniversalArrowOfBinProductIfContractible.
