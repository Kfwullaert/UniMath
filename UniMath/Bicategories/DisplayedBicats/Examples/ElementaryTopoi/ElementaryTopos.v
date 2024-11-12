Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.exponentials.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.terminal.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.binproducts.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.pullbacks.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.lex.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.subobjectclassifier.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.exponentials.

Local Open Scope cat.

Definition disp_bicat_toposes_over_lex
  : disp_bicat (total_bicat disp_bicat_lex)
  := disp_dirprod_bicat
       disp_bicat_subobjectclassifier_over_lex
       disp_bicat_exponentials_over_lex.

Definition disp_bicat_toposes
  : disp_bicat bicat_of_cats.
Proof.
  use sigma_bicat.
  - exact disp_bicat_lex.
  - exact disp_bicat_toposes_over_lex.
Defined.

Lemma disp_2cells_is_contr_toposes
  : disp_2cells_iscontr disp_bicat_toposes.
Proof.
  apply disp_bicat_of_sigma_iscontr.
  - exact disp_2cells_is_contr_lex.
  - apply disp_dirprod_bicat_of_dirprod_iscontr.
    + exact disp_2cells_is_contr_subobjectclassifier_over_lex.
    + exact disp_2cells_is_contr_exponentials_over_lex.
Qed.
