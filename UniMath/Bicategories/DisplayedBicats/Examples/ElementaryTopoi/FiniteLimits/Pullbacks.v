Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

Local Open Scope cat.

(**
 11. Categories that have pullbacks
 *)
Definition disp_bicat_pullbacks
  : disp_bicat bicat_of_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, Pullbacks C).
  - exact (λ C₁ C₂ _ _ F, preserves_pullback F).
  - exact (λ C _, identity_preserves_pullback _).
  - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_pullback HF HG).
Defined.

Definition cat_with_pullbacks
  : bicat
  := total_bicat disp_bicat_pullbacks.

(**
 10. Categories with a chosen pullbacks
 *)
Definition disp_bicat_chosen_pullbacks
  : disp_bicat bicat_of_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, Pullbacks C).
  - exact (λ C₁ C₂ BP₁ BP₂ F, preserves_chosen_pullbacks_eq F BP₁ BP₂).
  - exact (λ C T, identity_preserves_chosen_pullbacks_eq T).
  - exact (λ _ _ _ _ _ _ _ _ PF PG, composition_preserves_chosen_pullbacks_eq PF PG).
Defined.

Definition cat_with_chosen_pullbacks
  : bicat
  := total_bicat disp_bicat_chosen_pullbacks.

(**
 11. Categories that have pullbacks
 *)
Definition disp_bicat_have_pullbacks
  : disp_bicat bicat_of_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, hasPullbacks C).
  - exact (λ C₁ C₂ _ _ F, preserves_pullback F).
  - exact (λ C _, identity_preserves_pullback _).
  - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_pullback HF HG).
Defined.

Definition cat_with_having_pullbacks
  : bicat
  := total_bicat disp_bicat_have_pullbacks.

(* 12. Homotopy levels of each type of 2-cells *)
Lemma disp_2cells_is_contr_pullbacks
  : disp_2cells_iscontr disp_bicat_pullbacks.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.

Lemma disp_2cells_is_contr_have_pullbacks
  : disp_2cells_iscontr disp_bicat_have_pullbacks.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.

Lemma disp_2cells_is_contr_chosen_pullbacks
  : disp_2cells_iscontr disp_bicat_chosen_pullbacks.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.
