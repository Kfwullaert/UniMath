Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.Equalizers.
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
 7. Categories with a chosen equalizers
 *)
Definition disp_bicat_chosen_equalizers
  : disp_bicat bicat_of_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, Equalizers C).
  - exact (λ C₁ C₂ BP₁ BP₂ F, preserves_chosen_equalizers_eq F BP₁ BP₂).
  - exact (λ C T, identity_preserves_chosen_equalizers_eq T).
  - exact (λ _ _ _ _ _ _ _ _ PF PG, composition_preserves_chosen_equalizers_eq PF PG).
Defined.

Definition cat_with_chosen_equalizers
  : bicat
  := total_bicat disp_bicat_chosen_equalizers.

(**
 8. Categories that have equalizers
 *)
Definition disp_bicat_have_equalizers
  : disp_bicat bicat_of_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, hasEqualizers (C := C)).
  - exact (λ C₁ C₂ _ _ F, preserves_equalizer F).
  - exact (λ C _, identity_preserves_equalizer _).
  - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_equalizer HF HG).
Defined.

Definition cat_with_equalizers
  : bicat
  := total_bicat disp_bicat_have_equalizers.

(** 9. Homotopy levels of each type of 2-cells *)
Lemma disp_2cells_is_contr_have_equalizers
  : disp_2cells_iscontr disp_bicat_have_equalizers.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.

Lemma disp_2cells_is_contr_chosen_equalizers
  : disp_2cells_iscontr disp_bicat_chosen_equalizers.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.

(***************)
