Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FiniteLimits.Terminal.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FiniteLimits.ProductsBin.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FiniteLimits.Pullbacks.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FinitelyComplete.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.SubObjectClassifier.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.Exponentials.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.ElementaryTopos.

Local Open Scope cat.

Definition disp_bicat_subobjectclassifier_over_lex
  : disp_bicat (total_bicat disp_bicat_lex).
Proof.
  use disp_subbicat.
  - exact (λ C, subobject_classifier (pr112 C)).
  - exact (λ C₁ C₂ Ω₁ Ω₂ F, preserves_subobject_classifier (pr1 F) (pr112 C₁) (pr112 C₂) (pr212 F)).
  - intro ; intros ; apply identity_preserves_subobject_classifier.
  - exact (λ _ _ _ _ _ _ _ _ pO₁ pO₂, comp_preserves_subobject_classifier pO₁ pO₂).
Defined.

Definition disp_bicat_subobjectclassifier
  : disp_bicat bicat_of_cats.
Proof.
  use sigma_bicat.
  - exact disp_bicat_lex.
  - exact disp_bicat_subobjectclassifier_over_lex.
Defined.

Lemma sigma_of_contractible_is_contractible
  {A : UU} (B : A → UU)
  (p : iscontr A) (q : ∏ a :A, iscontr (B a))
  : iscontr (∑ a : A, B a).
Proof.
  exists (pr1 p ,, pr1 (q (pr1 p))).
  intros [tA tB].
  use subtypePath.
  - intro.
    apply isapropifcontr.
    apply q.
  - apply p.
Qed.

Lemma disp_bicat_of_sigma_iscontr
  {B : bicat}
  {C : disp_bicat B}
  (D : disp_bicat (total_bicat C))
  : disp_2cells_iscontr C → disp_2cells_iscontr D
    → disp_2cells_iscontr (sigma_bicat _ C D).
Proof.
  intros c d.
  intro ; intros.
  apply sigma_of_contractible_is_contractible.
  - apply c.
  - intro ; apply d.
Qed.

Lemma disp_2cells_is_contr_subobjectclassifier_over_lex
  : disp_2cells_iscontr disp_bicat_subobjectclassifier_over_lex.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.

Lemma disp_2cells_is_contr_subobjectclassifier
  : disp_2cells_iscontr disp_bicat_subobjectclassifier.
Proof.
  apply disp_bicat_of_sigma_iscontr.
  - exact disp_2cells_is_contr_lex.
  - exact disp_2cells_is_contr_subobjectclassifier_over_lex.
Qed.
