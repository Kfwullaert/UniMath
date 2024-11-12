Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.terminal.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.binproducts.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.pullbacks.

Local Open Scope cat.

Definition disp_bicat_lex : disp_bicat bicat_of_cats.
Proof.
  use (disp_dirprod_bicat _ (disp_dirprod_bicat _ _)).
  - exact disp_bicat_terminal.
  - exact disp_bicat_binproducts.
  - exact disp_bicat_pullbacks.
Defined.

Lemma dirprod_of_contractible_is_contractible
  {A₁ A₂ : UU}
  (p : iscontr A₁) (q : iscontr A₂)
  : iscontr (A₁ × A₂).
Proof.
  exists (pr1 p ,, pr1 q).
  intro t.
  induction t as [t₁ t₂].
  use subtypePath.
  - intro.
    apply isapropifcontr.
    apply q.
  - apply p.
Qed.

Lemma disp_dirprod_bicat_of_dirprod_iscontr
  {B : bicat}
  (D₁ D₂ : disp_bicat B)
  : disp_2cells_iscontr D₁ → disp_2cells_iscontr D₂
    → disp_2cells_iscontr (disp_dirprod_bicat D₁ D₂).
Proof.
  intros d1 d2.
  intro ; intros.
  apply dirprod_of_contractible_is_contractible;
    [apply d1 | apply d2 ].
Qed.

Lemma disp_2cells_is_contr_lex
  : disp_2cells_iscontr disp_bicat_lex.
Proof.
  apply disp_dirprod_bicat_of_dirprod_iscontr.
  { apply disp_2cells_is_contr_terminal. }
  apply disp_dirprod_bicat_of_dirprod_iscontr.
  - apply disp_2cells_is_contr_binproducts.
  - apply disp_2cells_is_contr_pullbacks.
Qed.
