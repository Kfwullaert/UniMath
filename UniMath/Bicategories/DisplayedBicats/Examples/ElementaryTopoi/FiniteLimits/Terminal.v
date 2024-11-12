(**
We construct 4 bicategories for categories.
[1.] Categories Cᵢ with a fixed/chosen terminal object Tᵢ.
     [a.] || F(Tᵢ) = T{ᵢ+1} ||
     [b.]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.Terminal.
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

(*
Print preserves_chosen_terminal. (* image of fixed terminal is terminal *)
Print preserves_terminal. (* image of arbitrary terminal is terminal *)
Print preserves_chosen_terminal_eq. (* image of fixed terminal is equal to fixed terminal, modulo hset-truncation *)
(* Print preserves_chosen_terminal_iso. (* image of fixed terminal is iso to fixed terminal *) *)
*)

(**
 1. Categories with a chosen terminal object
 *)

Definition disp_bicat_terminal
  : disp_bicat bicat_of_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, Terminal (pr1 C)).
  - exact (λ C₁ C₂ T₁ T₂ F, preserves_terminal F).
  - exact (λ C T, identity_preserves_terminal C).
  - exact (λ _ _ _ _ _ _ _ _ PF PG, composition_preserves_terminal PF PG).
Defined.

Definition cat_with_terminal
  : bicat
  := total_bicat disp_bicat_terminal.

Definition disp_bicat_chosen_terminal_obj
  : disp_bicat bicat_of_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, Terminal (pr1 C)).
  - exact (λ C₁ C₂ T₁ T₂ F, preserves_chosen_terminal_eq F T₁ T₂).
  - exact (λ C T, identity_preserves_chosen_terminal_eq T).
  - exact (λ _ _ _ _ _ _ _ _ PF PG, composition_preserves_chosen_terminal_eq PF PG).
Defined.

Definition cat_with_chosen_terminal_obj
  : bicat
  := total_bicat disp_bicat_chosen_terminal_obj.

(**
 2. Categories that have a terminal object
 *)
Definition disp_bicat_have_terminal_obj
  : disp_bicat bicat_of_cats.
Proof.
  use disp_subbicat.
  - exact (λ C, @hasTerminal (pr1 C)).
  - exact (λ C₁ C₂ _ _ F, preserves_terminal F).
  - exact (λ C _, identity_preserves_terminal _).
  - exact (λ _ _ _ _ _ _ _ _ HF HG, composition_preserves_terminal HF HG).
Defined.

Definition cat_with_terminal_obj
  : bicat
  := total_bicat disp_bicat_have_terminal_obj.

(* 3. Homotopy levels of each type of 2-cells *)
Lemma disp_2cells_is_contr_have_terminal_obj
  : disp_2cells_iscontr disp_bicat_have_terminal_obj.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.

Lemma disp_2cells_is_contr_terminal
  : disp_2cells_iscontr disp_bicat_terminal.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.

Lemma disp_2cells_is_contr_chosen_terminal_obj
  : disp_2cells_iscontr disp_bicat_chosen_terminal_obj.
Proof.
  intro ; intros.
  exists (tt,,tt).
  intro.
  use total2_paths_f ; apply iscontrunit.
Qed.
