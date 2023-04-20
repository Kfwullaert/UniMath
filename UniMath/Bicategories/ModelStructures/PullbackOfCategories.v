Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws. (* There is a possibility that this one will not be used, hence could be removed. However, this is currently in this file because of search reasons. *)

Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Limits.Pullbacks.

Local Open Scope cat.

Local Definition CAT : bicat := bicat_of_cats.

Section A.

  Context {A1 A2 B : category} (F1 : functor A1 B) (F2 : functor A2 B).

  Definition pullback_of_CATs_disp_cat_ob_mor
    : disp_cat_ob_mor (category_binproduct A1 A2).
  Proof.
    exists (λ a, z_iso (F1 (pr1 a)) (F2  (pr2 a))).
    intros [a1 a2]  [a1' a2']  [γ γ_iso]  [γ' γ'_iso] [f1 f2].
    exact (#F1 f1 · γ' = γ · #F2 f2).
  Defined.

  Lemma pullback_of_CATs_disp_cat_id_comp
    :  disp_cat_id_comp (category_binproduct A1 A2) pullback_of_CATs_disp_cat_ob_mor.
  Proof.
    split ; intro ; intros ; cbn in *.
    - do 2 rewrite functor_id.
      now rewrite id_left, id_right.
    - rewrite functor_comp.
      refine (assoc' _ _ _ @ _).
      etrans. {
        apply maponpaths.
        exact X0.
      }
      refine (assoc _ _ _ @ _).
      etrans. {
        apply maponpaths_2.
        exact X.
      }
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply pathsinv0, functor_comp.
  Qed.


  Definition pullback_of_CATs_disp_data
    : disp_cat_data (category_binproduct A1 A2)
    := _ ,, pullback_of_CATs_disp_cat_id_comp.

  Definition pullback_of_CATs_disp_cat
    : disp_cat (category_binproduct A1 A2).
  Proof.
    exists pullback_of_CATs_disp_data.
    repeat split ; intro ; intros
    ; try (apply homset_property).
    apply isasetaprop.
    apply homset_property.
  Defined.

  Definition CAT_pb_cone
    : pb_cone (B := CAT) F1 F2.
  Proof.
    exists (total_category pullback_of_CATs_disp_cat).
    exists (functor_composite (pr1_category _) (pr1_functor _ _)).
    exists (functor_composite (pr1_category _) (pr2_functor _ _)).

    apply nat_z_iso_to_invertible_2cell.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intros [[a1 a2] γ].
        exact (pr1 γ).
      + intros [[a1 a2] γ] [[a1' a2'] γ'] [[f1 f2] p].
        exact p.
    - intros [[a1 a2] γ].
      exact (pr2 γ).
  Defined.

  Lemma CAT_has_bp_ump : has_pb_ump CAT_pb_cone.
  Proof.
    unfold has_pb_ump.
    split.
    - unfold pb_ump_1.
      intro pbcone.
      unfold pb_1cell.
      use tpair.
      + use make_functor.
        * use make_functor_data.
          -- intro v.
             exists ((pr1 (pb_cone_pr1 pbcone) v) ,, (pr1 (pb_cone_pr2 pbcone) v)).
             cbn in *.
             Search pb_cone.
  Admitted.

End A.


Local Definition CAT_has_pb : has_pb CAT.
Proof.
  intros A1 A2 B F1 F2.
  exists (CAT_pb_cone F1 F2).
  exact (CAT_has_bp_ump F1 F2).
Defined.
