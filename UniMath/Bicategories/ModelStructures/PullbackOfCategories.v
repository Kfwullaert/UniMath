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
    abstract (repeat split ; intro ; intros
    ; try (apply homset_property) ;
              apply isasetaprop ;
              apply homset_property).
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
      + abstract (intros ? ? [? p] ;
        exact p).
    - intros [[a1 a2] γ].
      exact (pr2 γ).
  Defined.

  Definition CAT_bp_ump_1_functor_existence
    {C : category}
    {G1 : functor C A1}
    {G2 : functor C A2}
    (γ : nat_z_iso (functor_composite G1 F1) (functor_composite G2 F2))
    : functor C (total_category_data pullback_of_CATs_disp_data).
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro c.
        exists (G1 c ,, G2 c).
        exact ( _ ,, pr2 γ c).
      + intros c1 c2 f.
        exists (#G1 f ,, #G2 f).
        exact (pr21 γ _ _ f).
    - split ; intro ; intros ; use total2_paths_f.
      + abstract (cbn ; now do 2 rewrite functor_id).
      + abstract (apply homset_property).
      + abstract (cbn ; now do 2 rewrite functor_comp).
      + abstract (apply homset_property).
  Defined.

  Definition CAT_bp_ump_1_nat_z_iso_existence1
    {C : category}
    {G1 : functor C A1}
    {G2 : functor C A2}
    (γ : nat_z_iso (functor_composite G1 F1) (functor_composite G2 F2))
    : nat_z_iso
        (functor_composite (CAT_bp_ump_1_functor_existence γ)
           (functor_composite (pr1_category pullback_of_CATs_disp_cat) (pr1_functor A1 A2))) G1.
  Proof.
    use make_nat_z_iso.
    - apply nat_trans_id.
    - exact (is_nat_z_iso_nat_trans_id G1).
  Defined.

  Definition CAT_bp_ump_1_nat_z_iso_existence2
    {C : category}
    {G1 : functor C A1}
    {G2 : functor C A2}
    (γ : nat_z_iso (functor_composite G1 F1) (functor_composite G2 F2))
    : nat_z_iso
        (functor_composite (CAT_bp_ump_1_functor_existence γ)
           (functor_composite (pr1_category pullback_of_CATs_disp_cat) (pr2_functor A1 A2))) G2.
  Proof.
    use make_nat_z_iso.
    - apply nat_trans_id.
    - exact (is_nat_z_iso_nat_trans_id G2).
  Defined.

  Lemma CAT_bp_ump_1 : pb_ump_1 CAT_pb_cone.
  Proof.
    intros [C [G1 [G2 γ]]].
    exists (CAT_bp_ump_1_functor_existence (invertible_2cell_to_nat_z_iso _ _ γ)).
    exists (nat_z_iso_to_invertible_2cell _ _ (CAT_bp_ump_1_nat_z_iso_existence1 (invertible_2cell_to_nat_z_iso _ _ γ))).
    exists (nat_z_iso_to_invertible_2cell _ _ (CAT_bp_ump_1_nat_z_iso_existence2 (invertible_2cell_to_nat_z_iso _ _ γ))).
    use nat_trans_eq.
    { apply homset_property. }
    abstract (intro ; cbn ; rewrite (functor_id F1 _ ), (functor_id F2 _) ;
              do 2 rewrite id_left ;
              now do 2 rewrite id_right).
  Defined.

  Lemma CAT_bp_ump_2 : pb_ump_2 CAT_pb_cone.
  Proof.
    unfold pb_ump_2.
    intros C G1 G2 γ1 γ2 p.
    use tpair.
    - use tpair.
      + use make_nat_trans.
        * intro c.
          exists (pr1 γ1 c ,, pr1 γ2 c).
          abstract (
              refine (_ @ ! toforallpaths _ _ _ (base_paths _ _ p) c @ _)
              ; cbn ;
                  [ now rewrite id_left, id_right
                  | do 2 rewrite id_right] ; apply idpath).
        * intro ; intros.
          repeat (use total2_paths_f).
          -- abstract (apply (pr2 γ1)).
          -- abstract (cbn ; rewrite transportf_const ;
             apply (pr2 γ2)).
          -- apply homset_property.
      + abstract (split ; use (nat_trans_eq (homset_property _))
        ; intro ; apply idpath).
    - intro t.
      use total2_paths_f.
      + use (nat_trans_eq (homset_property _)).
        abstract (
            intro c
            ; use total2_paths_f ;
            [ use total2_paths_f ;
              [ exact (toforallpaths _ _ _ (base_paths _ _ (pr12 t)) c)
              | cbn ; rewrite transportf_const
                ; exact (toforallpaths _ _ _ (base_paths _ _ (pr22 t)) c)]
              | apply homset_property]).
      + abstract (use total2_paths_f
        ; apply isaset_nat_trans
        ; apply homset_property).
  Defined.

  Definition CAT_has_bp_ump : has_pb_ump CAT_pb_cone
    := CAT_bp_ump_1 ,, CAT_bp_ump_2.

End A.


Local Definition CAT_has_pb : has_pb CAT.
Proof.
  intros A1 A2 B F1 F2.
  exists (CAT_pb_cone F1 F2).
  exact (CAT_has_bp_ump F1 F2).
Defined.
