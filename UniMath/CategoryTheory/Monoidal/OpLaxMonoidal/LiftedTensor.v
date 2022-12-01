(* This file is the first file with the purpose of showing that any monoidal category admits a 'Monoidal Rezk-completion'.
More precisely: Assume that a category C is weakly equivalent to a univalent category D, by a functor H : C → D.
Then, given a product/tensor T : C ⊠ C → C, we construct a product TD on D such that H preserves the product in a 'strong sense'.
Then, we show that (D,TD) is universal along univalent categories with a product in the sense that
(D,TD) is the free univalent category equipped with a tensor of (C,T).
A more detailled explanation of the universality and the Rezk-completion is in LiftedMonoidal.v
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.Monoidal.OpLaxMonoidal.OpLaxMonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.OpLaxMonoidal.OpLaxMonoidalFunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.DisplayedCats.TotalCategoryFacts.

Local Open Scope cat.

Section TensorRezk.

  Context {C D E : category} {H : functor C D}
          (Duniv : is_univalent D)
          (Euniv : is_univalent E)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C)
          (TE : functor (E ⊠ E) E).

  Local Notation HH := (pair_functor H H).
  Let HH_eso := pair_functor_eso H H H_eso H_eso.
  Let HH_ff := pair_functor_ff H H H_ff H_ff.

  Definition TransportedTensor
    : functor (D ⊠ D) D
    := lift_functor_along (_,,Duniv) HH HH_eso HH_ff (functor_composite TC H).

  Definition TransportedTensorComm
    : nat_z_iso (functor_composite TC H) (HH ∙ TransportedTensor)
    := nat_z_iso_inv (lift_functor_along_comm (_,,Duniv) HH HH_eso HH_ff (functor_composite TC H)).

  Let TD := TransportedTensor.

  Definition precompT_data
    : disp_functor_data (pre_composition_functor _ _ E H)
                   (functor_tensor_disp_cat TD TE)
                   (functor_tensor_disp_cat TC TE).
  Proof.
    exists (λ G GG, functor_tensor_composition (pr1 TransportedTensorComm) GG).
    intros G1 G2 GG1 GG2 β ββ.
    intros x y.
    simpl.
    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      exact (ββ (H x) (H y)).
    }
    do 2 rewrite assoc.
    apply maponpaths_2.
    exact (! pr2 β _ _ (pr1 (pr1 (TransportedTensorComm)) (x, y))).
  Defined.

  Definition HT
    : disp_functor (pre_composition_functor _ _ E H)
                   (functor_tensor_disp_cat TD TE)
                   (functor_tensor_disp_cat TC TE).
  Proof.
    exists precompT_data.
    abstract (split ; intro ; intros ; apply isaprop_is_nat_trans_tensor).
  Defined.

  Definition lifted_functor_tensor
             {G : D ⟶ E}
             (HGG : functor_tensor TC TE (functor_compose H G))
    : functor_tensor TD TE G.
  Proof.
    use (lift_nat_trans_along (_,,Euniv) _ HH_eso HH_ff).
    use (nat_trans_comp _ _ _ _ HGG).
    exact (post_whisker (nat_z_iso_inv TransportedTensorComm) G).
  Defined.

  Definition HT_eso : disp_functor_disp_ess_split_surj HT.
  Proof.
    intros G HGG.
    exists (lifted_functor_tensor HGG).
    use Isos.make_z_iso_disp.
    - intros c1 c2.
      simpl.
      rewrite (functor_id TE).
      rewrite id_left, id_right.



      set (β := nat_trans_comp _ _ _
                               (post_whisker (nat_z_iso_inv TransportedTensorComm) G) HGG
             :  functor_composite HH (functor_composite TransportedTensor G)
                                  ⟹ functor_composite HH (functor_composite (pair_functor G G) TE)).

      set (p := toforallpaths _ _ _ (base_paths _ _
                                                (lift_nat_trans_along_comm (_,,Euniv) _ HH_eso HH_ff β)) (c1,c2)).

      etrans.
      2: {
        apply maponpaths.
        exact (! p).
      }
      clear p.
      unfold β.
      clear β.
      simpl.
      rewrite assoc.
      rewrite <- (functor_comp G).
      etrans.
      2: {
        apply maponpaths_2.
        apply maponpaths.
        apply (! pr12 (pr2 (TransportedTensorComm) (c1,c2))).
      }

      rewrite functor_id.
      exact (! id_left _).
    - use tpair.
      2: { split ; apply isaprop_is_nat_trans_tensor. }
      intros c1 c2.
      simpl.
      rewrite (functor_id TE).
      rewrite id_left, id_right.

      set (β := nat_trans_comp _ _ _
                               (post_whisker (nat_z_iso_inv TransportedTensorComm) G) HGG
             :  functor_composite HH (functor_composite TransportedTensor G)
                                  ⟹ functor_composite HH (functor_composite (pair_functor G G) TE)).

      set (p := toforallpaths _ _ _ (base_paths _ _
                                                (lift_nat_trans_along_comm (_,,Euniv) _ HH_eso HH_ff β)) (c1,c2)).

      etrans. {
        apply maponpaths.
        exact p.
      }
      clear p.
      unfold β.
      clear β.
      simpl.
      rewrite assoc.
      rewrite <- (functor_comp G).
      etrans. {
        apply maponpaths_2.
        apply maponpaths.
        apply (pr12 (pr2 (TransportedTensorComm) (c1,c2))).
      }

      rewrite functor_id.
      exact (id_left _).
  Qed.

  Definition HT_is_faithful
             {G1 G2 : [D, E]}
             (GG1 : functor_tensor_disp_cat TD TE G1)
             (GG2 : functor_tensor_disp_cat TD TE G2)
             (β : [D, E] ⟦ G1, G2 ⟧)
    : isincl (λ ff : GG1 -->[ β] GG2, (# HT)%mor_disp ff).
  Proof.
    do 3 intro.
    assert (p : isaset ( hfiber (λ ff : GG1 -->[ β] GG2, (# HT)%mor_disp ff) y)).
    {
      use isaset_hfiber ; use isasetaprop ; apply isaprop_is_nat_trans_tensor.
    }

    use tpair.
    + use total2_paths_f.
      { apply isaprop_is_nat_trans_tensor. }
      use proofirrelevance.
      use hlevelntosn.
      apply isaprop_is_nat_trans_tensor.
    + intro ; apply p.
  Qed.

  Definition HT_is_full
             {G1 G2 : [D, E]}
             (GG1 : functor_tensor_disp_cat TD TE G1)
             (GG2 : functor_tensor_disp_cat TD TE G2)
             (β : [D, E] ⟦ G1, G2 ⟧)
    :   issurjective (λ ff : GG1 -->[ β] GG2, (# HT)%mor_disp ff).
  Proof.
    intro βHH.
    apply hinhpr.
    use tpair.
    2: apply isaprop_is_nat_trans_tensor.

    intros d1 d2.

    use factor_through_squash.
    1: exact (∑ a : C, z_iso (H a) d1).
    1: apply homset_property.
    2: exact (H_eso d1).
    intro c1.

    use factor_through_squash.
    1: exact (∑ a : C, z_iso (H a) d2).
    1: apply homset_property.
    2: exact (H_eso d2).
    intro c2.

    induction (isotoid _ Duniv (pr2 c1)).
    induction (isotoid _ Duniv (pr2 c2)).

    set (t := βHH (pr1 c1) (pr1 c2)).


  Admitted.

  Definition HT_ff : disp_functor_ff HT.
  Proof.
    intro ; intros.
    apply isweqinclandsurj.
    - apply HT_is_faithful.
    - apply HT_is_full.
  Qed.

  Definition precomp_tensor_is_ff
    : fully_faithful (total_functor HT).
  Proof.
    use disp_functor_ff_to_total_ff.
    - apply precomp_fully_faithful.pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful.
      + exact H_eso.
      + exact H_ff.
    - exact HT_ff.
  Qed.

  Definition precomp_tensor_is_eso
    : essentially_surjective (total_functor HT).
  Proof.
    use disp_functor_eso_to_total_eso.
    - apply precomp_ess_surj.pre_composition_essentially_surjective.
      + exact Euniv.
      + exact H_eso.
      + exact H_ff.
    - exact HT_eso.
    - use Fibrations.iso_cleaving_category.
      apply is_univalent_functor_category.
      exact Euniv.
  Qed.

  Definition precomp_tensor_adj_equiv
    : adj_equivalence_of_cats (total_functor HT).
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_total_category.
      + apply is_univalent_functor_category.
        exact Euniv.
      + apply functor_tensor_disp_cat_is_univalent.
    - exact precomp_tensor_is_ff.
    - exact precomp_tensor_is_eso.
  Defined.

End TensorRezk.
