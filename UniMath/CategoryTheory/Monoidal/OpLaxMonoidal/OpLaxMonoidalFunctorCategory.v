Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Require Import UniMath.CategoryTheory.Monoidal.OpLaxMonoidal.OpLaxMonoidalCategories.

Local Open Scope cat.

Local Notation "C ⊠ D" := (category_binproduct C D) (at level 38).

Local Notation "( c , d )" := (make_catbinprod c d).
Local Notation "( f #, g )" := (catbinprodmor f g).

Section TensorFunctorCategory.

  Context {C D : category}
          (TC : functor (C ⊠ C) C)
          (TD : functor (D ⊠ D) D).

  Notation "X ⊗_C Y" := (TC (X , Y)) (at level 31).
  Notation "f #⊗_C g" := (# TC (f #, g)) (at level 31).
  Notation "X ⊗_D Y" := (TD (X , Y)) (at level 31).
  Notation "f #⊗_D g" := (# TD (f #, g)) (at level 31).

  Definition functor_tensor_map_dom (F : functor C D)
    : functor (C ⊠ C) D
    := functor_composite (pair_functor F F) TD.

  Definition functor_tensor_map_codom (F : functor C D)
    : functor (C ⊠ C) D
    := functor_composite TC F.

  Definition functor_tensor (F : functor C D)
    : UU := nat_trans (functor_tensor_map_codom F) (functor_tensor_map_dom F).
  Identity Coercion functor_tensor_c : functor_tensor >-> nat_trans.

  Definition is_nat_trans_tensor {F G : functor C D}
             (FF : functor_tensor F) (GG : functor_tensor G)
             (α : nat_trans F G) : UU
    := ∏ x y : C, α (x ⊗_C y) · GG (x, y) = FF (x, y) · (α x #⊗_D α y).

  Lemma isaprop_is_nat_trans_tensor {F G : functor C D}
             (FF : functor_tensor F) (GG : functor_tensor G)
             (α : nat_trans F G)
    : isaprop (is_nat_trans_tensor FF GG α).
  Proof.
    do 2 (apply impred_isaprop ; intro) ; apply D.
  Qed.

  Lemma is_nat_trans_tensor_id
             {F : functor C D} (FF : functor_tensor F)
    : is_nat_trans_tensor FF FF (nat_trans_id F).
  Proof.
    intros x y.
    simpl.
    rewrite (functor_id TD).
    exact (id_left _ @ ! id_right _).
  Qed.

  Lemma is_nat_trans_tensor_comp
             {F G H : functor C D}
             (FF : functor_tensor F) (GG : functor_tensor G) (HH : functor_tensor H)
             {α : nat_trans F G} {β : nat_trans G H}
             (αα : is_nat_trans_tensor FF GG α)
             (ββ : is_nat_trans_tensor GG HH β)
    : is_nat_trans_tensor FF HH (nat_trans_comp _ _ _ α β).
  Proof.
    intros x y.
    simpl.
    etrans. {
      rewrite assoc'.
      apply maponpaths.
      exact (ββ x y).
    }

    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      apply αα.
    }

    rewrite assoc'.
    apply maponpaths.
    exact (! functor_comp TD (α x #, α y) (β x #, β y)).
  Qed.

  Definition functor_tensor_disp_cat_ob_mor
    : disp_cat_ob_mor [C,D].
  Proof.
    exists (λ F, functor_tensor F).
    exact (λ F G FF GG α, is_nat_trans_tensor FF GG α).
  Defined.

  Definition functor_tensor_disp_cat_id_comp
    : disp_cat_id_comp _ functor_tensor_disp_cat_ob_mor.
  Proof.
    split ; intro ; intros ; [apply is_nat_trans_tensor_id | use is_nat_trans_tensor_comp ; assumption ].
  Qed.

  Definition functor_tensor_disp_cat_data
    : disp_cat_data [C,D]
    := _ ,, functor_tensor_disp_cat_id_comp.

  Definition functor_tensor_disp_cat_axioms
    : disp_cat_axioms _ functor_tensor_disp_cat_data.
  Proof.
    repeat split ; intro ; intros ; try (apply isaprop_is_nat_trans_tensor).
    use isasetaprop.
    apply isaprop_is_nat_trans_tensor.
  Qed.

  Definition functor_tensor_disp_cat : disp_cat [C,D]
    := _ ,, functor_tensor_disp_cat_axioms.

  Definition functor_tensor_cat : category
    := total_category functor_tensor_disp_cat.

End TensorFunctorCategory.

Section TensorFunctorCategoryUnivalence.

  Context {C D : category}
          (TC : functor (C ⊠ C) C)
          (TD : functor (D ⊠ D) D).

  Lemma isaset_functor_tensor_disp_cat (F : functor C D)
    :  isaset (functor_tensor_disp_cat TC TD F).
  Proof.
    apply isaset_nat_trans.
    { apply D. }
  Qed.

  Lemma functor_tensor_disp_cat_is_univalent
    : is_univalent_disp (functor_tensor_disp_cat TC TD).
  Proof.
    apply is_univalent_disp_from_fibers.
    intros F pt1 pt2.
    use isweqimplimpl.
    - intro i.
      use total2_paths_f.
      + apply funextsec ; intro.
        set (ix := (pr1 i) (pr1 x) (pr2 x)).
        cbn in ix.
        rewrite binprod_id in ix.
        rewrite (functor_id TD) in ix.
        rewrite id_right in ix.
        rewrite id_left in ix.
        exact (! ix).
      + do 2 (apply funextsec ; intro).
        repeat (apply impred_isaprop ; intro).
        apply D.
    - apply isaset_functor_tensor_disp_cat.
    - apply isaproptotal2.
      + intro ; apply Isos.isaprop_is_z_iso_disp.
      + do 4 intro ; apply isaprop_is_nat_trans_tensor.
  Qed.

End TensorFunctorCategoryUnivalence.

Section TensorFunctorProperties.

  Lemma functor_tensor_composition_is_nat_trans
        {C D E : category}
        {TC : functor (C ⊠ C) C}
        {TD : functor (D ⊠ D) D}
        {TE : functor (E ⊠ E) E}
        {F : functor C D} {G : functor D E}
        (FF : functor_tensor TC TD F) (GG : functor_tensor TD TE G)
        : is_nat_trans
            (functor_tensor_map_codom TC (F ∙ G))
            (functor_tensor_map_dom TE (F ∙ G))
            (λ cc : C × C, # G (FF cc) · GG (F (pr1 cc), F (pr2 cc))).
  Proof.
    intros cc1 cc2 f.
    simpl.
    etrans. {
      rewrite assoc.
      apply maponpaths_2.
      rewrite <- functor_comp.
      apply maponpaths.
      exact(pr2 FF cc1 cc2 f).
    }

    rewrite functor_comp.
    do 2 rewrite assoc'.
    apply maponpaths.

    exact (pr2 GG ((pair_functor F F) cc1) (pair_functor F F cc2) (# (pair_functor F F) f)).
  Qed.

  Definition functor_tensor_composition
             {C D E : category}
             {TC : functor (C ⊠ C) C}
             {TD : functor (D ⊠ D) D}
             {TE : functor (E ⊠ E) E}
             {F : functor C D} {G : functor D E}
             (FF : functor_tensor TC TD F) (GG : functor_tensor TD TE G)
    : functor_tensor TC TE (functor_composite F G).
  Proof.
    exists (λ cc : C × C, # G (FF cc) · GG (F (pr1 cc), F (pr2 cc))).
    apply functor_tensor_composition_is_nat_trans.
  Defined.

End TensorFunctorProperties.

Section UnitFunctorCategory.

  Context {C D : category} (IC : C) (ID : D).

  Definition functor_unit (F : functor C D) : UU
    := D⟦pr1 F IC, ID⟧.

  Definition is_nat_trans_unit
             {F G : functor C D} (FF : functor_unit F) (GG : functor_unit G)
             (α : nat_trans F G) : UU
    := α IC · GG = FF.

  Definition functor_unit_disp_cat_ob_mor
    : disp_cat_ob_mor [C,D].
  Proof.
    exists (λ F, functor_unit F).
    exact (λ F G FF GG α, is_nat_trans_unit FF GG α).
  Defined.

  Lemma is_nat_trans_unit_id
             {F : functor C D} (FF : functor_unit F)
    : is_nat_trans_unit FF FF (nat_trans_id F).
  Proof.
    apply id_left.
  Qed.

  Lemma is_nat_trans_unit_comp
             {F G H : functor C D}
             (FF : functor_unit F) (GG : functor_unit G) (HH : functor_unit H)
             {α : nat_trans F G} {β : nat_trans G H}
             (αα : is_nat_trans_unit FF GG α)
             (ββ : is_nat_trans_unit GG HH β)
    : is_nat_trans_unit FF HH (nat_trans_comp _ _ _ α β).
  Proof.
    etrans. {
      simpl.
      rewrite assoc'.
      apply maponpaths.
      exact ββ.
    }
    exact αα.
  Qed.

  Definition functor_unit_disp_cat_id_comp
    : disp_cat_id_comp _ functor_unit_disp_cat_ob_mor.
  Proof.
    split ; intro ; intros ; [apply is_nat_trans_unit_id | use is_nat_trans_unit_comp ; assumption ].
  Qed.

  Definition functor_unit_disp_cat_data
    : disp_cat_data [C,D]
    := _ ,, functor_unit_disp_cat_id_comp.

  Definition functor_unit_disp_cat_axioms
    : disp_cat_axioms _ functor_unit_disp_cat_data.
  Proof.
    repeat split ; intro ; intros ; try (apply D).
    use isasetaprop.
    apply D.
  Qed.

  Definition functor_unit_disp_cat : disp_cat [C,D]
    := _ ,, functor_unit_disp_cat_axioms.

  Definition functor_unit_cat : category
    := total_category functor_unit_disp_cat.

End UnitFunctorCategory.

Section UnitFunctorCategoryUnivalence.

  Context {C D : category} (IC : C) (ID : D).

  Lemma functor_unit_disp_cat_is_univalent
    : is_univalent_disp (functor_unit_disp_cat IC ID).
  Proof.
    apply is_univalent_disp_from_fibers.
    intros F pt1 pt2.
    use isweqimplimpl.
    - intro i.
      refine (! pr1 i @ _).
      apply id_left.
    - apply D.
    - apply isaproptotal2.
      + intro ; apply Isos.isaprop_is_z_iso_disp.
      + do 4 intro ; apply D.
  Qed.

End UnitFunctorCategoryUnivalence.

Section UnitFunctorProperties.

  Definition functor_unit_composition
             {C D E : category}
             {IC : C} {ID : D} {IE : E}
             {F : functor C D} {G : functor D E}
             (FF : functor_unit IC ID F) (GG : functor_unit ID IE G)
    : functor_unit IC IE (functor_composite F G)
    := #G FF · GG.

End UnitFunctorProperties.


Section FunctorTensorUnit.

  Context {C D : category}
          (TC : functor (C ⊠ C) C) (TD : functor (D ⊠ D) D)
          (IC : C) (ID : D).

  Definition functor_tensorunit_disp_cat
    : disp_cat [C,D]
    := dirprod_disp_cat (functor_tensor_disp_cat TC TD) (functor_unit_disp_cat IC ID).

  Lemma functor_tensorunit_disp_cat_is_univalent
    : is_univalent_disp functor_tensorunit_disp_cat.
  Proof.
    apply dirprod_disp_cat_is_univalent.
    - apply functor_tensor_disp_cat_is_univalent.
    - apply functor_unit_disp_cat_is_univalent.
  Qed.

  Definition functor_tensorunit_cat
    : category := total_category functor_tensorunit_disp_cat.

End FunctorTensorUnit.

Section TensorUnitFunctorProperties.

  Context {C D E : category}
          {TC : functor (C ⊠ C) C} {TD : functor (D ⊠ D) D}
          {TE : functor (E ⊠ E) E}
          {IC : C} {ID : D} {IE : E}.

  Definition functor_tensorunit_composition
             {F : functor C D} {G : functor D E}
             (FF : functor_tensorunit_disp_cat TC TD IC ID F)
             (GG : functor_tensorunit_disp_cat TD TE ID IE G)
    : functor_tensorunit_disp_cat TC TE IC IE (functor_composite F G).
  Proof.
    exists (functor_tensor_composition (pr1 FF) (pr1 GG)).
    exact (functor_unit_composition (pr2 FF) (pr2 GG)).
  Defined.

End TensorUnitFunctorProperties.

Section MonoidalFunctorCategory.

  Context {C D : category}
          {TC : functor (C ⊠ C) C} {TD : functor (D ⊠ D) D}
          {IC : C} {ID : D}
          (luC : left_unitor TC IC) (luD : left_unitor TD ID)
          (ruC : right_unitor TC IC) (ruD : right_unitor TD ID)
          (αC : associator TC) (αD : associator TD).

  Notation "X ⊗_C Y" := (TC (X , Y)) (at level 31).
  Notation "f #⊗_C g" := (# TC (f #, g)) (at level 31).
  Notation "X ⊗_D Y" := (TD (X , Y)) (at level 31).
  Notation "f #⊗_D g" := (# TD (f #, g)) (at level 31).

  Definition functor_lu_disp_cat : disp_cat (functor_tensorunit_cat TC TD IC ID).
  Proof.
    use disp_full_sub.
    intros [F [FT FU]].
    exact (∏ x : C, luD (pr1 F x) = #(pr1 F) (luC x) · (pr1 FT) (IC, x) · FU #⊗_D (id (pr1 F x))).
  Defined.

  Definition functor_ru_disp_cat : disp_cat (functor_tensorunit_cat TC TD IC ID).
  Proof.
    use disp_full_sub.
    intros [F [FT FU]].
    exact (∏ x : C, ruD (pr1 F x) =  ( #(pr1 F) (ruC x) · (pr1 FT) (x, IC) · (id (pr1 F x) #⊗_D FU))).
  Defined.

  Definition functor_ass_disp_cat : disp_cat (functor_tensorunit_cat TC TD IC ID).
  Proof.
    use disp_full_sub.
    intros [F [FT FU]].

    exact (∏ (x y z : C),
             #(pr1 F) (αC ((x, y), z)) · pr1 FT (x ⊗_C y, z) · pr1 FT (x, y) #⊗_D id (pr1 F(z))
            = pr1 FT (x, y ⊗_C z) · id (pr1 F x) #⊗_D pr1 FT (y, z) · αD ((pr1 F x, pr1 F y), pr1 F z)).
  Defined.

  Lemma functor_lu_disp_cat_is_univalent
    : is_univalent_disp functor_lu_disp_cat.
  Proof.
    apply disp_full_sub_univalent.
    intro.
    apply impred_isaprop ; intro ; apply D.
  Qed.

  Lemma functor_ru_disp_cat_is_univalent
    : is_univalent_disp functor_ru_disp_cat.
  Proof.
    apply disp_full_sub_univalent.
    intro.
    apply impred_isaprop ; intro ; apply D.
  Qed.

  Lemma functor_ass_disp_cat_is_univalent
    : is_univalent_disp functor_ass_disp_cat.
  Proof.
    apply disp_full_sub_univalent.
    intro.
    do 3 (apply impred_isaprop ; intro) ; apply D.
  Qed.

  Definition functor_monoidal_disp_cat
    : disp_cat (functor_tensorunit_cat TC TD IC ID)
    := dirprod_disp_cat
         (dirprod_disp_cat functor_lu_disp_cat functor_ru_disp_cat)
         functor_ass_disp_cat.

  Definition functor_monoidal_cat
    : category
    := total_category functor_monoidal_disp_cat.

End MonoidalFunctorCategory.

Section StrongMonoidalFunctorCategory.

  Context {C D : category}
          {TC : functor (C ⊠ C) C} {TD : functor (D ⊠ D) D}
          {IC : C} {ID : D}
          (luC : left_unitor TC IC) (luD : left_unitor TD ID)
          (ruC : right_unitor TC IC) (ruD : right_unitor TD ID)
          (αC : associator TC) (αD : associator TD).

  Notation "X ⊗_C Y" := (TC (X , Y)) (at level 31).
  Notation "f #⊗_C g" := (# TC (f #, g)) (at level 31).
  Notation "X ⊗_D Y" := (TD (X , Y)) (at level 31).
  Notation "f #⊗_D g" := (# TD (f #, g)) (at level 31).

  Definition functor_strong_monoidal_disp_cat
    : disp_cat (functor_monoidal_cat luC luD ruC ruD αC αD)
    := disp_full_sub (functor_monoidal_cat luC luD ruC ruD αC αD)
                     (λ F,
                       is_nat_z_iso (pr121 F : nat_trans _ _)
                                    × is_z_isomorphism (pr221 F)).

  Definition strong_functor_monoidal_cat
    : category
    := total_category functor_strong_monoidal_disp_cat.

End StrongMonoidalFunctorCategory.

Definition LaxMonoidalFunctorCat
           (M N : monoidal_cat)
  : category
  := functor_monoidal_cat
       (monoidal_cat_left_unitor M)
       (monoidal_cat_left_unitor N)
       (monoidal_cat_right_unitor M)
       (monoidal_cat_right_unitor N)
       (monoidal_cat_associator M)
       (monoidal_cat_associator N).

Definition StrongMonoidalFunctorCat
           (M N : monoidal_cat)
  : category
  := strong_functor_monoidal_cat
       (monoidal_cat_left_unitor M)
       (monoidal_cat_left_unitor N)
       (monoidal_cat_right_unitor M)
       (monoidal_cat_right_unitor N)
       (monoidal_cat_associator M)
       (monoidal_cat_associator N).

Section FunctorMonoidalProperties.

  Context {C D E : category}
          {TC : functor (C ⊠ C) C} {TD : functor (D ⊠ D) D}
          {TE : functor (E ⊠ E) E}
          {IC : C} {ID : D} {IE : E}.

  Notation "X ⊗_C Y" := (TC (X , Y)) (at level 31).
  Notation "f #⊗_C g" := (# TC (f #, g)) (at level 31).
  Notation "X ⊗_D Y" := (TD (X , Y)) (at level 31).
  Notation "f #⊗_D g" := (# TD (f #, g)) (at level 31).
  Notation "X ⊗_E Y" := (TE (X , Y)) (at level 31).
  Notation "f #⊗_E g" := (# TE (f #, g)) (at level 31).

  Definition functor_lu_composition
             {luC : left_unitor TC IC} {luD : left_unitor TD ID} {luE : left_unitor TE IE}
             {F : functor C D} {G : functor D E}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             {GG : functor_tensorunit_disp_cat TD TE ID IE G}
             (FFF : functor_lu_disp_cat luC luD (_,,FF))
             (GGG : functor_lu_disp_cat luD luE (_,,GG))
    : functor_lu_disp_cat luC luE (_,, functor_tensorunit_composition FF GG).
  Proof.
    intro x.
    refine (GGG (F x) @ _).
    cbn.
    unfold functor_unit_composition.

    etrans.
    2: {
      apply maponpaths.
      rewrite (! id_left (id G (F x))).
      rewrite binprod_comp.
      exact (! functor_comp TE _ _).
    }

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      rewrite <- functor_id.
      exact (nat_trans_ax (pr1 GG) _ _ (pr2 FF #, id (F x))).
    }

    simpl.
    apply maponpaths_2.
    rewrite ! assoc.
    apply maponpaths_2.
    do 2 rewrite <- (functor_comp G).
    apply maponpaths.

    exact (FFF x).
  Qed.

  Definition functor_ru_composition
             {ruC : right_unitor TC IC} {ruD : right_unitor TD ID} {ruE : right_unitor TE IE}
             {F : functor C D} {G : functor D E}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             {GG : functor_tensorunit_disp_cat TD TE ID IE G}
             (FFF : functor_ru_disp_cat ruC ruD (_,,FF))
             (GGG : functor_ru_disp_cat ruD ruE (_,,GG))
    : functor_ru_disp_cat ruC ruE (_,, functor_tensorunit_composition FF GG).
  Proof.
    intro x.
    refine (GGG (F x) @ _).
    cbn.
    unfold functor_unit_composition.

    etrans.
    2: {
      apply maponpaths.
      rewrite (! id_left (id G (F x))).
      rewrite binprod_comp.
      exact (! functor_comp TE _ _).
    }

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      rewrite <- functor_id.
      exact (nat_trans_ax (pr1 GG) _ _ (id (F x) #, pr2 FF)).
    }

    simpl.
    apply maponpaths_2.
    rewrite ! assoc.
    apply maponpaths_2.
    do 2 rewrite <- (functor_comp G).
    apply maponpaths.

    exact (FFF x).
  Qed.

  Definition functor_ass_composition
             {αC : associator TC} {αD : associator TD} {αE : associator TE}
             {F : functor C D} {G : functor D E}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             {GG : functor_tensorunit_disp_cat TD TE ID IE G}
             (FFF : functor_ass_disp_cat αC αD (_,,FF))
             (GGG : functor_ass_disp_cat αD αE (_,,GG))
    : functor_ass_disp_cat αC αE (_,, functor_tensorunit_composition FF GG).
  Proof.
    intros x y z. cbn.

    etrans.
    2: {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      rewrite <- (id_right (id G (F x))).
      rewrite binprod_comp.
      rewrite (functor_comp TE).
      rewrite assoc.
      apply maponpaths_2.
      rewrite <- functor_id.
      exact (nat_trans_ax (pr1 GG) _ _ (id (F x) #, (pr11 FF) (y, z))).
    }

    simpl.
    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      do 2 rewrite assoc'.
      apply maponpaths.
      rewrite assoc.
      exact (GGG (F x) (F y) (F z)).
    }

    rewrite ! assoc.
    rewrite <- (id_right (id G (F z))).
    rewrite binprod_comp.
    rewrite (functor_comp TE).
    rewrite ! assoc.
    apply maponpaths_2.
    do 3 rewrite <- (functor_comp G).

    etrans.
    2: {
      apply maponpaths_2.
      apply maponpaths.
      exact (FFF x y z).
    }

    rewrite ! (functor_comp G).
    rewrite ! assoc'.
    do 2 apply maponpaths.

    rewrite <- (functor_id G).
    exact (! nat_trans_ax (pr1 GG) _ _ ((pr11 FF) (x, y) #, id (F z))).
  Qed.

  Definition functor_monoidal_composition
             {luC : left_unitor TC IC} {luD : left_unitor TD ID} {luE : left_unitor TE IE}
             {ruC : right_unitor TC IC} {ruD : right_unitor TD ID} {ruE : right_unitor TE IE}
             {αC : associator TC} {αD : associator TD} {αE : associator TE}
             {F : functor C D} {G : functor D E}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             {GG : functor_tensorunit_disp_cat TD TE ID IE G}
             (FFF : functor_monoidal_disp_cat luC luD ruC ruD αC αD (_,,FF))
             (GGG : functor_monoidal_disp_cat luD luE ruD ruE αD αE (_,,GG))
    : functor_monoidal_disp_cat luC luE ruC ruE αC αE (_,, functor_tensorunit_composition FF GG).
  Proof.
    repeat split.
    - use functor_lu_composition.
      exact luD.
      exact (pr11 FFF).
      exact (pr11 GGG).
    - use functor_ru_composition.
      exact ruD.
      exact (pr21 FFF).
      exact (pr21 GGG).
    - use functor_ass_composition.
      exact αD.
      exact (pr2 FFF).
      exact (pr2 GGG).
  Defined.

End FunctorMonoidalProperties.

Section AssociatorMonoidalProperty.

  Definition pair_nat_trans
             {C1 C2 D1 D2 : category}
             {F1 G1 : functor C1 D1}
             {F2 G2 : functor C2 D2}
             (α : nat_trans F1 G1)
             (β : nat_trans F2 G2)
    : nat_trans (pair_functor F1 F2) (pair_functor G1 G2).
  Proof.
    use make_nat_trans.
    - intro x.
      use catbinprodmor.
      + exact (α (pr1 x)).
      + exact (β (pr2 x)).
    - abstract (intro ; intros ; use total2_paths_f ;
                   [ apply (pr2 α) | rewrite transportf_const ; apply (pr2 β) ]
               ).
  Defined.

  Definition pair_nat_z_iso
             {C1 C2 D1 D2 : category}
             {F1 G1 : functor C1 D1}
             {F2 G2 : functor C2 D2}
             (α : nat_z_iso F1 G1)
             (β : nat_z_iso F2 G2)
    : nat_z_iso (pair_functor F1 F2) (pair_functor G1 G2).
  Proof.
    use make_nat_z_iso.
    { exact (pair_nat_trans α β). }
    intro x.
    use tpair.
    - use catbinprodmor.
      + exact (pr1 (pr2 α (pr1 x))).
      + exact (pr1 (pr2 β (pr2 x))).
    - abstract (
          split ; (use total2_paths_f ;
                   [ apply (pr2 α) | rewrite transportf_const ; apply (pr2 β) ]
                  )
        ).
  Defined.

  Lemma unassoc_commutes
        {C D : category} (F : functor C D)
    : nat_z_iso ((pair_functor (pair_functor F F) F) ∙ (precategory_binproduct_unassoc D D D))
                ((precategory_binproduct_unassoc C C C) ∙ (pair_functor F (pair_functor F F))).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro ; use catbinprodmor ; apply identity.
      + intro ; intros.
        use total2_paths_f.
        * exact (id_right _ @ ! id_left _).
        * abstract (rewrite transportf_const ; exact (id_right _ @ ! id_left _)).
    - intro.
      use tpair.
      * use catbinprodmor ; apply identity.
      * abstract (split ; (use total2_paths_f ; [ apply id_right | rewrite transportf_const ; apply id_right ])).
  Defined.

  Lemma assoc_right_commutes_with_triple_pairing
        {C D : category}
        (F : functor C D)
        {TC : functor (C ⊠ C) C}
        {TD : functor (D ⊠ D) D}
        {FF : functor_tensor TC TD F}
        (FF_iso : is_nat_z_iso FF)
    : nat_z_iso
        (pair_functor (pair_functor F F) F ∙ assoc_right TD) (assoc_right TC ∙ F).
  Proof.
    (* This commuting diagram can be split in 3 commuting diagrams stacked together *)
    (* Step 1: The top commuting diagram is unassoc_commutes *)
    use nat_z_iso_comp.
    2: apply nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    2: {
      use post_whisker_nat_z_iso.
      2: apply unassoc_commutes.
    }
    use nat_z_iso_comp.
    2: apply (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    3: apply nat_z_iso_functor_comp_assoc.
    apply pre_whisker_nat_z_iso.

    (* Step 2: The lowest commuting diagram is the tensor preserving commuting one *)
    use nat_z_iso_comp.
    3: apply nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    3: {
      apply pre_whisker_nat_z_iso.
      exact (nat_z_iso_inv (FF ,, FF_iso : nat_z_iso _ _)).
    }

    use nat_z_iso_comp.
    3: apply (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    2: apply nat_z_iso_functor_comp_assoc.
    apply post_whisker_nat_z_iso.

    (* Step 3: The middle commuting square is the tensor preserving commuting one
               but tensored with the identity functor on the left *)

    use product_of_commuting_squares.
    { apply (make_nat_z_iso _ _ _ (is_nat_z_iso_nat_trans_id F)). }
    apply (nat_z_iso_inv (FF ,, FF_iso)).
  Defined.

  Lemma pair_functor_composite
        {C1 C2 C3 D1 D2 D3 : category}
        (F1 : functor C1 C2)
        (G1 : functor D1 D2)
        (F2 : functor C2 C3)
        (G2 : functor D2 D3)
    : nat_z_iso
        (functor_composite (pair_functor F1 G1) (pair_functor F2 G2))
        (pair_functor (functor_composite F1 F2) (functor_composite G1 G2)).
  Proof.
    use make_nat_z_iso.
    { apply nat_trans_id. }
    intro.
    use tpair.
    - use catbinprodmor ; apply identity.
    - split ; apply id_right.
  Defined.

  Lemma assoc_left_commutes_with_triple_pairing
        {C D : category}
        (F : functor C D)
        {TC : functor (C ⊠ C) C}
        {TD : functor (D ⊠ D) D}
        {FF : functor_tensor TC TD F}
        (FF_iso : is_nat_z_iso FF)
    :  nat_z_iso ((pair_functor (pair_functor F F) F) ∙ assoc_left TD) (assoc_left TC ∙ F).
  Proof.
    unfold assoc_left.
    use nat_z_iso_comp.
    2: apply nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    2: {
      use post_whisker_nat_z_iso.
      2: apply pair_functor_composite.
    }
    use nat_z_iso_comp.
    2: {
      use post_whisker_nat_z_iso.
      2: {
        use pair_nat_z_iso.
        3: exact (nat_z_iso_inv (FF ,, FF_iso)).
        2: {
          exists (nat_trans_id _).
          apply is_nat_z_iso_nat_trans_id.
        }
      }
    }
    unfold functor_tensor_map_codom.
    use nat_z_iso_comp.
    2: {
      use post_whisker_nat_z_iso.
      2: {
        use pair_nat_z_iso.
        3: {
          exists (nat_trans_id _).
          apply is_nat_z_iso_nat_trans_id.
        }
        2: apply functor_commutes_with_id.
      }
    }

    use nat_z_iso_comp.
    2: {
      use post_whisker_nat_z_iso.
      2: apply (nat_z_iso_inv (pair_functor_composite _ _ _ _)).
    }
    use nat_z_iso_comp.
    2: apply (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    2: {
      use pre_whisker_nat_z_iso.
      2: exact (nat_z_iso_inv (FF ,, FF_iso)).
    }
    apply nat_z_iso_functor_comp_assoc.
  Defined.

End AssociatorMonoidalProperty.

Section StrongMonoidalProperty.

  Context {C D E : category}
          {TC : functor (C ⊠ C) C} {TD : functor (D ⊠ D) D} {TE : functor (E ⊠ E) E}
          {IC : C} {ID : D} {IE : E}
          {luC : left_unitor TC IC} {luD : left_unitor TD ID} {luE : left_unitor TE IE}
          {ruC : right_unitor TC IC} {ruD : right_unitor TD ID} {ruE : right_unitor TE IE}
          {αC : associator TC} {αD : associator TD} {αE : associator TE}.

  Notation "X ⊗_C Y" := (TC (X , Y)) (at level 31).
  Notation "f #⊗_C g" := (# TC (f #, g)) (at level 31).
  Notation "X ⊗_D Y" := (TD (X , Y)) (at level 31).
  Notation "f #⊗_D g" := (# TD (f #, g)) (at level 31).
  Notation "X ⊗_E Y" := (TE (X , Y)) (at level 31).
  Notation "f #⊗_E g" := (# TE (f #, g)) (at level 31).

  Definition strong_functor_composition
             {F : functor_monoidal_cat luC luD ruC ruD αC αD}
             {G : functor_monoidal_cat luD luE ruD ruE αD αE}
             (FF : functor_strong_monoidal_disp_cat luC luD ruC ruD αC αD F)
             (GG : functor_strong_monoidal_disp_cat luD luE ruD ruE αD αE G)
    : functor_strong_monoidal_disp_cat
        luC luE ruC ruE αC αE
        (_,, functor_monoidal_composition (pr2 F) (pr2 G)).
  Proof.
    split.
    - intro cc.
      use is_z_isomorphism_comp.
      1: apply (pr2 (functor_on_z_iso (pr11 G) (_,, pr1 FF cc))).
      exact (pr1 GG  ((pr111 F) (pr1 cc), (pr111 F) (pr2 cc))).
    - use is_z_isomorphism_comp.
      + exact (pr2 (functor_on_z_iso (pr11 G) (make_z_iso' _ (pr2 FF)))).
      + exact (pr2 GG).
  Defined.

End StrongMonoidalProperty.
