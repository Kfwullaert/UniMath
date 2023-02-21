(* In this file, we have formalized the (correct) notion of isomorphisms of dagger categories, the so called unitary morphisms.
Notice that this definition is different compared to (non-dagger) categories, therefore, we can not reuse is_z_isomorphism. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.Bicategories.DaggerCategories.Core.

Local Open Scope cat.

Section UnitaryMorphisms.

  Definition is_unitary
             {C : category} (dag : dagger_structure C)
             {x y : C} (f : C⟦x,y⟧)
    : UU := is_inverse_in_precat f (dag x y f).

  Lemma isaprop_is_unitary
        {C : category} (dag : dagger_structure C)
        {x y : C} (f : C⟦x,y⟧)
    : isaprop (is_unitary dag f).
  Proof.
    apply isaprop_is_inverse_in_precat.
  Qed.

  Definition unitary {C : category} (dag : dagger_structure C)
             (x y : C)
    : UU
    := ∑ f : C⟦x,y⟧, is_unitary dag f.

  Lemma isaset_unitary
        {C : category} (dag : dagger_structure C) (x y : C)
    : isaset (unitary dag x y).
  Proof.
    apply isaset_total2.
    - apply homset_property.
    - intro ; apply isasetaprop ; apply isaprop_is_unitary.
  Qed.

  Definition unitary_id
             {C : category} (dag : dagger C)
             (x : C)
    : unitary dag x x.
  Proof.
    exists (identity_z_iso x).
    abstract (apply make_is_inverse_in_precat ;
              [ refine (id_left _ @ _) ; apply dagger_to_law_id
              | refine (id_right _ @ _) ; apply dagger_to_law_id ]).
  Defined.

End UnitaryMorphisms.
