(* In this file, the (underlying) notions of dagger categories and dagger functors are formalized *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Local Open Scope cat.

Section DaggerCategories.

  Definition dagger_structure (C : category) : UU
    := ∏ x y : C, C⟦x,y⟧ → C⟦y,x⟧.

  Lemma isaset_dagger_structure (C : category)
    : isaset (dagger_structure C).
  Proof.
    do 2 (apply impred_isaset ; intro).
    apply funspace_isaset.
    apply homset_property.
  Qed.

  Definition dagger_law_id {C : category} (dag : dagger_structure C)
    : UU
    := ∏ x : C, dag x x (identity x) = identity x.

  Definition dagger_law_comp {C : category} (dag : dagger_structure C)
    : UU
    := ∏ (x y z : C) (f: C⟦x,y⟧) (g : C⟦y,z⟧), dag x z (f · g) = dag y z g · dag x y f.

  Definition dagger_law_idemp {C : category} (dag : dagger_structure C)
    : UU
    := ∏ (x y : C) (f : C⟦x,y⟧), dag y x (dag x y f) = f.

  Definition dagger_laws {C : category} (dag : dagger_structure C)
    : UU := dagger_law_id dag × dagger_law_comp dag × dagger_law_idemp dag.

  Lemma isaprop_dagger_laws {C : category} (dag : dagger_structure C)
    : isaprop (dagger_laws dag).
  Proof.
    repeat (apply isapropdirprod)
    ; repeat (apply impred_isaprop ; intro)
    ; apply homset_property.
  Qed.

  Definition dagger (C : category)
    : UU
    := ∑ d : dagger_structure C, dagger_laws d.

  Definition dagger_to_struct {C : category} (dag : dagger C)
    : dagger_structure C := pr1 dag.
  Coercion dagger_to_struct : dagger >-> dagger_structure.

  Definition dagger_to_laws {C : category} (dag : dagger C)
    : dagger_laws dag := pr2 dag.

  Definition dagger_to_law_id
             {C : category} (dag : dagger C)
    : dagger_law_id dag := pr1 (dagger_to_laws dag).

  Definition dagger_to_law_comp
             {C : category} (dag : dagger C)
    : dagger_law_comp dag := pr12 (dagger_to_laws dag).

  Definition dagger_to_law_idemp
             {C : category} (dag : dagger C)
    : dagger_law_idemp dag := pr22 (dagger_to_laws dag).

  Lemma isaset_dagger (C : category)
    : isaset (dagger C).
  Proof.
    apply isaset_total2.
    - apply isaset_dagger_structure.
    - intro ; apply isasetaprop ; apply isaprop_dagger_laws.
  Qed.

  Definition is_dagger_functor {C D : category}
             (dagC : dagger_structure C) (dagD : dagger_structure D)
             (F : functor C D)
    : UU
    := ∏ (x y : C) (f : C⟦x,y⟧), #F (dagC _ _ f) = dagD _ _ (#F f).

  Lemma isaprop_is_dagger_functor
        {C D : category}
        (dagC : dagger_structure C) (dagD : dagger_structure D)
        (F : functor C D)
    : isaprop (is_dagger_functor dagC dagD F).
  Proof.
    repeat (apply impred_isaprop ; intro) ; apply homset_property.
  Qed.

  Definition dagger_functor_id
             {C : category} (dag : dagger C)
    : is_dagger_functor dag dag (functor_identity C).
  Proof.
    intro ; intros ; apply idpath.
  Qed.

  Definition is_dagger_functor_comp {C D E : category}
             {dagC : dagger_structure C} {dagD : dagger_structure D} {dagE : dagger_structure E}
             {F : functor C D} {G : functor D E}
             (dF : is_dagger_functor dagC dagD F)
             (dG : is_dagger_functor dagD dagE G)
    : is_dagger_functor dagC dagE (functor_composite F G).
  Proof.
    intros x y f.
    cbn.
    etrans.
    1: apply maponpaths, dF.
    apply dG.
  Qed.

End DaggerCategories.
