(** In this file, the category of comonoids internal to a monoidal category is defined

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.

Local Open Scope cat.

Section Category_of_Comonoids.

  Context {C : category} (M : monoidal C).

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : C := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.
  Let luinv : leftunitorinv_data M (monoidal_unit M) := monoidal_leftunitorinvdata M.
  Let ruinv : rightunitorinv_data M (monoidal_unit M) := monoidal_rightunitorinvdata M.
  Let αinv : associatorinv_data M := monoidal_associatorinvdata M.

  Definition comonoid_data (x : C) : UU
    := C⟦x, x ⊗ x⟧ × C⟦x, I⟧.

  Definition comonoid_data_comultiplication {x : C} (m : comonoid_data x)
    : C⟦x, x ⊗ x⟧
    := pr1 m.
  Notation "μ_{ m }" := (comonoid_data_comultiplication m).

  Definition comonoid_data_counit {x : C} (m : comonoid_data x)
    : C⟦x, I⟧
    := pr2 m.
  Notation "η_{ m }" := (comonoid_data_counit m).

  Definition comonoid_laws_assoc {x : C} (m : comonoid_data x) : UU
    := μ_{m} · (μ_{m} ⊗r x) · α x x x = μ_{m} · x ⊗l μ_{m}.

  Definition comonoid_laws_unit_left {x : C} (m : comonoid_data x) : UU
    := μ_{m} · (η_{m} ⊗r x) · lu x = identity x.
  Definition comonoid_laws_unit_right {x : C} (m : comonoid_data x) : UU
    := μ_{m} · (x ⊗l η_{m}) · ru x = identity x.

  Definition comonoid_laws {x : C} (m : comonoid_data x) : UU
    := comonoid_laws_unit_left m × comonoid_laws_unit_right m × comonoid_laws_assoc m.

  Lemma isaprop_comonoid_laws {x : C} (m : comonoid_data x)
    : isaprop (comonoid_laws m).
  Proof.
    repeat (apply isapropdirprod) ; apply homset_property.
  Qed.

  Definition comonoid (x : C) : UU
    := ∑ m : comonoid_data x, comonoid_laws m.

  Definition comonoid_to_comonoid_data {x : C} (m : comonoid x)
    : comonoid_data x := pr1 m.
  Coercion comonoid_to_comonoid_data : comonoid >-> comonoid_data.

  Definition comonoid_to_comonoid_laws {x : C} (m : comonoid x)
    : comonoid_laws m := pr2 m.

  Definition comonoid_to_unit_left_law {x : C} (m : comonoid x)
    : comonoid_laws_unit_left m := pr1 (comonoid_to_comonoid_laws m).

  Definition comonoid_to_unit_right_law {x : C} (m : comonoid x)
    : comonoid_laws_unit_right m := pr12 (comonoid_to_comonoid_laws m).

  Definition comonoid_to_assoc_law {x : C} (m : comonoid x)
    : comonoid_laws_assoc m := pr22 (comonoid_to_comonoid_laws m).

  Definition is_comonoid_mor_mult {x y : C}
             (mx : comonoid x) (my : comonoid y) (f : C⟦x,y⟧) : UU
    := μ_{mx} · (f ⊗⊗ f) = f · μ_{my}.

  Definition is_comonoid_mor_unit {x y : C}
             (mx : comonoid x) (my : comonoid y) (f : C⟦x,y⟧) : UU
    := f · η_{my} = η_{mx}.

  Definition is_comonoid_mor {x y : C}
             (mx : comonoid x) (my : comonoid y) (f : C⟦x,y⟧) : UU
    := is_comonoid_mor_mult mx my f × is_comonoid_mor_unit mx my f.

  Lemma isaprop_is_comonoid_mor {x y : C}
        (mx : comonoid x) (my : comonoid y) (f : C⟦x,y⟧)
    : isaprop (is_comonoid_mor mx my f).
  Proof.
    apply isapropdirprod ; apply homset_property.
  Qed.

  Definition comonoid_disp_cat_ob_mor : disp_cat_ob_mor C.
  Proof.
    exists (λ x, comonoid x).
    exact (λ x y mx my f, is_comonoid_mor mx my f).
  Defined.

  Lemma id_is_comonoid_mor {x : C} (xx : comonoid x)
    : is_comonoid_mor xx xx (identity x).
  Proof.
    split.
    - refine (_ @ ! id_left _).
      etrans. {
        apply maponpaths, bifunctor_distributes_over_id.
        apply (bifunctor_leftid M).
        apply (bifunctor_rightid M).
      }
      apply id_right.
    - apply id_left.
  Qed.

  Lemma comp_is_comonoid_mor {x y z : C}
        {f : C ⟦ x, y ⟧} {g : C ⟦ y, z ⟧}
        {xx : comonoid x} {yy : comonoid y} {zz : comonoid z}
        (pf : is_comonoid_mor xx yy f) (pg : is_comonoid_mor yy zz g)
    : is_comonoid_mor xx zz (f · g).
  Proof.
    split.
    - etrans. {
        apply maponpaths.
        apply bifunctor_distributes_over_comp.
        apply (bifunctor_leftcomp M).
        apply (bifunctor_rightcomp M).
        apply (bifunctor_equalwhiskers M).
      }
      etrans.
      { apply assoc. }
      etrans. {
        apply maponpaths_2.
        apply (pr1 pf).
      }
      etrans.
      { apply assoc'. }
      etrans. {
        apply maponpaths.
        apply (pr1 pg).
      }
      apply assoc.
    - unfold is_comonoid_mor_unit.
      etrans.
      { apply assoc'. }
      etrans. {
        apply maponpaths.
        apply (pr2 pg).
      }
      apply (pr2 pf).
  Qed.

  Definition comonoid_disp_cat_id_comp
    : disp_cat_id_comp C comonoid_disp_cat_ob_mor.
  Proof.
    split.
    - intro ; intro ; apply id_is_comonoid_mor.
    - intros x y z f g xx yy zz pf pg.
      exact (comp_is_comonoid_mor pf pg).
  Qed.

  Definition comonoid_disp_cat_data : disp_cat_data C.
  Proof.
    exists comonoid_disp_cat_ob_mor.
    exact comonoid_disp_cat_id_comp.
  Defined.

  Definition comonoid_disp_cat_axioms
    : disp_cat_axioms C comonoid_disp_cat_data.
  Proof.
    repeat split ; intro ; intros ; try (apply isaprop_is_comonoid_mor).
    apply isasetaprop ; apply isaprop_is_comonoid_mor.
  Qed.

  Definition comonoid_disp_cat : disp_cat C.
  Proof.
    exists comonoid_disp_cat_data.
    exact comonoid_disp_cat_axioms.
  Defined.

  Definition category_of_comonoids_in_comonoidal_cat : category
    := total_category comonoid_disp_cat.

  Let COMON : category := category_of_comonoids_in_comonoidal_cat.

  Definition comonoid_carrier
             (X : COMON)
    : ob C := pr1 X.

  Definition comonoid_struct (X : COMON)
    : comonoid (comonoid_carrier X)
    := pr2 X.

  Definition comonoid_comultiplication (X : COMON)
    : C⟦comonoid_carrier X, comonoid_carrier X ⊗_{ M} comonoid_carrier X⟧
    := comonoid_data_comultiplication (comonoid_struct X).

  Definition comonoid_counit (X : COMON)
    : C⟦comonoid_carrier X, I⟧
    := comonoid_data_counit (comonoid_struct X).

  Definition comonoid_left_counit_law (X : COMON)
    : comonoid_laws_unit_left (comonoid_struct X)
    := comonoid_to_unit_left_law (comonoid_struct X).

  Definition comonoid_right_counit_law (X : COMON)
    : comonoid_laws_unit_right (comonoid_struct X)
    := comonoid_to_unit_right_law (comonoid_struct X).

  Definition comonoid_assoc_law (X : COMON)
    : comonoid_laws_assoc (comonoid_struct X)
    := comonoid_to_assoc_law (comonoid_struct X).

End Category_of_Comonoids.

Section Monoidal_Category_of_Comonoids.

  Search "symm".
  Context {C : category} {M : monoidal C} (S : symmetric M).

  Notation "x ⊗ y" := (x ⊗_{M} y).
  Notation "x ⊗l f" := (x ⊗^{M}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{M}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{M} g) (at level 31).

  Let I : C := monoidal_unit M.
  Let lu : leftunitor_data M (monoidal_unit M) := monoidal_leftunitordata M.
  Let ru : rightunitor_data M (monoidal_unit M) := monoidal_rightunitordata M.
  Let α : associator_data M := monoidal_associatordata M.
  Let luinv : leftunitorinv_data M (monoidal_unit M) := monoidal_leftunitorinvdata M.
  Let ruinv : rightunitorinv_data M (monoidal_unit M) := monoidal_rightunitorinvdata M.
  Let αinv : associatorinv_data M := monoidal_associatorinvdata M.

  Notation "σ_{ x , y }" := (monoidal_braiding_data (symmetric_to_braiding S) x y).
  Notation "μ_{ m }" := (comonoid_data_comultiplication _ m).
  Notation "η_{ m }" := (comonoid_data_counit _ m).

  Definition tensor_of_comonoids_data
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : comonoid_data M (x ⊗ y).
  Proof.
    split.
    - refine (μ_{mx} ⊗⊗ μ_{my} · _).
      refine (αinv (x ⊗ x) y y · _).
      refine (α x x y ⊗r y · _).
      refine ((x ⊗l σ_{x,y}) ⊗r y · _).
      refine (_ · α (x ⊗ y) x y).
      refine (αinv _ _ _ ⊗r y).
    - refine (η_{mx} ⊗⊗ η_{my} · lu _).
  Defined.

  Lemma tensor_of_comonoids_laws
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : comonoid_laws M (tensor_of_comonoids_data mx my).
  Proof.
    refine (_ ,, _ ,, _).
    - unfold comonoid_laws_unit_left.
      cbn.
  Admitted.

  Definition tensor_of_comonoids
    {x y : C} (mx : comonoid M x) (my : comonoid M y)
    : comonoid M (x ⊗ y)
    := _ ,, tensor_of_comonoids_laws mx my.

  Definition tensor_of_comonoid_mor_mult_left
    {x y1 y2 : C} {g : C ⟦ y1, y2 ⟧}
    {xx : comonoid M x} {yy1 : comonoid M y1} {yy2 : comonoid M y2}
    (gg : is_comonoid_mor_mult M yy1 yy2 g)
    : is_comonoid_mor_mult M (tensor_of_comonoids xx yy1) (tensor_of_comonoids xx yy2) (x ⊗^{ M}_{l} g).
  Proof.
  Admitted.

  Definition tensor_of_comonoid_mor_unit_left
    {x y1 y2 : C} {g : C ⟦ y1, y2 ⟧}
    {xx : comonoid M x} {yy1 : comonoid M y1} {yy2 : comonoid M y2}
    (gg : is_comonoid_mor_unit M yy1 yy2 g)
    : is_comonoid_mor_unit M (tensor_of_comonoids xx yy1) (tensor_of_comonoids xx yy2) (x ⊗^{ M}_{l} g).
  Proof.
  Admitted.

  Definition tensor_of_comonoid_mor_left
    {x y1 y2 : C} {g : C ⟦ y1, y2 ⟧}
    {xx : comonoid M x} {yy1 : comonoid M y1} {yy2 : comonoid M y2}
    (gg : is_comonoid_mor M yy1 yy2 g)
    : is_comonoid_mor M (tensor_of_comonoids xx yy1) (tensor_of_comonoids xx yy2) (x ⊗^{ M}_{l} g).
  Proof.
    split.
    - apply (tensor_of_comonoid_mor_mult_left (pr1 gg)).
    - apply (tensor_of_comonoid_mor_unit_left (pr2 gg)).
  Qed.

  Definition tensor_of_comonoid_mor_mult_right
    {x y1 y2 : C} {g : C ⟦ y1, y2 ⟧}
    {xx : comonoid M x} {yy1 : comonoid M y1} {yy2 : comonoid M y2}
    (gg : is_comonoid_mor_mult M yy1 yy2 g)
    : is_comonoid_mor_mult M (tensor_of_comonoids yy1 xx) (tensor_of_comonoids yy2 xx) (g ⊗r x).
  Proof.
  Admitted.

  Definition tensor_of_comonoid_mor_unit_right
    {x y1 y2 : C} {g : C ⟦ y1, y2 ⟧}
    {xx : comonoid M x} {yy1 : comonoid M y1} {yy2 : comonoid M y2}
    (gg : is_comonoid_mor_unit M yy1 yy2 g)
    : is_comonoid_mor_unit M (tensor_of_comonoids yy1 xx) (tensor_of_comonoids yy2 xx) (g ⊗r x).
  Proof.
    unfold is_comonoid_mor_unit.
    cbn.
  Admitted.

  Definition tensor_of_comonoid_mor_right
    {x y1 y2 : C} {g : C ⟦ y1, y2 ⟧}
    {xx : comonoid M x} {yy1 : comonoid M y1} {yy2 : comonoid M y2}
    (gg : is_comonoid_mor M yy1 yy2 g)
    : is_comonoid_mor M (tensor_of_comonoids yy1 xx) (tensor_of_comonoids yy2 xx) (g ⊗r x).
  Proof.
    split.
    - apply (tensor_of_comonoid_mor_mult_right (pr1 gg)).
    - apply (tensor_of_comonoid_mor_unit_right (pr2 gg)).
  Qed.

  Definition comonoid_disp_tensor_data
    : disp_bifunctor_data M (comonoid_disp_cat M) (comonoid_disp_cat M) (comonoid_disp_cat M).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (λ x y mx my, tensor_of_comonoids mx my).
    - intro ; intros.
      apply tensor_of_comonoid_mor_left.
      assumption.
    - intro ; intros.
      apply tensor_of_comonoid_mor_right.
      assumption.
  Defined.

  Lemma comonoid_disp_tensor_laws
    : is_disp_bifunctor comonoid_disp_tensor_data.
  Proof.
    repeat split ; intro ; intros ; apply isaprop_is_comonoid_mor.
  Qed.

  Definition comonoid_disp_tensor
    :  disp_tensor (comonoid_disp_cat M) M.
  Proof.
    use tpair.
    - exact comonoid_disp_tensor_data.
    - exact comonoid_disp_tensor_laws.
  Defined.

  Definition comonoid_disp_unit_data
    : comonoid_data M (monoidal_unit M).
  Proof.
    exists (luinv _).
    apply identity.
  Defined.

  Lemma comonoid_disp_unit_laws
    : comonoid_laws M comonoid_disp_unit_data.
  Proof.
    refine (_ ,, _ ,, _).
    - unfold comonoid_laws_unit_left.
      cbn.
      rewrite (bifunctor_rightid M).
      rewrite id_right.
      apply monoidal_leftunitorisolaw.
    - unfold comonoid_laws_unit_right.
      cbn.
      rewrite (bifunctor_leftid M).
      rewrite id_right.
      admit.
    - unfold comonoid_laws_assoc.
      cbn.
      admit.
  Admitted.

  Definition comonoid_disp_unit
    :  comonoid_disp_cat M (monoidal_unit M).
  Proof.
    exists comonoid_disp_unit_data.
    exact comonoid_disp_unit_laws.
  Defined.

  Lemma TODO_JOKER (A : UU) : A. Proof. Admitted.
  Definition comonoid_disp_monoidal_data
    : disp_monoidal_data (comonoid_disp_cat M) M.
  Proof.
    exists comonoid_disp_tensor.
    exists comonoid_disp_unit.
    refine (_ ,, _ ,, _ ,, _ ,, _ ,, _) ; intro ; intros ; apply TODO_JOKER.
  Defined.

  Definition comonoid_disp_monoidal
    : disp_monoidal (comonoid_disp_cat M) M.
  Proof.
    exists comonoid_disp_monoidal_data.
    abstract (repeat split ; try (intro ; intros) ; apply isaprop_is_comonoid_mor).
  Defined.

  Definition monoidal_category_of_comonoids
    : monoidal (category_of_comonoids_in_comonoidal_cat M)
    := total_monoidal comonoid_disp_monoidal.

End Monoidal_Category_of_Comonoids.

Section Symmetric_Monoidal_Category_of_Comonoids.

End Symmetric_Monoidal_Category_of_Comonoids.
