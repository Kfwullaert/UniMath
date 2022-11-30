(**
  Lax Monoidal categories: Monoidal categories where the unitors and associator are not invertible
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Notation "'id' X" := (identity X) (at level 30).

Notation "C ⊠ D" := (category_binproduct C D) (at level 38).
Notation "( c , d )" := (make_catbinprod c d).
Notation "( f #, g )" := (catbinprodmor f g).

Section Monoidal_Precat.

Context {C : category} (tensor : C ⊠ C ⟶ C) (I : C).

Notation "X ⊗ Y" := (tensor (X, Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Lemma tensor_id {X Y : C} : id X #⊗ id Y = id (X ⊗ Y).
Proof.
  apply (functor_id tensor).
Qed.

Lemma tensor_comp {X Y Z X' Y' Z' : C} (f : X --> Y) (g : Y --> Z) (f' : X' --> Y') (g' : Y' --> Z') :
  (f · g) #⊗ (f' · g') = f #⊗ f' · g #⊗ g'.
Proof.
  rewrite binprod_comp.
  apply (functor_comp tensor).
Qed.

Definition is_z_iso_tensor_z_iso {X Y X' Y' : C} {f : X --> Y} {g : X' --> Y'}
           (f_is_z_iso : is_z_isomorphism f) (g_is_z_iso : is_z_isomorphism g) : is_z_isomorphism (f #⊗ g).
Proof.
  exact (functor_on_is_z_isomorphism _ (is_z_iso_binprod_z_iso f_is_z_iso g_is_z_iso)).
Defined.

(* I ⊗ - *)
Definition I_pretensor : C ⟶ C := functor_fix_fst_arg _ _ _ tensor I.

Lemma I_pretensor_ok: functor_on_objects I_pretensor = λ c, I ⊗ c.
Proof.
  apply idpath.
Qed.

(* λ *)
Definition left_unitor : UU :=
  nat_trans I_pretensor (functor_identity C).

Definition left_unitor_funclass (λ' : left_unitor):
  ∏ x : ob C, I_pretensor x -->  x
  := pr1 λ'.
Coercion left_unitor_funclass : left_unitor >-> Funclass.

(* - ⊗ I *)
Definition I_posttensor : C ⟶ C := functor_fix_snd_arg _ _ _ tensor I.

Lemma I_posttensor_ok: functor_on_objects I_posttensor = λ c, c ⊗ I.
Proof.
  apply idpath.
Qed.

(* ρ *)
Definition right_unitor : UU :=
  nat_trans I_posttensor (functor_identity C).

Definition right_unitor_funclass (ρ' : right_unitor):
  ∏ x : ob C, I_posttensor x -->  x
  := pr1 ρ'.
Coercion right_unitor_funclass : right_unitor >-> Funclass.

(* (- ⊗ =) ⊗ ≡ *)
Definition assoc_left : (C ⊠ C) ⊠ C ⟶ C :=
  functor_composite (pair_functor tensor (functor_identity _)) tensor.

Lemma assoc_left_ok: functor_on_objects assoc_left =
  λ c, (ob1 (ob1 c) ⊗ ob2 (ob1 c)) ⊗ ob2 c.
Proof.
  apply idpath.
Qed.

(* - ⊗ (= ⊗ ≡) *)
Definition assoc_right : (C ⊠ C) ⊠ C ⟶ C :=
  functor_composite
    (precategory_binproduct_unassoc _ _ _)
    (functor_composite (pair_functor (functor_identity _) tensor) tensor).

Lemma assoc_right_ok: functor_on_objects assoc_right =
  λ c, ob1 (ob1 c) ⊗ (ob2 (ob1 c) ⊗ ob2 c).
Proof.
  apply idpath.
Qed.

(* α *)
Definition associator : UU :=
  nat_trans assoc_left assoc_right.
(* This definition goes in the opposite direction of that by Mac Lane (CWM 2nd ed., p.162)
   but conforms to the def. on Wikipedia. *)

Definition associator_funclass (α' : associator):
  ∏ x : ob ((C ⊠ C) ⊠ C), assoc_left x -->  assoc_right x
  := pr1 α'.
Coercion associator_funclass : associator >-> Funclass.

Definition triangle_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
  ∏ (a b : C), pr1 ρ' a #⊗ id b = pr1 α' ((a, I), b) · id a #⊗ pr1 λ' b.

Definition pentagon_eq (α' : associator) : UU :=
  ∏ (a b c d : C), pr1 α' ((a ⊗ b, c), d) · pr1 α' ((a, b), c ⊗ d) =
   pr1 α' ((a, b), c) #⊗ id d · pr1 α' ((a, b ⊗ c), d) · id a #⊗ pr1 α' ((b, c), d).

End Monoidal_Precat.

Definition monoidal_cat : UU :=
  ∑ C : category, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor,
         (triangle_eq tensor I λ' ρ' α') × (pentagon_eq tensor α').

(*
Definition monoidal_precat_struct : UU :=
  ∑ C : precategory, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor, unit.

Definition make_monoidal_precat_struct (C: precategory)(tensor: C ⊠ C ⟶ C)(I: C)
  (λ': left_unitor tensor I)(ρ': right_unitor tensor I)(α': associator tensor): monoidal_precat_struct :=
  (C,, (tensor,, (I,, (λ',, (ρ',, (α',, tt)))))).
*)

Definition make_monoidal_cat (C: category)(tensor: C ⊠ C ⟶ C)(I: C)
  (λ': left_unitor tensor I)(ρ': right_unitor tensor I)(α': associator tensor)
  (eq1: triangle_eq tensor I λ' ρ' α')(eq2: pentagon_eq tensor α'): monoidal_cat :=
  (C,, (tensor,, (I,, (λ',, (ρ',, (α',, (eq1,, eq2))))))).

Definition monoidal_cat_cat (M : monoidal_cat) : category := pr1 M.
Coercion monoidal_cat_cat : monoidal_cat >-> category.

Section Monoidal_Cat_Accessors.

  Context (M : monoidal_cat).

  (** it is important that no new coercions are used in the given types in the following projections *)

Definition monoidal_cat_tensor : pr1 M ⊠ pr1 M ⟶ pr1 M := pr1 (pr2 M).

Definition monoidal_cat_unit : pr1 M := pr1 (pr2 (pr2 M)).

Definition monoidal_cat_left_unitor : left_unitor (pr1 (pr2 M)) (pr1 (pr2 (pr2 M))) := pr1 (pr2 (pr2 (pr2 M))).

Definition monoidal_cat_right_unitor : right_unitor (pr1 (pr2 M)) (pr1 (pr2 (pr2 M))) := pr1 (pr2 (pr2 (pr2 (pr2 M)))).

Definition monoidal_cat_associator : associator (pr1 (pr2 M)) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

Definition monoidal_cat_triangle_eq : triangle_eq (pr1 (pr2 M)) (pr1 (pr2 (pr2 M))) (pr1 (pr2 (pr2 (pr2 M)))) (pr1 (pr2 (pr2 (pr2 (pr2 M))))) (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))).

Definition monoidal_cat_pentagon_eq : pentagon_eq (pr1 (pr2 M)) (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))) := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))).

End Monoidal_Cat_Accessors.

Section coherence_lemmas.

Context {Mon_V : monoidal_cat}.

Let I        : Mon_V                  := monoidal_cat_unit Mon_V.
Let tensor   : Mon_V ⊠ Mon_V ⟶ Mon_V := monoidal_cat_tensor Mon_V.
Let α        : associator tensor      := monoidal_cat_associator Mon_V.
Let l_unitor : left_unitor tensor I   := monoidal_cat_left_unitor Mon_V.
Let r_unitor : right_unitor tensor I  := monoidal_cat_right_unitor Mon_V.

Local Notation "X ⊗ Y" := (tensor (X, Y)).
Local Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Lemma tensor_comp_left {X Y Z W : Mon_V} (f : X --> Y) (g : Y --> Z) : ((f · g) #⊗ id W) = (f #⊗ id W) · (g #⊗ id W).
Proof.
  rewrite <- (functor_comp tensor).
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  rewrite id_left.
  apply idpath.
Defined.

Lemma tensor_comp_right {X Y Z W : Mon_V} (f : X --> Y) (g : Y --> Z) : (id W #⊗ (f · g)) = (id W #⊗ f) · (id W #⊗ g).
Proof.
  rewrite <- (functor_comp tensor).
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  rewrite id_left.
  apply idpath.
Defined.

(* Corollaries for the inverses of left and right unitors. *)

Lemma tensor_z_isomorphism_left : ∏ (x y z : Mon_V) (f : x --> y) (f_z_iso : is_z_isomorphism f), # tensor (is_z_isomorphism_mor f_z_iso #, id z) = is_z_isomorphism_mor (functor_on_is_z_isomorphism (functor_fix_snd_arg _ _ _ tensor z) f_z_iso).
Proof.
  intros.
  reflexivity.
Qed.

Lemma tensor_z_isomorphism_right : ∏ (x y z : Mon_V) (f : x --> y) (f_z_iso : is_z_isomorphism f), # tensor (id z #, is_z_isomorphism_mor f_z_iso) = is_z_isomorphism_mor (functor_on_is_z_isomorphism (functor_fix_fst_arg _ _ _ tensor z) f_z_iso).
Proof.
  intros.
  reflexivity.
Qed.

End coherence_lemmas.
