module

public import BondalThomsen.Ports.TauCeti.Algebra.Homology.Ext.Basic
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Skyscraper

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.CategoryTheory (freeYonedaSheafFunctor freeYonedaSheafSectionsEquiv sheafH'_eq
  freeYonedaSheafSectionsEquiv_naturality_left freeYonedaSheafSectionsEquiv_naturality_right)

universe u

namespace TauCeti

namespace Topology

variable {X : TopCat.{u}}

noncomputable section

instance isFlasque_of_injective
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective F] :
    TopCat.Presheaf.IsFlasque F.obj where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    refine ⟨freeYonedaSheafSectionsEquiv _ U.unop F
      (Injective.factorThru ((freeYonedaSheafSectionsEquiv _ V.unop F).symm s)
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map i.unop)), ?_⟩
    have h := freeYonedaSheafSectionsEquiv_naturality_left
      (Opens.grothendieckTopology X) i.unop F
      (Injective.factorThru ((freeYonedaSheafSectionsEquiv _ V.unop F).symm s)
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map i.unop))
    rw [Injective.comp_factorThru, AddEquiv.apply_symm_apply] at h
    exact h.symm

instance isFlasque_injectiveCokernelSequence_X₂
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₂.obj :=
  isFlasque_of_injective _

lemma subsingleton_H'_succ_of_isFlasque_aux (n : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      TopCat.Presheaf.IsFlasque F.obj → ∀ U : Opens X,
      Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) := by
  induction n with
  | zero =>
    intro F hF U
    rw [sheafH'_eq]
    apply subsingleton_ext_succ_of_injectiveCokernelSequence
    intro x₃
    let S := injectiveCokernelSequence F
    have hS₁ : TopCat.Presheaf.IsFlasque S.X₁.obj := by dsimp [S]; exact hF
    let _ : TopCat.Presheaf.IsFlasque S.X₁.obj := hS₁
    have hS := injectiveCokernelSequence_shortExact F
    have hepi : Epi (S.g.hom.app (op U)) :=
      TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
    rw [AddCommGrpCat.epi_iff_surjective] at hepi
    obtain ⟨t, ht⟩ := hepi
      (freeYonedaSheafSectionsEquiv _ U S.X₃ (Abelian.Ext.addEquiv₀ x₃))
    have hx₃ : x₃ =
        (Abelian.Ext.mk₀ ((freeYonedaSheafSectionsEquiv _ U S.X₂).symm t)).comp
        (Abelian.Ext.mk₀ S.g) (add_zero 0) := by
      rw [Abelian.Ext.mk₀_comp_mk₀]
      refine (Abelian.Ext.mk₀_addEquiv₀_apply x₃).symm.trans (congrArg Abelian.Ext.mk₀ ?_)
      refine (freeYonedaSheafSectionsEquiv _ U S.X₃).injective ?_
      rw [freeYonedaSheafSectionsEquiv_naturality_right, AddEquiv.apply_symm_apply, ht]
    rw [hx₃, Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
      Abelian.Ext.comp_zero]
  | succ n ih =>
    intro F hF U
    rw [sheafH'_eq]
    apply subsingleton_ext_succ_of_injectiveCokernelSequence
    intro x₃
    let S := injectiveCokernelSequence F
    have hS₁ : TopCat.Presheaf.IsFlasque S.X₁.obj := by dsimp [S]; exact hF
    let _ : TopCat.Presheaf.IsFlasque S.X₁.obj := hS₁
    have hS := injectiveCokernelSequence_shortExact F
    have hS₃ : TopCat.Presheaf.IsFlasque S.X₃.obj :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    have hH : Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} S.X₃ (n + 1) U) :=
      ih S.X₃ hS₃ U
    have hExt : Subsingleton
        (Abelian.Ext.{u}
          ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).obj U) S.X₃ (n + 1)) :=
      by simpa only [sheafH'_eq] using hH
    rw [@Subsingleton.elim _ hExt x₃ 0, Abelian.Ext.zero_comp]

instance subsingleton_H'_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) (U : Opens X) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) :=
  subsingleton_H'_succ_of_isFlasque_aux n F inferInstance U

instance subsingleton_H_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F (n + 1)) := by
  have := subsingleton_H'_succ_of_isFlasque F n (⊤ : Opens X)
  exact Function.Injective.subsingleton
    (f := ConcreteCategory.hom
      (F.cohomologyPresheafObjIsoH (n + 1) isTerminalTop).inv)
    ((ConcreteCategory.bijective_of_isIso _).injective)

instance isFlasque_skyscraperSheaf (p₀ : X) (A : AddCommGrpCat.{u})
    [(U : Opens X) → Decidable (p₀ ∈ U)] :
    TopCat.Presheaf.IsFlasque (skyscraperSheaf p₀ A).obj :=
  isFlasque_skyscraperSheaf_of_hasZeroObject p₀ A

end

end Topology

end TauCeti
