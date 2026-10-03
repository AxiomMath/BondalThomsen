module

public import BondalThomsen.Fan.OrderingObstruction
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

@[expose] public section

namespace BondalThomsen

open CategoryTheory
open CategoryTheory.Abelian

universe schemeUniverse

theorem exists_sheafExt_backward_ordering
    {Index : Type*} [Fintype Index] (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (objects : Index → scheme.Modules)
    (identity_nonzero : ∀ index, 𝟙 (objects index) ≠ 0)
    (composition_nonzero : ∀ {source middle target : Index}
      (first : objects source ⟶ objects middle) (second : objects middle ⟶ objects target),
      first ≠ 0 → second ≠ 0 → first ≫ second ≠ 0)
    (endomorphism_iso : ∀ index (endomorphism : objects index ⟶ objects index),
      endomorphism ≠ 0 → IsIso endomorphism)
    (pairwise_nonisomorphic : ∀ {first second : Index}, Nonempty (objects first ≅ objects second) →
      first = second)
    (positive_vanishing : ∀ source target degree, 0 < degree →
      Subsingleton (Ext (objects source) (objects target) degree)) :
    ∃ numbering : Index ≃ Fin (Fintype.card Index),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Ext (objects source) (objects target) degree), extension = 0 := by
  let := OrderingObstruction.nonzeroHom_isPartialOrder objects identity_nonzero
    composition_nonzero endomorphism_iso (fun _ _ => pairwise_nonisomorphic)
  obtain ⟨numbering, compatible⟩ :=
    OrderingObstruction.exists_monotone_numbering (OrderingObstruction.NonzeroHom objects)
  refine ⟨numbering, ?_⟩
  intro source target backward degree extension
  by_cases zero_degree : degree = 0
  · subst degree
    obtain ⟨morphism, rfl⟩ := (Ext.mk₀_bijective (objects source) (objects target)).2 extension
    apply (Ext.mk₀_eq_zero_iff morphism).mpr
    by_contra nonzero
    exact (not_le_of_gt backward) (compatible source target ⟨morphism, nonzero⟩)
  · let := positive_vanishing source target degree (Nat.pos_of_ne_zero zero_degree)
    exact Subsingleton.elim _ _

theorem sheafExt_two_cycle_obstructs_ordering
    {Index : Type*} [Fintype Index] (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (objects : Index → scheme.Modules) {source target : Index} (different : source ≠ target)
    (forward : objects source ⟶ objects target) (forward_nonzero : forward ≠ 0)
    (degree : ℕ) (reverse : Ext (objects target) (objects source) degree)
    (reverse_nonzero : reverse ≠ 0) :
    ¬ ∃ numbering : Index ≃ Fin (Fintype.card Index),
      ∀ first second, numbering second < numbering first →
        ∀ index (extension : Ext (objects first) (objects second) index), extension = 0 := by
  rintro ⟨numbering, vanishing⟩
  have number_different : numbering source ≠ numbering target :=
    fun same => different (numbering.injective same)
  rcases lt_or_gt_of_ne number_different with increasing | decreasing
  · exact reverse_nonzero (vanishing target source increasing degree reverse)
  · exact forward_nonzero ((Ext.mk₀_eq_zero_iff forward).mp
      (vanishing source target decreasing 0 (Ext.mk₀ forward)))

theorem exists_invertibleSheafExt_backward_ordering
    {Index : Type*} [Fintype Index] (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (identity_nonzero : ∀ index, 𝟙 (line_bundles index).obj ≠ 0)
    (composition_nonzero : ∀ {source middle target : Index}
      (first : (line_bundles source).obj ⟶ (line_bundles middle).obj)
      (second : (line_bundles middle).obj ⟶ (line_bundles target).obj),
      first ≠ 0 → second ≠ 0 → first ≫ second ≠ 0)
    (endomorphism_iso : ∀ index
      (endomorphism : (line_bundles index).obj ⟶ (line_bundles index).obj),
      endomorphism ≠ 0 → IsIso endomorphism)
    (pairwise_nonisomorphic : ∀ {first second : Index},
      Nonempty ((line_bundles first).obj ≅ (line_bundles second).obj) → first = second)
    (positive_vanishing : ∀ source target degree, 0 < degree →
      Subsingleton (Ext (line_bundles source).obj (line_bundles target).obj degree)) :
    ∃ numbering : Index ≃ Fin (Fintype.card Index),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Ext (line_bundles source).obj (line_bundles target).obj degree),
          extension = 0 :=
  exists_sheafExt_backward_ordering scheme (fun index => (line_bundles index).obj)
    identity_nonzero composition_nonzero endomorphism_iso pairwise_nonisomorphic positive_vanishing

end BondalThomsen
