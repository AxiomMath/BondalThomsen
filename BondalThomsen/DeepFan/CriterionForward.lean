module

public import BondalThomsen.Fan.PrimitiveDivisorPairing
public import BondalThomsen.DeepFan.BadPrimitivePair
public import BondalThomsen.Collection.BondalThomsenClasses
public import BondalThomsen.Derived.SheafExtOrdering
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.Basic

@[expose] public section

open Finset Module CategoryTheory CategoryTheory.Abelian

namespace BondalThomsen

open TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

def ToricClassNefPrimitiveCriterion (fan : TauCeti.Toric.Fan embedding)
    (nef : fan.InvariantRayDivisorClass → Prop)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop) :
    Prop :=
  ∀ divisor_class, nef divisor_class ↔
    ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
      extremal left right relation → 0 ≤ relation.classPairing divisor_class

theorem inverse_bondalThomsen_nef_of_small_extremal
    (fan : TauCeti.Toric.Fan embedding) (nef : fan.InvariantRayDivisorClass → Prop)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (criterion : ToricClassNefPrimitiveCriterion fan nef extremal)
    (small_extremal : ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
      extremal left right relation → ∑ ray : right, relation.coefficients ray ≤ 1) :
    ∀ member : fan.BondalThomsenClass, nef (-member.val) := by
  intro member
  obtain ⟨pairing, same⟩ := member.property
  apply (criterion _).mpr
  intro left right relation is_extremal
  rw [← same]
  exact relation.classPairing_negative_floor_nonnegative
    (small_extremal left right relation is_extremal) pairing

end BondalThomsen

namespace BondalThomsen

open TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

section Cohomology

universe schemeUniverse

variable {Index : Type*}

theorem subsingleton_factor_of_positive_multiplicity
    {Groups : Index → Type*} [∀ index, Zero (Groups index)] (multiplicity : Index → ℕ)
    (positive : ∀ index, 0 < multiplicity index)
    (vanishing : Subsingleton (∀ index, Fin (multiplicity index) → Groups index))
    (chosen : Index) : Subsingleton (Groups chosen) := by
  classical
  let := vanishing
  refine ⟨fun first second => ?_⟩
  let first_family : ∀ index, Fin (multiplicity index) → Groups index :=
    Function.update (fun _ _ => 0) chosen (fun _ => first)
  let second_family : ∀ index, Fin (multiplicity index) → Groups index :=
    Function.update (fun _ _ => 0) chosen (fun _ => second)
  have same := Subsingleton.elim first_family second_family
  have evaluated := congrFun (congrFun same chosen) ⟨0, positive chosen⟩
  simpa [first_family, second_family] using evaluated

structure ToricFrobeniusExtDecomposition
    (fan : TauCeti.Toric.Fan embedding) (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (classes : Index → fan.BondalThomsenClass)
    (realization : fan.InvariantRayDivisorClass → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    where
  multiplication : ℕ
  multiplication_positive : 0 < multiplication
  multiplicity : Index → ℕ
  multiplicity_positive : ∀ index, 0 < multiplicity index
  cohomology_equiv : ∀ source degree,
    TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
        (realization (-((multiplication : ℤ) • (classes source).val))).obj degree ≃+
      (∀ target, Fin (multiplicity target) →
        Ext (realization (classes source).val).obj (realization (classes target).val).obj degree)

theorem positive_sheafExt_vanishing_of_frobenius
    (fan : TauCeti.Toric.Fan embedding) (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (classes : Index → fan.BondalThomsenClass)
    (realization : fan.InvariantRayDivisorClass → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (decomposition : ToricFrobeniusExtDecomposition fan scheme classes realization)
    (nef : fan.InvariantRayDivisorClass → Prop)
    (kodaira : ∀ source degree, 0 < degree → nef (-(classes source).val) →
      Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
        (realization (-((decomposition.multiplication : ℤ) • (classes source).val))).obj degree))
    (all_nef : ∀ member : fan.BondalThomsenClass, nef (-member.val)) :
    ∀ source target degree, 0 < degree →
      Subsingleton (Ext (realization (classes source).val).obj
        (realization (classes target).val).obj degree) := by
  intro source target degree degree_positive
  let := kodaira source degree degree_positive (all_nef (classes source))
  have product_vanishing : Subsingleton
      (∀ target, Fin (decomposition.multiplicity target) →
        Ext (realization (classes source).val).obj (realization (classes target).val).obj degree) := by
    refine ⟨fun first second => ?_⟩
    apply (decomposition.cohomology_equiv source degree).symm.injective
    exact Subsingleton.elim _ _
  exact subsingleton_factor_of_positive_multiplicity decomposition.multiplicity
    decomposition.multiplicity_positive product_vanishing target

end Cohomology

end BondalThomsen
