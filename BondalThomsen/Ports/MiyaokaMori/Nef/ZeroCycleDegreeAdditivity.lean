module

public import BondalThomsen.Ports.MiyaokaMori.NefLineBundle

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

universe u v

noncomputable section

namespace AlgebraicGeometry.Intersection

namespace DimensionCycle

abbrev zero (scheme : Scheme.{u}) (dimension : ℕ) : DimensionCycle scheme dimension := 0

abbrev add {scheme : Scheme.{u}} {dimension : ℕ}
    (first second : DimensionCycle scheme dimension) : DimensionCycle scheme dimension := first + second

abbrev neg {scheme : Scheme.{u}} {dimension : ℕ}
    (cycle : DimensionCycle scheme dimension) : DimensionCycle scheme dimension := -cycle

abbrev zsmul {scheme : Scheme.{u}} {dimension : ℕ} (multiplicity : ℤ)
    (cycle : DimensionCycle scheme dimension) : DimensionCycle scheme dimension := multiplicity • cycle

abbrev finsetSum {scheme : Scheme.{u}} {dimension : ℕ} {index : Type v}
    (indices : Finset index) (cycles : index → DimensionCycle scheme dimension) :
    DimensionCycle scheme dimension := ∑ entry ∈ indices, cycles entry

def weightedSum {scheme : Scheme.{u}} {dimension : ℕ} {index : Type v}
    (indices : Finset index) (multiplicities : index → ℤ)
    (cycles : index → DimensionCycle scheme dimension) : DimensionCycle scheme dimension :=
  finsetSum indices fun entry => zsmul (multiplicities entry) (cycles entry)

end DimensionCycle

def rawZeroCycleDegreeAddHom {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap] :
    DimensionCycle scheme 0 →+ ℤ := by
  letI : scheme.Over (Spec (CommRingCat.of baseField)) := ⟨structureMap⟩
  letI : IsProper (scheme ↘ Spec (CommRingCat.of baseField)) :=
    (inferInstance : IsProper structureMap)
  exact (AlgebraicCycle.degreeAddHom (baseField := baseField)).comp
    (AlgebraicGeometry.cycleSubgroup scheme 0).subtype

@[simp] theorem rawZeroCycleDegreeAddHom_apply {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} (structureMap : scheme ⟶ Spec (CommRingCat.of baseField))
    [IsProper structureMap] (cycle : DimensionCycle scheme 0) :
    rawZeroCycleDegreeAddHom structureMap cycle = rawZeroCycleDegree structureMap cycle := rfl

@[simp] theorem rawZeroCycleDegree_zero {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} (structureMap : scheme ⟶ Spec (CommRingCat.of baseField))
    [IsProper structureMap] : rawZeroCycleDegree structureMap (DimensionCycle.zero scheme 0) = 0 :=
  (rawZeroCycleDegreeAddHom structureMap).map_zero

theorem rawZeroCycleDegree_add {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (first second : DimensionCycle scheme 0) :
    rawZeroCycleDegree structureMap (DimensionCycle.add first second) =
      rawZeroCycleDegree structureMap first + rawZeroCycleDegree structureMap second :=
  (rawZeroCycleDegreeAddHom structureMap).map_add first second

end AlgebraicGeometry.Intersection
