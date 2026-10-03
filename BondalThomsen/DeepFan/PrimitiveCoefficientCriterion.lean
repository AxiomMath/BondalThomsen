module

public import BondalThomsen.Fan.PrimitiveRelationDegree
public import BondalThomsen.DeepFan.CriterionConverse
public import BondalThomsen.DeepFan.CriterionForward
public import BondalThomsen.Fan.PrimitiveNonfaces
public import BondalThomsen.Fan.PrimitiveRelationBasis
public import BondalThomsen.Collection.SectionThree.Equivalences

@[expose] public section

open Finset Set Module Classical

namespace BondalThomsen

open TauCeti.Toric.Fan

section Algebraic

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

def HasSmallExtremalPrimitiveCoefficients (fan : TauCeti.Toric.Fan embedding)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop) :
    Prop :=
  ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
    extremal left right relation → ∑ ray : right, relation.coefficients ray ≤ 1

def ExtremalDropOneConeIncidence (fan : TauCeti.Toric.Fan embedding)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop) :
    Prop :=
  ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
    extremal left right relation → ∀ distinguished : left,
      relation.DropOneConeIncidence distinguished

end Algebraic

section GeometricInputs

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] {embedding : Lattice →+ Ambient}

structure PrimitiveCoefficientCriterionInputs (fan : TauCeti.Toric.Fan embedding)
    (dimension : ℕ) (nef : fan.InvariantRayDivisor → Prop)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop) :
    Prop where
  cone_incidence : ExtremalDropOneConeIncidence fan extremal
  nef_support : ToricNefSupportCriterion fan dimension nef
  mori_negative : ExtremalPrimitiveNegativeWitness fan nef extremal

theorem deep_of_small_extremal_primitive_coefficients
    (fan : TauCeti.Toric.Fan embedding) (regular : fan.IsRegular) (dimension : ℕ)
    (nef : fan.InvariantRayDivisor → Prop)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (support : ToricNefSupportCriterion fan dimension nef)
    (negative : ExtremalPrimitiveNegativeWitness fan nef extremal)
    (small : HasSmallExtremalPrimitiveCoefficients fan extremal) : fan.IsDeep dimension :=
  proposition_4_1_ii_implies_i fan regular dimension nef extremal support negative small

theorem extremalPrimitiveNegativeWitness_of_classNefCriterion
    (fan : TauCeti.Toric.Fan embedding) (nef : fan.InvariantRayDivisorClass → Prop)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (criterion : ToricClassNefPrimitiveCriterion fan nef extremal) :
    ExtremalPrimitiveNegativeWitness fan (fun divisor => nef (fan.invariantRayDivisorClass divisor))
      extremal := by
  intro divisor not_nef
  by_contra absent
  apply not_nef
  apply (criterion _).mpr
  intro left right relation is_extremal
  change 0 ≤ relation.divisorIntersection divisor
  by_contra negative
  exact absent ⟨left, right, relation, is_extremal, by omega⟩

end GeometricInputs

end BondalThomsen
