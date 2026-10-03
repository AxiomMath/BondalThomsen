module

public import BondalThomsen.Derived.CoherentDerivedCategory
public import BondalThomsen.Collection.ActualDerivedStrongness
public import Mathlib.CategoryTheory.Triangulated.Generators

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.FaithfulCollection

noncomputable section

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    {embedding : Lattice →+ Ambient}

local instance instHasDerivedCategoryModules (scheme : Scheme) : HasDerivedCategory scheme.Modules :=
  HasDerivedCategory.standard scheme.Modules

abbrev derivedTheta (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (member : fan.BondalThomsenClass) :
    DerivedCategory (fan.algebraicRealization 𝕜 regular).Modules :=
  (DerivedCategory.singleFunctor (fan.algebraicRealization 𝕜 regular).Modules 0).obj
    (fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val).obj

def exceptionalOrdering (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  letI := fan.scalarSheafModulesLinear 𝕜 complete regular
  ∃ numbering : fan.BondalThomsenClass ≃ Fin (Fintype.card fan.BondalThomsenClass),
    OrderingObstruction.IsExceptionalOrdering
      (fun member => SectionThree.IsExceptionalDerivedObject 𝕜
        (derivedTheta 𝕜 fan complete regular member))
      (SectionThree.derivedNonvanishing (derivedTheta 𝕜 fan complete regular)) numbering

def strongVanishing (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  OrderingObstruction.IsStrongVanishing
    (SectionThree.derivedNonvanishing (derivedTheta 𝕜 fan complete regular))

def strongOrdering (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  letI := fan.scalarSheafModulesLinear 𝕜 complete regular
  ∃ numbering : fan.BondalThomsenClass ≃ Fin (Fintype.card fan.BondalThomsenClass),
    OrderingObstruction.IsStrongExceptionalOrdering
      (fun member => SectionThree.IsExceptionalDerivedObject 𝕜
        (derivedTheta 𝕜 fan complete regular member))
      (SectionThree.derivedNonvanishing (derivedTheta 𝕜 fan complete regular)) numbering

def thetaProperty (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    ObjectProperty (DerivedCategory (fan.algebraicRealization 𝕜 regular).Modules) :=
  fun complex => ∃ member : fan.BondalThomsenClass,
    complex = derivedTheta 𝕜 fan complete regular member

def fullGeneration (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  letI := fan.algebraicRealization_isNoetherian 𝕜 regular
  boundedCoherentProperty (fan.algebraicRealization 𝕜 regular) ≤
    (thetaProperty 𝕜 fan complete regular).triangEnvelope

def fullStrongOrdering (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  strongOrdering 𝕜 fan complete regular ∧ fullGeneration 𝕜 fan complete regular

theorem strongOrdering_iff (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    strongOrdering 𝕜 fan complete regular ↔
      exceptionalOrdering 𝕜 fan complete regular ∧ strongVanishing 𝕜 fan complete regular := by
  constructor
  · rintro ⟨numbering, exceptional, strong⟩
    exact ⟨⟨numbering, exceptional⟩, strong⟩
  · rintro ⟨⟨numbering, exceptional⟩, strong⟩
    exact ⟨numbering, exceptional, strong⟩

theorem fullStrongOrdering_exceptionalOrdering (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ordering : fullStrongOrdering 𝕜 fan complete regular) :
    exceptionalOrdering 𝕜 fan complete regular :=
  ((strongOrdering_iff 𝕜 fan complete regular).mp ordering.1).1

theorem fullStrongOrdering_iff_of_generation (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (generation : fullGeneration 𝕜 fan complete regular) :
    fullStrongOrdering 𝕜 fan complete regular ↔ strongOrdering 𝕜 fan complete regular := by
  exact and_iff_left generation

theorem exceptionalOrdering_sheafBackwardExt (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ordering : exceptionalOrdering 𝕜 fan complete regular) :
    ∃ numbering : fan.BondalThomsenClass ≃ Fin (Fintype.card fan.BondalThomsenClass),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Ext
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular source.val).obj
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular target.val).obj degree),
          extension = 0 := by
  let := fan.scalarSheafModulesLinear 𝕜 complete regular
  obtain ⟨numbering, ordered⟩ := ordering
  exact ⟨numbering, SectionThree.sheafExt_backward_of_derivedExceptionalOrdering 𝕜
    (fan.algebraicRealization 𝕜 regular)
    (fun member : fan.BondalThomsenClass =>
      fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val)
    (derivedTheta 𝕜 fan complete regular)
    (SheafDerivedDegreeZero.canonicalDerivedSheafExtComparison _) numbering ordered⟩

theorem fullStrongOrdering_sheafBackwardExt (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ordering : fullStrongOrdering 𝕜 fan complete regular) :
    ∃ numbering : fan.BondalThomsenClass ≃ Fin (Fintype.card fan.BondalThomsenClass),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Ext
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular source.val).obj
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular target.val).obj degree),
          extension = 0 :=
  exceptionalOrdering_sheafBackwardExt 𝕜 fan complete regular
    (fullStrongOrdering_exceptionalOrdering 𝕜 fan complete regular ordering)

end

end BondalThomsen.FaithfulCollection
