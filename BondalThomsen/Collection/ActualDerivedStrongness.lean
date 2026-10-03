module

public import BondalThomsen.Collection.SectionThree.SheafUnconditionalPrimitive

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Module

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

universe derivedUniverse

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    {embedding : Lattice →+ Ambient}

theorem actualDerived_exceptional_iff_strong_of_kodaira_nef_inputs
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    [HasDerivedCategory.{derivedUniverse} (fan.algebraicRealization 𝕜 regular).Modules]
    (dimension : ℕ)
    (geometric_nef : TauCeti.AlgebraicGeometry.LineBundleClass
      (fan.algebraicRealization 𝕜 regular) → Prop)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (nef_criterion : BondalThomsen.ToricClassNefPrimitiveCriterion fan
      (fun divisor_class => geometric_nef
        (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisor_class))) extremal)
    (fano_support : BondalThomsen.ToricFanoExtremalSupport fan dimension extremal)
    (kodaira : ∀ multiplication : ℕ, 0 < multiplication →
      ∀ (source : fan.BondalThomsenClass) degree, 0 < degree →
        geometric_nef (Additive.toMul
          (fan.invariantDivisorPicardRealization 𝕜 complete regular (-source.val))) →
        Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
          (fan.invariantClassInvertibleSheaf 𝕜 complete regular
            (-((multiplication : ℤ) • source.val))).obj degree)) :
    letI := fan.scalarSheafModulesLinear 𝕜 complete regular
    let objects := fun member : fan.BondalThomsenClass =>
      (DerivedCategory.singleFunctor (fan.algebraicRealization 𝕜 regular).Modules 0).obj
        (fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val).obj
    let exceptional : Prop := ∃ numbering : fan.BondalThomsenClass ≃
        Fin (Fintype.card fan.BondalThomsenClass),
      BondalThomsen.OrderingObstruction.IsExceptionalOrdering
        (fun member => BondalThomsen.SectionThree.IsExceptionalDerivedObject 𝕜 (objects member))
        (BondalThomsen.SectionThree.derivedNonvanishing objects) numbering
    let positive_ext : Prop := BondalThomsen.SectionThree.PositiveSheafExtVanishing
      (fan.algebraicRealization 𝕜 regular)
      (fun member : fan.BondalThomsenClass =>
        fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val)
    let strong : Prop := ∃ numbering : fan.BondalThomsenClass ≃
        Fin (Fintype.card fan.BondalThomsenClass),
      BondalThomsen.OrderingObstruction.IsStrongExceptionalOrdering
        (fun member => BondalThomsen.SectionThree.IsExceptionalDerivedObject 𝕜 (objects member))
        (BondalThomsen.SectionThree.derivedNonvanishing objects) numbering
    (exceptional ↔ positive_ext) ∧ (positive_ext ↔ strong) := by
  let := fan.scalarSheafModulesLinear 𝕜 complete regular
  exact BondalThomsen.SectionThree.exceptional_iff_strong_of_kodaira_nef_and_derived_inputs 𝕜
    fan complete regular
    (fun member : fan.BondalThomsenClass =>
      (DerivedCategory.singleFunctor (fan.algebraicRealization 𝕜 regular).Modules 0).obj
        (fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val).obj)
    (BondalThomsen.SheafDerivedDegreeZero.canonicalDerivedSheafExtComparison _)
    (fan.derivedSheafScalarCompatibility 𝕜 complete regular _)
    dimension geometric_nef extremal nef_criterion fano_support kodaira

end TauCeti.Toric.Fan
