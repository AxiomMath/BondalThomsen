module

public import BondalThomsen.Derived.SheafDerivedDegreeZero
public import BondalThomsen.Toric.Divisor.LineBundleOrder

@[expose] public section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

universe derivedUniverse

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

@[instance_reducible] noncomputable def scalarSheafModulesLinear (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    Linear 𝕜 (fan.algebraicRealization 𝕜 regular).Modules :=
  BondalThomsen.SheafDerivedDegreeZero.sheafModulesLinear
    (fan.scalarGlobalFunctionsEquiv 𝕜 complete regular).toRingHom

theorem derivedSheafScalarCompatibility (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    [HasDerivedCategory.{derivedUniverse} (fan.algebraicRealization 𝕜 regular).Modules]
    {Index : Type*}
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf
      (fan.algebraicRealization 𝕜 regular)) :
    letI := fan.scalarSheafModulesLinear 𝕜 complete regular
    BondalThomsen.SectionThree.DerivedSheafScalarCompatibility 𝕜
      (fan.scalarGlobalFunctionsEquiv 𝕜 complete regular)
      (BondalThomsen.SheafDerivedDegreeZero.canonicalDerivedSheafExtComparison line_bundles) :=
  BondalThomsen.SheafDerivedDegreeZero.canonicalDerivedSheafScalarCompatibility
    (fan.scalarGlobalFunctionsEquiv 𝕜 complete regular) line_bundles

end TauCeti.Toric.Fan
