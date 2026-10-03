module

public import BondalThomsen.Toric.RankOne.CurveDegreeNormalization
public import BondalThomsen.LineBundle.PicardGeometricNef
public import BondalThomsen.Toric.RankOne.PicardCohomology
public import BondalThomsen.Toric.Positivity.StrictSupportAmple
public import BondalThomsen.Toric.Scheme.BasisChart
public import BondalThomsen.Toric.RankOne.CohomologicalDimension

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable {𝕜} in
noncomputable local instance rankOneNefBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

theorem rankOneInvertibleSheaf_isNef_iff_degree_nonnegative
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    AlgebraicGeometry.IsNef (baseField := 𝕜) bundle.obj ↔
      0 ≤ fan.rankOneInvertibleSheafDegree 𝕜 complete regular basis bundle := by
  let : Nonempty fan.cones := fan.completeFan_nonemptyCones complete
  constructor
  · intro nef
    let curve := fan.rankOneIntegralCurve 𝕜 complete regular basis
    let comparison : (Scheme.Modules.pullback curve.ι).obj bundle.obj ≅ bundle.obj :=
      (Scheme.Modules.pullbackId (fan.algebraicRealization 𝕜 regular)).app bundle.obj
    have nonnegative := nef curve
    rw [curve.lineBundleDegree_eq_of_iso comparison] at nonnegative
    change 0 ≤ fan.rankOneGeometricLineBundleDegree 𝕜 complete regular basis bundle at nonnegative
    rwa [fan.rankOneGeometricLineBundleDegree_eq_picardDegree 𝕜 complete regular basis] at nonnegative
  · intro nonnegative
    exact BondalThomsen.invertibleSheaf_isNef_of_semiample bundle
      ((fan.rankOneInvertibleSheafSemiample_iff_degree_nonnegative 𝕜
        complete regular basis bundle).mpr nonnegative)

theorem rankOneInvertibleSheaf_isNef_iff_semiample
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    AlgebraicGeometry.IsNef (baseField := 𝕜) bundle.obj ↔ BondalThomsen.InvertibleSheafSemiample bundle :=
  (fan.rankOneInvertibleSheaf_isNef_iff_degree_nonnegative 𝕜 complete regular basis bundle).trans
    (fan.rankOneInvertibleSheafSemiample_iff_degree_nonnegative 𝕜 complete regular basis bundle).symm

theorem rankOneInvariantDivisor_isNef_iff_support
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (basis : Basis (Fin 1) ℤ Lattice) (divisor : fan.InvariantRayDivisor) :
    AlgebraicGeometry.IsNef (baseField := 𝕜)
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj ↔
      fan.HasRaySupportInequalities divisor :=
  (fan.rankOneInvertibleSheaf_isNef_iff_semiample 𝕜 complete regular basis _).trans
    (fan.invariantDivisorLineBundleSemiample_iff_support 𝕜 complete regular divisor)

end TauCeti.Toric.Fan
