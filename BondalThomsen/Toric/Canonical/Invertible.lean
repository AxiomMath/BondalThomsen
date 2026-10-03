module

public import BondalThomsen.Toric.Canonical.FanChartRestriction
public import BondalThomsen.Toric.Divisor.DivisorLineBundle
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Class

@[expose] public section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CanonicalInvertible

noncomputable def openImmersionUnitRestrictionIso {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    (modules : Target.Modules)
    (coordinates : modules.restrict inclusion ≅ SheafOfModules.unit Source.ringCatSheaf) :
    SheafOfModules.unit (inclusion.opensRange : Scheme).ringCatSheaf ≅
      modules.restrict inclusion.opensRange.ι :=
  (Scheme.Modules.restrictUnitIso inclusion.isoOpensRange.inv).symm ≪≫
    (Scheme.Modules.restrictFunctor inclusion.isoOpensRange.inv).mapIso coordinates.symm ≪≫
    (Scheme.Modules.restrictFunctorComp inclusion.isoOpensRange.inv inclusion).symm.app modules ≪≫
    (Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_inv_comp).app modules

end BondalThomsen.CanonicalInvertible

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

noncomputable def basisConeCanonicalUnitIso (fan : Fan embedding)
    (regular : fan.IsRegular) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_mem : PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index))) ∈ fan.cones) :
    let cone : fan.cones :=
      ⟨PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))), cone_mem⟩
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).restrict
        (fan.affineToricChartι 𝕜 regular cone) ≅
      SheafOfModules.unit (affineToricScheme 𝕜 fan.lattice cone.val).ringCatSheaf := by
  let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice
    (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
  let differentialBasis := fan.basisConeDifferentialBasis 𝕜 basis
  let coordinates := BondalThomsen.TopExterior.trivialization differentialBasis
  exact fan.basisConeCanonicalRestrictionTildeIso 𝕜 regular basis cone_mem ≪≫
    (tilde.functor CoordinateRing).mapIso coordinates.toModuleIso ≪≫ tildeSelf

theorem toricCanonicalExteriorSheaf_isInvertible [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (fan.algebraicRealization 𝕜 regular)
      (fan.toricCanonicalExteriorSheaf 𝕜 regular (Module.finrank ℤ Lattice)) := by
  apply TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
  let indices := (Finite.equivFin fan.cones).symm
  let atlas := fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0
  refine ⟨Fin (Nat.card fan.cones),
    (fun index => (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange),
    atlas.covers, ?_⟩
  intro index
  let cone := indices index
  let basisData := fan.divisorChartBasis complete regular cone
  have dimension_eq : basisData.val.1 = Module.finrank ℤ Lattice := by
    simpa using (Module.finrank_eq_card_basis basisData.val.2).symm
  have coordinates :
      (fan.toricCanonicalExteriorSheaf 𝕜 regular (Module.finrank ℤ Lattice)).restrict
          (fan.affineToricChartι 𝕜 regular (fan.divisorChartCone complete regular cone)) ≅
        SheafOfModules.unit
          (affineToricScheme 𝕜 fan.lattice (fan.divisorChartCone complete regular cone).val).ringCatSheaf := by
    rw [← dimension_eq]
    exact fan.basisConeCanonicalUnitIso 𝕜 regular basisData.val.2 basisData.property.1
  exact ⟨BondalThomsen.CanonicalInvertible.openImmersionUnitRestrictionIso
    (fan.affineToricChartι 𝕜 regular (fan.divisorChartCone complete regular cone))
    (fan.toricCanonicalExteriorSheaf 𝕜 regular (Module.finrank ℤ Lattice)) coordinates⟩

noncomputable def toricCanonicalInvertibleSheaf [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    TauCeti.AlgebraicGeometry.InvertibleSheaf (fan.algebraicRealization 𝕜 regular) :=
  ⟨fan.toricCanonicalExteriorSheaf 𝕜 regular (Module.finrank ℤ Lattice),
    fan.toricCanonicalExteriorSheaf_isInvertible 𝕜 complete regular⟩

noncomputable def toricCanonicalLineBundleClass [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    TauCeti.AlgebraicGeometry.LineBundleClass (fan.algebraicRealization 𝕜 regular) :=
  TauCeti.AlgebraicGeometry.LineBundleClass.mk
    (fan.toricCanonicalInvertibleSheaf 𝕜 complete regular)

end TauCeti.Toric.Fan
