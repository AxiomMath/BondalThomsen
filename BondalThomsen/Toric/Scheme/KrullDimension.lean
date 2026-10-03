module

public import BondalThomsen.Toric.Scheme.Dimension
public import BondalThomsen.Toric.Divisor.DivisorLineBundle
public import BondalThomsen.Ports.MiyaokaMori.Nef.ProperCurveProjectiveLineModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module TopologicalSpace

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem algebraicRealization_topologicalKrullDim_eq_ambient_finrank
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    topologicalKrullDim (fan.algebraicRealization 𝕜 regular) = finrank ℝ Ambient := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let := fan.structureMap_locallyOfFiniteType 𝕜 regular
  obtain ⟨dimension, basis, coneBasis, _⟩ :=
    fan.exists_coneBasis_containing complete regular (0 : Ambient)
  let cone : fan.cones := ⟨_, coneBasis⟩
  let chartStructure := Spec.map (CommRingCat.ofHom
    (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val)))
  let : SmoothOfRelativeDimension dimension chartStructure :=
    fan.basisConeChart_smoothOfRelativeDimension 𝕜 basis
  let : Smooth chartStructure := SmoothOfRelativeDimension.smooth dimension _
  let inclusion := fan.affineToricChartι 𝕜 regular cone
  let := fan.affineToricChart_isIntegral 𝕜 cone
  have genericEquality : inclusion (genericPoint (fan.affineToricChart 𝕜 cone)) =
      genericPoint (fan.algebraicRealization 𝕜 regular) :=
    genericPoint_eq_of_isOpenImmersion inclusion
  have genericBijective : Function.Bijective
      (functionFieldAlgebra inclusion genericEquality).algebraMap :=
    ConcreteCategory.bijective_of_isIso
      (((fan.algebraicRealization 𝕜 regular).presheaf.stalkCongr
        (Inseparable.of_eq genericEquality.symm)).hom ≫
          inclusion.stalkMap (genericPoint _))
  have dimensionEquality := ProperCurveProjectiveLine.dimension_eq_of_generic_bijective
    chartStructure (fan.structureMap 𝕜 regular) inclusion
    (fan.chartι_comp_structureMap 𝕜 regular cone) genericEquality genericBijective
  rw [← dimensionEquality]
  change topologicalKrullDim (PrimeSpectrum (affineCoordinateRing 𝕜 fan.lattice cone.val)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    fan.basisConeCoordinateRing_krullDim 𝕜 basis, fan.ambient_finrank_eq_basis_card basis]

theorem algebraicRealization_topologicalKrullDim_eq_lattice_finrank
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    topologicalKrullDim (fan.algebraicRealization 𝕜 regular) = finrank ℤ Lattice := by
  rw [fan.algebraicRealization_topologicalKrullDim_eq_ambient_finrank 𝕜 complete regular,
    fan.lattice.finrank_eq]

end TauCeti.Toric.Fan
