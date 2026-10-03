module

public import BondalThomsen.Toric.Scheme.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

@[expose] public section

open AlgebraicGeometry CategoryTheory

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem structureMap_locallyOfFiniteType (fan : Fan embedding)
    (regular : fan.IsRegular) : LocallyOfFiniteType (fan.structureMap 𝕜 regular) := by
  let cover := fan.toricChartOpenCover 𝕜 regular
  let : ∀ cone : cover.I₀, IsAffine (cover.X cone) := fun cone => by
    change IsAffine (fan.affineToricChart 𝕜 cone)
    infer_instance
  apply (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFiniteType) cover).mpr
  intro cone
  change RingHom.FiniteType (fan.affineToricChartι 𝕜 regular cone ≫ fan.structureMap 𝕜 regular).appTop.hom
  rw [fan.chartι_comp_structureMap 𝕜 regular cone]
  apply HasRingHomProperty.appTop (P := @LocallyOfFiniteType)
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  let := fan.affineCoordinateRing_finiteType 𝕜 cone.val (regular cone.property)
  exact RingHom.finiteType_algebraMap.mpr inferInstance

theorem structureMap_quasiCompact (fan : Fan embedding) (regular : fan.IsRegular) :
    QuasiCompact (fan.structureMap 𝕜 regular) := by
  let := fan.algebraicRealization_isNoetherian 𝕜 regular
  infer_instance

end TauCeti.Toric.Fan
