module

public import BondalThomsen.Fan.CompleteFanGlobalFunctions
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Regular
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open AlgebraicGeometry CategoryTheory Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem affineCoordinateRing_finiteType (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (regular : IsRegularCone embedding cone) :
    Algebra.FiniteType 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone) := by
  let := regular.fg_dualSemigroup fan.lattice
  infer_instance

theorem affineCoordinateRing_isNoetherianRing (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (regular : IsRegularCone embedding cone) :
    IsNoetherianRing (affineCoordinateRing 𝕜 fan.lattice cone) := by
  let := fan.affineCoordinateRing_finiteType 𝕜 cone regular
  exact Algebra.FiniteType.isNoetherianRing 𝕜 _

theorem algebraicRealization_isNoetherian (fan : Fan embedding) (regular : fan.IsRegular) :
    IsNoetherian (fan.algebraicRealization 𝕜 regular) := by
  let cover := fan.toricChartOpenCover 𝕜 regular
  let : Finite cover.I₀ := fan.finite_cones.to_subtype
  let : ∀ cone : cover.I₀, IsAffine (cover.X cone) := fun cone => by
    change IsAffine (fan.affineToricChart 𝕜 cone)
    infer_instance
  apply (isNoetherian_iff_of_finite_affine_openCover (𝒰 := cover)).mpr
  intro cone
  change IsNoetherianRing Γ(fan.affineToricChart 𝕜 cone, ⊤)
  let := fan.affineCoordinateRing_isNoetherianRing 𝕜 cone.val (regular cone.property)
  exact isNoetherianRing_of_ringEquiv _
    (Scheme.ΓSpecIso (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice cone.val))).symm.commRingCatIsoToRingEquiv

end TauCeti.Toric.Fan
