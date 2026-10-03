module

public import BondalThomsen.Toric.Scheme.BasisChart
public import BondalThomsen.Fan.Facets
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

@[expose] public section

open AlgebraicGeometry CategoryTheory Module

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem basisConeCoordinateRing_standardSmooth_dimension (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) :
    Algebra.IsStandardSmoothOfRelativeDimension dimension 𝕜
      (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) := by
  let : Algebra.IsStandardSmoothOfRelativeDimension dimension 𝕜
      (MvPolynomial (Fin dimension) 𝕜) := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial 𝕜 (Fin dimension)
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv dimension
    (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm

theorem basisConeCoordinateRing_krullDim (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) :
    ringKrullDim (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) = dimension := by
  rw [(fan.basisConeCoordinateRingEquiv 𝕜 basis).toRingEquiv.ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]
  simp

theorem basisConeChart_smoothOfRelativeDimension (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) :
    SmoothOfRelativeDimension dimension (Spec.map (CommRingCat.ofHom
      (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))))) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension dimension)).mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact RingHom.isStandardSmoothOfRelativeDimension_algebraMap dimension |>.mpr
    (fan.basisConeCoordinateRing_standardSmooth_dimension 𝕜 basis)

variable [FiniteDimensional ℝ Ambient]

theorem affineToricChart_smoothOfRelativeDimension (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (cone : fan.cones) :
    SmoothOfRelativeDimension (finrank ℝ Ambient) (Spec.map (CommRingCat.ofHom
      (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val)))) := by
  obtain ⟨dimension, basis, cone_basis, face⟩ :=
    fan.exists_coneBasis_above complete regular cone.val cone.property
  rw [fan.ambient_finrank_eq_basis_card basis]
  let face_map := faceAffineToricSchemeMap 𝕜 fan.lattice face
  let basis_map := Spec.map (CommRingCat.ofHom
    (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))))
  let : IsOpenImmersion face_map :=
    (regular cone_basis).isOpenImmersion_faceAffineToricSchemeMap 𝕜 _ _
  let : SmoothOfRelativeDimension dimension basis_map :=
    fan.basisConeChart_smoothOfRelativeDimension 𝕜 basis
  have composition : face_map ≫ basis_map =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val))) := by
    unfold face_map basis_map
    rw [faceAffineToricSchemeMap_def, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro coefficient
    exact (faceAffineCoordinateRingMap 𝕜 fan.lattice face).commutes coefficient
  rw [← composition]
  exact (by simpa using
    (inferInstance : SmoothOfRelativeDimension (0 + dimension) (face_map ≫ basis_map)))

theorem structureMap_smoothOfRelativeDimension (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    SmoothOfRelativeDimension (finrank ℝ Ambient) (fan.structureMap 𝕜 regular) := by
  let cover := fan.toricChartOpenCover 𝕜 regular
  let : ∀ cone : cover.I₀, IsAffine (cover.X cone) := fun cone => by
    change IsAffine (fan.affineToricChart 𝕜 cone)
    infer_instance
  apply (HasRingHomProperty.iff_of_source_openCover
    (P := @SmoothOfRelativeDimension (finrank ℝ Ambient)) cover).mpr
  intro cone
  change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (finrank ℝ Ambient))
    (fan.affineToricChartι 𝕜 regular cone ≫ fan.structureMap 𝕜 regular).appTop.hom
  rw [fan.chartι_comp_structureMap 𝕜 regular cone]
  exact HasRingHomProperty.appTop (P := @SmoothOfRelativeDimension (finrank ℝ Ambient)) _
    (fan.affineToricChart_smoothOfRelativeDimension 𝕜 complete regular cone)

end TauCeti.Toric.Fan
