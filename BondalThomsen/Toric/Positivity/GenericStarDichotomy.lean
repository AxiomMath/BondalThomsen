module

public import BondalThomsen.Toric.Scheme.ValuativeStarInduction
public import BondalThomsen.DeepFan.StarDeep

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem fieldMorphism_factors_affineToricChart (fan : Fan embedding)
    (regular : fan.IsRegular) {TargetField : Type} [Field TargetField]
    (generic : Spec (CommRingCat.of TargetField) ⟶ fan.algebraicRealization 𝕜 regular) :
    ∃ cone : fan.cones, ∃ chart_generic : Spec (CommRingCat.of TargetField) ⟶ fan.affineToricChart 𝕜 cone,
      chart_generic ≫ fan.affineToricChartι 𝕜 regular cone = generic := by
  obtain ⟨cone, chart_point, point_eq⟩ := fan.exists_affineToricChartι_apply_eq 𝕜 regular
    (generic (IsLocalRing.closedPoint TargetField))
  have in_range : Set.range generic ⊆ Set.range (fan.affineToricChartι 𝕜 regular cone) := by
    rintro point ⟨field_point, rfl⟩
    have same : field_point = IsLocalRing.closedPoint TargetField := Subsingleton.elim _ _
    rw [same]
    exact ⟨chart_point, point_eq⟩
  exact ⟨cone, IsOpenImmersion.lift (fan.affineToricChartι 𝕜 regular cone) generic in_range,
    IsOpenImmersion.lift_fac _ _ _⟩

theorem fieldMorphism_factors_basisChart [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {TargetField : Type} [Field TargetField]
    (generic : Spec (CommRingCat.of TargetField) ⟶ fan.algebraicRealization 𝕜 regular) :
    ∃ dimension : ℕ, ∃ basis : Basis (Fin dimension) ℤ Lattice,
      ∃ cone_basis : fan.IsConeBasis basis,
        ∃ chart_generic : Spec (CommRingCat.of TargetField) ⟶ fan.affineToricChart 𝕜 ⟨_, cone_basis⟩,
          chart_generic ≫ fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩ = generic := by
  obtain ⟨cone, chart_generic, factorization⟩ := fan.fieldMorphism_factors_affineToricChart 𝕜 regular generic
  obtain ⟨dimension, basis, cone_basis, face⟩ :=
    fan.exists_coneBasis_above complete regular cone.val cone.property
  refine ⟨dimension, basis, cone_basis, chart_generic ≫ faceAffineToricSchemeMap 𝕜 fan.lattice face, ?_⟩
  rw [Category.assoc]
  exact (congrArg (fun morphism => chart_generic ≫ morphism)
    (fan.faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 regular
      (τ := cone) (σ := ⟨_, cone_basis⟩) face)).trans factorization

noncomputable def coneBasisRay (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (index : Fin dimension) : fan.Ray := by
  have independent : LinearIndependent ℝ (fun index => embedding (basis index)) := by
    convert (fan.lattice.isBaseChange.basis basis).linearIndependent using 1
    funext coordinate
    exact (fan.lattice.isBaseChange.basis_apply basis coordinate).symm
  have face := PointedCone.isFaceOf_hull_image independent rfl {index}
  simp only [Set.image_singleton] at face
  exact ⟨basis index, basis.isPrimitive index, fan.mem_of_isFaceOf cone_basis face⟩

theorem basisGeneric_monomial_ne_zero (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) {TargetField : Type}
    [Field TargetField] [Algebra 𝕜 TargetField]
    (generic : MvPolynomial (Fin dimension) 𝕜 →ₐ[𝕜] TargetField)
    (coordinates_nonzero : ∀ index, generic (MvPolynomial.X index) ≠ 0)
    (character : dualSemigroup fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :
    generic (fan.basisConeCoordinateRingEquiv 𝕜 basis (MonoidAlgebra.single (ofAdd character) 1)) ≠ 0 := by
  have eval_eq : generic = MvPolynomial.aeval (fun index => generic (MvPolynomial.X index)) := by
    apply MvPolynomial.algHom_ext
    intro index
    simp
  rw [fan.basisConeCoordinateRingEquiv_single 𝕜, eval_eq, MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr (fun index _ => pow_ne_zero _ (coordinates_nonzero index))

theorem basisGeneric_torusChart_factorization (fan : Fan embedding) (regular : fan.IsRegular)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    {TargetField : Type} [Field TargetField] [Algebra 𝕜 TargetField]
    (generic : MvPolynomial (Fin dimension) 𝕜 →ₐ[𝕜] TargetField)
    (coordinates_nonzero : ∀ index, generic (MvPolynomial.X index) ≠ 0) :
    ∃ torus_generic : Spec (CommRingCat.of TargetField) ⟶ fan.denseTorus 𝕜,
      torus_generic ≫ faceAffineToricSchemeMap 𝕜 fan.lattice
        ((fan.isToricCone cone_basis).salient.bot_isFaceOf) =
          Spec.map (CommRingCat.ofHom
            (generic.comp (fan.basisConeCoordinateRingEquiv 𝕜 basis).toAlgHom).toRingHom) := by
  let face := (fan.isToricCone cone_basis).salient.bot_isFaceOf
  obtain ⟨character, localization⟩ :=
    (regular cone_basis).exists_isLocalization_away_faceAffineCoordinateRingMap 𝕜 fan.lattice face
  let := (faceAffineCoordinateRingMap 𝕜 fan.lattice face).toRingHom.toAlgebra
  let := localization
  let ring_generic := (generic.comp (fan.basisConeCoordinateRingEquiv 𝕜 basis).toAlgHom).toRingHom
  have unit : IsUnit (ring_generic (MonoidAlgebra.single (ofAdd character) 1)) :=
    isUnit_iff_ne_zero.mpr (fan.basisGeneric_monomial_ne_zero 𝕜 basis generic coordinates_nonzero character)
  let torus_ring := IsLocalization.Away.lift
    (S := affineCoordinateRing 𝕜 fan.lattice (⊥ : PointedCone ℝ Ambient))
    (MonoidAlgebra.single (ofAdd character) (1 : 𝕜)) unit
  refine ⟨Spec.map (CommRingCat.ofHom torus_ring), ?_⟩
  rw [faceAffineToricSchemeMap_def, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact IsLocalization.Away.lift_comp _ unit

theorem rayFaceAffineSchemeMap_cone_transport (fan : Fan embedding) (regular : fan.IsRegular)
    (ray : fan.Ray) {first second : fan.cones} (equality : first = second)
    (first_contains : embedding ray.val ∈ first.val)
    (second_contains : embedding ray.val ∈ second.val)
    (projected_eq : PointedCone.map (fan.starProjection ray) first.val =
      PointedCone.map (fan.starProjection ray) second.val) :
    (eqToHom (congrArg (affineToricScheme 𝕜 (fan.star ray).lattice) projected_eq.symm) ≫
      fan.rayFaceAffineSchemeMap 𝕜 ray first.val first_contains) ≫
        fan.affineToricChartι 𝕜 regular first =
      fan.rayFaceAffineSchemeMap 𝕜 ray second.val second_contains ≫ fan.affineToricChartι 𝕜 regular second := by
  subst second
  simp

theorem rayFaceAffineSchemeMap_comp_chartι (fan : Fan embedding) (regular : fan.IsRegular)
    (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular)
    (cone : fan.cones) (contains : embedding ray.val ∈ cone.val) :
    fan.rayFaceAffineSchemeMap 𝕜 ray cone.val contains ≫ fan.affineToricChartι 𝕜 regular cone =
      (fan.star ray).affineToricChartι 𝕜 star_regular
        ⟨PointedCone.map (fan.starProjection ray) cone.val, ⟨cone.val, ⟨cone.property, contains⟩, rfl⟩⟩ ≫
          fan.starOrbitClosureMap 𝕜 regular ray star_regular := by
  let projected : (fan.star ray).cones :=
    ⟨PointedCone.map (fan.starProjection ray) cone.val, ⟨cone.val, ⟨cone.property, contains⟩, rfl⟩⟩
  have lift_eq := fan.starConeLift_eq_of_projected ray projected cone contains rfl
  have formula := fan.affineToricChartι_comp_starOrbitClosureMap 𝕜 regular ray star_regular projected
  dsimp only [rayFaceChartMap] at formula
  exact (fan.rayFaceAffineSchemeMap_cone_transport 𝕜 regular ray lift_eq
    (fan.starConeLift_contains ray projected) contains
    (fan.starConeLift_projected ray projected)).symm.trans formula.symm

theorem basisGeneric_starGlobal_factorization (fan : Fan embedding) (regular : fan.IsRegular)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (removed : Fin dimension) (star_regular : (fan.star (fan.coneBasisRay basis cone_basis removed)).IsRegular)
    {TargetField : Type} [Field TargetField] [Algebra 𝕜 TargetField]
    (generic : MvPolynomial (Fin dimension) 𝕜 →ₐ[𝕜] TargetField)
    (coordinate_zero : generic (MvPolynomial.X removed) = 0) :
    ∃ star_generic : Spec (CommRingCat.of TargetField) ⟶
        (fan.star (fan.coneBasisRay basis cone_basis removed)).algebraicRealization 𝕜 star_regular,
      star_generic ≫ fan.starOrbitClosureMap 𝕜 regular (fan.coneBasisRay basis cone_basis removed) star_regular =
        Spec.map (CommRingCat.ofHom
          (generic.comp (fan.basisConeCoordinateRingEquiv 𝕜 basis).toAlgHom).toRingHom) ≫
            fan.affineToricChartι 𝕜 regular ⟨_, cone_basis⟩ := by
  let ray := fan.coneBasisRay basis cone_basis removed
  let cone : fan.cones := ⟨_, cone_basis⟩
  have contains : embedding ray.val ∈ cone.val :=
    PointedCone.subset_hull ⟨removed, rfl⟩
  let projected : (fan.star ray).cones :=
    ⟨PointedCone.map (fan.starProjection ray) cone.val, ⟨cone.val, ⟨cone.property, contains⟩, rfl⟩⟩
  let star_point := Spec.map (CommRingCat.ofHom (fan.basisGenericStarRingMap 𝕜 basis ray generic).toRingHom)
  have local_factorization : star_point ≫ fan.rayFaceAffineSchemeMap 𝕜 ray cone.val contains =
      Spec.map (CommRingCat.ofHom
        (generic.comp (fan.basisConeCoordinateRingEquiv 𝕜 basis).toAlgHom).toRingHom) := by
    rw [rayFaceAffineSchemeMap, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (fan.basisGenericStarRingMap_factorization 𝕜 basis removed ray rfl
      generic coordinate_zero contains)
  refine ⟨star_point ≫ (fan.star ray).affineToricChartι 𝕜 star_regular projected, ?_⟩
  rw [Category.assoc, ← fan.rayFaceAffineSchemeMap_comp_chartι 𝕜 regular ray star_regular cone contains,
    ← Category.assoc, local_factorization]

section CompleteGenericPoints

variable [FiniteDimensional ℝ Ambient]

local instance dichotomyRaySpan_isClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

theorem complete_regular_fieldMorphism_torus_or_star_overField (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    {TargetField : Type} [Field TargetField] [Algebra 𝕜 TargetField]
    (generic : Spec (CommRingCat.of TargetField) ⟶ fan.algebraicRealization 𝕜 regular)
    (over_base : generic ≫ fan.structureMap 𝕜 regular =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 TargetField))) :
    (∃ torus_generic : Spec (CommRingCat.of TargetField) ⟶ fan.denseTorus 𝕜,
      torus_generic ≫ fan.denseTorusι 𝕜 regular nonempty = generic) ∨
    (∃ ray : fan.Ray, ∃ star_generic : Spec (CommRingCat.of TargetField) ⟶
      (fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray),
        star_generic ≫ fan.completeStarOrbitClosureMap 𝕜 complete regular ray = generic) := by
  classical
  obtain ⟨dimension, basis, cone_basis, chart_generic, chart_factorization⟩ :=
    fan.fieldMorphism_factors_basisChart 𝕜 complete regular generic
  let cone : fan.cones := ⟨_, cone_basis⟩
  let chart_ring : affineCoordinateRing 𝕜 fan.lattice cone.val →+* TargetField :=
    (Spec.preimage chart_generic).hom
  have chart_scalars : ∀ scalar : 𝕜,
      chart_ring (algebraMap 𝕜 _ scalar) = algebraMap 𝕜 TargetField scalar := by
    have chart_over_base : chart_generic ≫ fan.affineToricChartι 𝕜 regular cone ≫
        fan.structureMap 𝕜 regular = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 TargetField)) := by
      rw [← Category.assoc, chart_factorization]
      exact over_base
    rw [fan.chartι_comp_structureMap 𝕜 regular cone,
      ← Spec.map_preimage chart_generic, ← Spec.map_comp] at chart_over_base
    have ring_eq := Spec.map_injective chart_over_base
    exact fun scalar => ConcreteCategory.congr_hom ring_eq scalar
  let chart_algebra : affineCoordinateRing 𝕜 fan.lattice cone.val →ₐ[𝕜] TargetField :=
    { chart_ring with commutes' := chart_scalars }
  let polynomial_generic := chart_algebra.comp (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm.toAlgHom
  have chart_map_eq : Spec.map (CommRingCat.ofHom
      (polynomial_generic.comp (fan.basisConeCoordinateRingEquiv 𝕜 basis).toAlgHom).toRingHom) =
        chart_generic := by
    rw [← Spec.map_preimage chart_generic]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro element
    exact congrArg chart_ring ((fan.basisConeCoordinateRingEquiv 𝕜 basis).symm_apply_apply element)
  by_cases coordinates_nonzero : ∀ index, polynomial_generic (MvPolynomial.X index) ≠ 0
  · obtain ⟨torus_generic, torus_factorization⟩ :=
      fan.basisGeneric_torusChart_factorization 𝕜 regular basis cone_basis polynomial_generic coordinates_nonzero
    left
    refine ⟨torus_generic, ?_⟩
    rw [fan.denseTorusι_eq 𝕜 regular nonempty (Nonempty.intro cone), fan.denseTorusι_face 𝕜 regular cone,
      ← Category.assoc, torus_factorization, chart_map_eq]
    exact chart_factorization
  · obtain ⟨removed, coordinate_zero⟩ := not_forall.mp coordinates_nonzero
    have zero_eq : polynomial_generic (MvPolynomial.X removed) = 0 := not_ne_iff.mp coordinate_zero
    let ray := fan.coneBasisRay basis cone_basis removed
    obtain ⟨star_generic, star_factorization⟩ := fan.basisGeneric_starGlobal_factorization 𝕜
      regular basis cone_basis removed (fan.star_isRegular complete regular ray) polynomial_generic zero_eq
    right
    refine ⟨ray, star_generic, ?_⟩
    exact star_factorization.trans (by rw [chart_map_eq]; exact chart_factorization)

theorem complete_regular_fieldMorphism_torus_or_star (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    {TargetField : Type} [Field TargetField]
    (generic : Spec (CommRingCat.of TargetField) ⟶ fan.algebraicRealization 𝕜 regular) :
    (∃ torus_generic : Spec (CommRingCat.of TargetField) ⟶ fan.denseTorus 𝕜,
      torus_generic ≫ fan.denseTorusι 𝕜 regular nonempty = generic) ∨
    (∃ ray : fan.Ray, ∃ star_generic : Spec (CommRingCat.of TargetField) ⟶
      (fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray),
        star_generic ≫ fan.completeStarOrbitClosureMap 𝕜 complete regular ray = generic) := by
  let base_ring : 𝕜 →+* TargetField := (Spec.preimage (generic ≫ fan.structureMap 𝕜 regular)).hom
  let : Algebra 𝕜 TargetField := base_ring.toAlgebra
  exact fan.complete_regular_fieldMorphism_torus_or_star_overField 𝕜 complete regular nonempty generic
    (Spec.map_preimage (generic ≫ fan.structureMap 𝕜 regular)).symm

end CompleteGenericPoints

end TauCeti.Toric.Fan
