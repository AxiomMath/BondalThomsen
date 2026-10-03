module

public import BondalThomsen.Toric.Scheme.StarClosedGluing
public import BondalThomsen.Toric.Scheme.Separated
public import BondalThomsen.Fan.Completeness
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

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

variable [FiniteDimensional ℝ Ambient]

local instance starRaySpan_isClosed (fan : Fan embedding) (ray : fan.Ray) :
    IsClosed ((Submodule.span ℝ {embedding ray.val}) : Set Ambient) :=
  Submodule.closed_of_finiteDimensional _

omit [FiniteDimensional ℝ Ambient] in
theorem affineStructureMap_eqToHom (fan : Fan embedding)
    {first second : PointedCone ℝ Ambient} (equality : first = second) :
    eqToHom (congrArg (affineToricScheme 𝕜 fan.lattice) equality) ≫
        Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice second))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice first))) := by
  subst second
  simp

omit [FiniteDimensional ℝ Ambient] in
theorem rayFaceAffineSchemeMap_comp_structureMap (fan : Fan embedding)
    (ray : fan.Ray) (cone : PointedCone ℝ Ambient) (contains : embedding ray.val ∈ cone) :
    fan.rayFaceAffineSchemeMap 𝕜 ray cone contains ≫
        Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 (fan.star ray).lattice
        (PointedCone.map (fan.starProjection ray) cone)))) := by
  rw [rayFaceAffineSchemeMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro scalar
  exact (fan.rayFaceCoordinateRingMap 𝕜 ray cone contains).commutes scalar

omit [FiniteDimensional ℝ Ambient] in
theorem starOrbitClosureMap_comp_structureMap (fan : Fan embedding)
    (regular : fan.IsRegular) (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular) :
    fan.starOrbitClosureMap 𝕜 regular ray star_regular ≫ fan.structureMap 𝕜 regular =
      (fan.star ray).structureMap 𝕜 star_regular := by
  apply ((fan.star ray).isColimitAffineToricCocone 𝕜 star_regular).hom_ext
  intro cone
  change (fan.star ray).affineToricChartι 𝕜 star_regular cone ≫
    (fan.starOrbitClosureMap 𝕜 regular ray star_regular ≫ fan.structureMap 𝕜 regular) =
      (fan.star ray).affineToricChartι 𝕜 star_regular cone ≫
        (fan.star ray).structureMap 𝕜 star_regular
  rw [← Category.assoc, fan.affineToricChartι_comp_starOrbitClosureMap 𝕜 regular ray star_regular,
    Category.assoc, fan.chartι_comp_structureMap 𝕜 regular,
    (fan.star ray).chartι_comp_structureMap 𝕜 star_regular]
  dsimp only [rayFaceChartMap]
  rw [Category.assoc, fan.rayFaceAffineSchemeMap_comp_structureMap 𝕜]
  exact (fan.star ray).affineStructureMap_eqToHom 𝕜
    (fan.starConeLift_projected ray cone).symm

noncomputable def starValuativeSquare (fan : Fan embedding) (regular : fan.IsRegular)
    (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular)
    (square : ValuativeCommSq (fan.structureMap 𝕜 regular))
    (generic : Spec (CommRingCat.of square.K) ⟶ (fan.star ray).algebraicRealization 𝕜 star_regular)
    (factorization : generic ≫ fan.starOrbitClosureMap 𝕜 regular ray star_regular = square.i₁) :
    ValuativeCommSq ((fan.star ray).structureMap 𝕜 star_regular) where
  R := square.R
  K := square.K
  i₁ := generic
  i₂ := square.i₂
  commSq := ⟨by
    rw [← fan.starOrbitClosureMap_comp_structureMap 𝕜 regular ray star_regular,
      ← Category.assoc, factorization]
    exact square.commSq.w⟩

omit [FiniteDimensional ℝ Ambient] in
theorem starValuativeSquare_hasLift_transfer (fan : Fan embedding)
    (regular : fan.IsRegular) (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular)
    (square : ValuativeCommSq (fan.structureMap 𝕜 regular))
    (generic : Spec (CommRingCat.of square.K) ⟶ (fan.star ray).algebraicRealization 𝕜 star_regular)
    (factorization : generic ≫ fan.starOrbitClosureMap 𝕜 regular ray star_regular = square.i₁)
    (star_lift : (fan.starValuativeSquare 𝕜 regular ray star_regular square generic factorization).commSq.HasLift) :
    square.commSq.HasLift := by
  obtain ⟨lift, generic_eq, base_eq⟩ := star_lift.exists_lift
  refine CommSq.HasLift.mk' ⟨lift ≫ fan.starOrbitClosureMap 𝕜 regular ray star_regular, ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun morphism => morphism ≫ fan.starOrbitClosureMap 𝕜 regular ray star_regular)
        generic_eq).trans factorization)
  · rw [Category.assoc, fan.starOrbitClosureMap_comp_structureMap 𝕜]
    exact base_eq

omit [FiniteDimensional ℝ Ambient] in
theorem starImage_valuativeSquare_hasLift_of_starExistence (fan : Fan embedding)
    (regular : fan.IsRegular) (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular)
    (star_existence : ValuativeCriterion.Existence ((fan.star ray).structureMap 𝕜 star_regular))
    (square : ValuativeCommSq (fan.structureMap 𝕜 regular))
    (generic : Spec (CommRingCat.of square.K) ⟶ (fan.star ray).algebraicRealization 𝕜 star_regular)
    (factorization : generic ≫ fan.starOrbitClosureMap 𝕜 regular ray star_regular = square.i₁) :
    square.commSq.HasLift :=
  fan.starValuativeSquare_hasLift_transfer 𝕜 regular ray star_regular square generic factorization
    (star_existence (fan.starValuativeSquare 𝕜 regular ray star_regular square generic factorization))

theorem starAmbient_finrank_add_one
    (fan : Fan embedding) (ray : fan.Ray) :
    Module.finrank ℝ (fan.StarAmbient ray) + 1 = Module.finrank ℝ Ambient := by
  have nonzero : embedding ray.val ≠ 0 := by
    simpa using fan.lattice.injective.ne ray.property.1.ne_zero
  simpa only [finrank_span_singleton nonzero] using
    (Submodule.span ℝ {embedding ray.val}).finrank_quotient_add_finrank

theorem starAmbient_finrank_lt
    (fan : Fan embedding) (ray : fan.Ray) :
    Module.finrank ℝ (fan.StarAmbient ray) < Module.finrank ℝ Ambient := by
  have equality := fan.starAmbient_finrank_add_one ray
  omega

omit [FiniteDimensional ℝ Ambient] in
theorem basisConeCoordinateRingEquiv_single (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice)
    (character : dualSemigroup fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) (scalar : 𝕜) :
    fan.basisConeCoordinateRingEquiv 𝕜 basis (MonoidAlgebra.single (ofAdd character) scalar) =
      MvPolynomial.monomial (fan.basisConeDualSemigroupEquiv basis character) scalar := by
  rw [basisConeCoordinateRingEquiv, AlgEquiv.trans_apply, MonoidAlgebra.domCongr_single]
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv 𝕜 𝕜 (Fin dimension →₀ ℕ)).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (AddMonoidAlgebra.toMultiplicativeAlgEquiv_single
    (R := 𝕜) (A := 𝕜) (fan.basisConeDualSemigroupEquiv basis character) scalar).symm

omit [FiniteDimensional ℝ Ambient] in
theorem basisGeneric_monomial_zero_of_rayValue_ne_zero (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (removed : Fin dimension) (ray : fan.Ray)
    (equality : basis removed = ray.val) {Target : Type} [CommRing Target] [Algebra 𝕜 Target]
    (generic : MvPolynomial (Fin dimension) 𝕜 →ₐ[𝕜] Target)
    (coordinate_zero : generic (MvPolynomial.X removed) = 0)
    (character : dualSemigroup fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (nonzero : (character : Lattice →+ ℤ) ray.val ≠ 0) :
    generic (fan.basisConeCoordinateRingEquiv 𝕜 basis (MonoidAlgebra.single (ofAdd character) 1)) = 0 := by
  have nonnegative := (fan.mem_dualSemigroup_basisCone_iff basis _).mp character.property removed
  have coordinate_nonzero : (fan.basisConeDualSemigroupEquiv basis character) removed ≠ 0 := by
    change ((character : Lattice →+ ℤ) (basis removed)).toNat ≠ 0
    rw [equality] at nonnegative ⊢
    omega
  rw [fan.basisConeCoordinateRingEquiv_single 𝕜]
  obtain ⟨factor, factorization⟩ := (MvPolynomial.X_dvd_monomial
    (R := 𝕜) (i := removed) (j := fan.basisConeDualSemigroupEquiv basis character)
    (r := 1)).mpr (Or.inr coordinate_nonzero)
  rw [factorization, map_mul, coordinate_zero, zero_mul]

omit [FiniteDimensional ℝ Ambient] in
theorem rayFaceCoordinateRingSection_quotient_single (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (character : dualSemigroup fan.lattice cone)
    (vanishes : (character : Lattice →+ ℤ) ray.val = 0) :
    fan.rayFaceCoordinateRingSection 𝕜 ray cone
      (MonoidAlgebra.single (ofAdd (fan.rayFaceQuotientCharacter ray cone character vanishes)) 1) =
      MonoidAlgebra.single (ofAdd character) 1 := by
  rw [rayFaceCoordinateRingSection, affineCoordinateRingMap_single]
  apply congrArg (fun exponent => MonoidAlgebra.single (ofAdd exponent) (1 : 𝕜))
  apply Subtype.ext
  ext vector
  rw [dualSemigroupMap_apply]
  exact fan.rayCharacterDescend_mkQ ray character vanishes vector

omit [FiniteDimensional ℝ Ambient] in
noncomputable def basisGenericStarRingMap (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (ray : fan.Ray)
    {Target : Type} [CommRing Target] [Algebra 𝕜 Target]
    (generic : MvPolynomial (Fin dimension) 𝕜 →ₐ[𝕜] Target) :
    affineCoordinateRing 𝕜 (fan.star ray).lattice (PointedCone.map (fan.starProjection ray)
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) →ₐ[𝕜] Target :=
  (generic.comp (fan.basisConeCoordinateRingEquiv 𝕜 basis).toAlgHom).comp
    (fan.rayFaceCoordinateRingSection 𝕜 ray _)

omit [FiniteDimensional ℝ Ambient] in
theorem basisGenericStarRingMap_factorization (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (removed : Fin dimension) (ray : fan.Ray)
    (equality : basis removed = ray.val) {Target : Type} [CommRing Target] [Algebra 𝕜 Target]
    (generic : MvPolynomial (Fin dimension) 𝕜 →ₐ[𝕜] Target)
    (coordinate_zero : generic (MvPolynomial.X removed) = 0)
    (contains : embedding ray.val ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) :
    (fan.basisGenericStarRingMap 𝕜 basis ray generic).comp
      (fan.rayFaceCoordinateRingMap 𝕜 ray _ contains) =
        generic.comp (fan.basisConeCoordinateRingEquiv 𝕜 basis).toAlgHom := by
  apply MonoidAlgebra.algHom_ext
  · intro exponent
    let character := toAdd exponent
    change generic (fan.basisConeCoordinateRingEquiv 𝕜 basis
      (fan.rayFaceCoordinateRingSection 𝕜 ray _
        (fan.rayFaceCoordinateRingMap 𝕜 ray _ contains (MonoidAlgebra.single (ofAdd character) 1)))) =
      generic (fan.basisConeCoordinateRingEquiv 𝕜 basis (MonoidAlgebra.single (ofAdd character) 1))
    by_cases vanishes : character.val ray.val = 0
    · rw [fan.rayFaceCoordinateRingMap_single_of_zero 𝕜 ray _ contains character vanishes,
        fan.rayFaceCoordinateRingSection_quotient_single 𝕜]
    · rw [fan.rayFaceCoordinateRingMap_single_of_nonzero 𝕜 ray _ contains character vanishes,
        map_zero, map_zero, map_zero]
      exact (fan.basisGeneric_monomial_zero_of_rayValue_ne_zero 𝕜 basis removed ray equality generic
        coordinate_zero character vanishes).symm
  · exact Subsingleton.elim _ _

end TauCeti.Toric.Fan
