module

public import BondalThomsen.Fan.CompleteFanGlobalFunctions
public import BondalThomsen.Toric.Scheme.BasisChart
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Regular
public import Mathlib.RingTheory.RingHom.Integral
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Expand
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

open AlgebraicGeometry CategoryTheory Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] {embedding : Lattice →+ Ambient}

def multiplicationFanHom (fan : Fan embedding) (degree : ℕ) : FanHom fan fan where
  latticeMap := nsmulAddMonoidHom degree
  realMap := (degree : ℝ) • LinearMap.id
  map_lattice vector := by simp [Nat.cast_smul_eq_nsmul]
  map_cone cone member := by
    refine ⟨cone, member, ?_⟩
    rintro _ ⟨vector, contained, rfl⟩
    exact cone.smul_mem (Nat.cast_nonneg degree) contained

@[simp] theorem multiplicationFanHom_lattice (fan : Fan embedding) (degree : ℕ)
    (vector : Lattice) : (fan.multiplicationFanHom degree).latticeMap vector = degree • vector := rfl

@[simp] theorem multiplicationFanHom_real (fan : Fan embedding) (degree : ℕ)
    (vector : Ambient) : (fan.multiplicationFanHom degree).realMap vector = (degree : ℝ) • vector := rfl

theorem multiplicationFanHom_map_cone (fan : Fan embedding) {degree : ℕ}
    (positive : 0 < degree) (cone : PointedCone ℝ Ambient) :
    cone.map (fan.multiplicationFanHom degree).realMap = cone := by
  have scalar_positive : (0 : ℝ) < degree := by exact_mod_cast positive
  ext vector
  constructor
  · rintro ⟨original, member, rfl⟩
    exact cone.smul_mem scalar_positive.le member
  · intro member
    refine ⟨(degree : ℝ)⁻¹ • vector, cone.smul_mem (inv_nonneg.mpr scalar_positive.le) member, ?_⟩
    simp [smul_smul, scalar_positive.ne']

noncomputable def toricMultiplication (fan : Fan embedding) (regular : fan.IsRegular)
    (degree : ℕ) : fan.algebraicRealization 𝕜 regular ⟶ fan.algebraicRealization 𝕜 regular :=
  (fan.multiplicationFanHom degree).algebraicMap 𝕜 regular regular

noncomputable def toricMultiplicationRing (fan : Fan embedding) (degree : ℕ)
    (cone : PointedCone ℝ Ambient) :
    affineCoordinateRing 𝕜 fan.lattice cone →ₐ[𝕜] (affineCoordinateRing 𝕜) fan.lattice cone :=
  affineCoordinateRingMap 𝕜 fan.lattice fan.lattice
    (fan.multiplicationFanHom degree).latticeMap (fan.multiplicationFanHom degree).realMap
    (fan.multiplicationFanHom degree).map_lattice
    (fun _ member => cone.smul_mem (Nat.cast_nonneg degree) member)

theorem toricMultiplication_dualSemigroup (fan : Fan embedding) (degree : ℕ)
    (cone : PointedCone ℝ Ambient) (character : dualSemigroup fan.lattice cone) :
    dualSemigroupMap fan.lattice fan.lattice
      (fan.multiplicationFanHom degree).latticeMap (fan.multiplicationFanHom degree).realMap
      (fan.multiplicationFanHom degree).map_lattice
      (fun _ member => cone.smul_mem (Nat.cast_nonneg degree) member) character =
        degree • character := by
  apply Subtype.ext
  ext vector
  change (character : Lattice →+ ℤ) (degree • vector) = _
  simp

theorem toricMultiplicationRing_single (fan : Fan embedding) (degree : ℕ)
    (cone : PointedCone ℝ Ambient) (character : dualSemigroup fan.lattice cone) (coefficient : 𝕜) :
    fan.toricMultiplicationRing 𝕜 degree cone (MonoidAlgebra.single (ofAdd character) coefficient) =
      MonoidAlgebra.single (ofAdd (degree • character)) coefficient := by
  unfold toricMultiplicationRing
  erw [affineCoordinateRingMap_single, fan.toricMultiplication_dualSemigroup]
  rfl

theorem toricMultiplicationRing_character (fan : Fan embedding) (degree : ℕ)
    (cone : PointedCone ℝ Ambient) (character : dualSemigroup fan.lattice cone) :
    fan.toricMultiplicationRing 𝕜 degree cone (MonoidAlgebra.single (ofAdd character) 1) =
      MonoidAlgebra.single (ofAdd character) (1 : 𝕜) ^ degree := by
  simp only [fan.toricMultiplicationRing_single 𝕜, MonoidAlgebra.single_pow, one_pow,
    ofAdd_nsmul]

noncomputable def toricMultiplicationChart (fan : Fan embedding) (degree : ℕ)
    (cone : fan.cones) : fan.affineToricChart 𝕜 cone ⟶ fan.affineToricChart 𝕜 cone :=
  Spec.map (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree cone.val).toRingHom)

theorem affineToricChartι_comp_toricMultiplication (fan : Fan embedding)
    (regular : fan.IsRegular) {degree : ℕ} (positive : 0 < degree) (cone : fan.cones) :
    fan.affineToricChartι 𝕜 regular cone ≫ fan.toricMultiplication 𝕜 regular degree =
      fan.toricMultiplicationChart 𝕜 degree cone ≫ fan.affineToricChartι 𝕜 regular cone := by
  rw [toricMultiplication, FanHom.affineToricChartι_comp_algebraicMap]
  let target : fan.cones := ⟨(fan.multiplicationFanHom degree).leastCone cone.property,
    (fan.multiplicationFanHom degree).leastCone_mem cone.property⟩
  have face : target.val.IsFaceOf cone.val := fan.isFaceOf_of_le cone.property target.property
    ((fan.multiplicationFanHom degree).leastCone_le cone.property cone.property
      (fan.multiplicationFanHom_map_cone positive cone.val).le)
  have factor := fan.faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 regular
    (τ := target) (σ := cone) face
  rw [← factor, ← Category.assoc]
  congr 1
  rw [FanHom.affineToricChartMap_def, faceAffineToricSchemeMap_eq_affineToricSchemeMap,
    affineToricSchemeMap_comp]
  simp only [AddMonoidHom.id_comp, LinearMap.id_comp]
  rfl

theorem toricMultiplicationRing_isIntegral (fan : Fan embedding) {degree : ℕ}
    (positive : 0 < degree) (cone : PointedCone ℝ Ambient) :
    (fan.toricMultiplicationRing 𝕜 degree cone).toRingHom.IsIntegral := by
  let ring_map := (fan.toricMultiplicationRing 𝕜 degree cone).toRingHom
  let := ring_map.toAlgebra
  intro polynomial
  change IsIntegral (affineCoordinateRing 𝕜 fan.lattice cone) polynomial
  refine MonoidAlgebra.induction_linear polynomial ?_ ?_ ?_
  · exact isIntegral_zero
  · intro first second first_integral second_integral
    exact first_integral.add second_integral
  · intro character coefficient
    have monomial_integral :
        IsIntegral (affineCoordinateRing 𝕜 fan.lattice cone)
          (MonoidAlgebra.single character (1 : 𝕜)) := by
      apply IsIntegral.of_pow positive
      have power := fan.toricMultiplicationRing_character 𝕜 degree cone character.toAdd
      change fan.toricMultiplicationRing 𝕜 degree cone (MonoidAlgebra.single character 1) =
        MonoidAlgebra.single character (1 : 𝕜) ^ degree at power
      have integral : IsIntegral (affineCoordinateRing 𝕜 fan.lattice cone)
          (ring_map (MonoidAlgebra.single character (1 : 𝕜))) := isIntegral_algebraMap
      change IsIntegral (affineCoordinateRing 𝕜 fan.lattice cone)
        (fan.toricMultiplicationRing 𝕜 degree cone (MonoidAlgebra.single character (1 : 𝕜))) at integral
      rw [power] at integral
      exact integral
    have scalar_integral :
        IsIntegral (affineCoordinateRing 𝕜 fan.lattice cone)
          (MonoidAlgebra.single (1 : Multiplicative (dualSemigroup fan.lattice cone)) coefficient) := by
      have integral : IsIntegral (affineCoordinateRing 𝕜 fan.lattice cone)
          (ring_map (MonoidAlgebra.single (ofAdd 0) coefficient)) := isIntegral_algebraMap
      change IsIntegral (affineCoordinateRing 𝕜 fan.lattice cone)
        (fan.toricMultiplicationRing 𝕜 degree cone (MonoidAlgebra.single (ofAdd 0) coefficient)) at integral
      rw [fan.toricMultiplicationRing_single 𝕜, smul_zero] at integral
      exact integral
    simpa only [MonoidAlgebra.single_mul_single, one_mul, mul_one] using
      scalar_integral.mul monomial_integral

theorem toricMultiplicationRing_finite (fan : Fan embedding) {degree : ℕ}
    (positive : 0 < degree) (cone : PointedCone ℝ Ambient)
    (regular : IsRegularCone embedding cone) :
    (fan.toricMultiplicationRing 𝕜 degree cone).toRingHom.Finite := by
  let : AddMonoid.FG (dualSemigroup fan.lattice cone) := regular.fg_dualSemigroup fan.lattice
  let : Monoid.FG (Multiplicative (dualSemigroup fan.lattice cone)) := inferInstance
  have finite_type : (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone)).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have composed : ((fan.toricMultiplicationRing 𝕜 degree cone).toRingHom.comp
      (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone))) =
        algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone) := by
    apply RingHom.ext
    intro coefficient
    exact (fan.toricMultiplicationRing 𝕜 degree cone).commutes coefficient
  apply (fan.toricMultiplicationRing_isIntegral 𝕜 positive cone).to_finite
  apply RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone))
  rw [composed]
  exact finite_type

theorem toricMultiplicationChart_isFinite (fan : Fan embedding) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) (cone : fan.cones) :
    IsFinite (fan.toricMultiplicationChart 𝕜 degree cone) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact fan.toricMultiplicationRing_finite 𝕜 positive cone.val (regular cone.property)

theorem toricMultiplicationRing_injective (fan : Fan embedding) {degree : ℕ}
    (positive : 0 < degree) (cone : PointedCone ℝ Ambient) :
    Function.Injective (fan.toricMultiplicationRing 𝕜 degree cone) := by
  unfold toricMultiplicationRing affineCoordinateRingMap
  change Function.Injective (MonoidAlgebra.mapDomainAlgHom 𝕜 𝕜 _)
  change Function.Injective (MonoidAlgebra.mapDomain _)
  apply MonoidAlgebra.mapDomain_injective
  intro first second equality
  have characters := congrArg toAdd equality
  change dualSemigroupMap fan.lattice fan.lattice
      (fan.multiplicationFanHom degree).latticeMap (fan.multiplicationFanHom degree).realMap
      (fan.multiplicationFanHom degree).map_lattice
      (fun _ member => cone.smul_mem (Nat.cast_nonneg degree) member) first.toAdd =
    dualSemigroupMap fan.lattice fan.lattice
      (fan.multiplicationFanHom degree).latticeMap (fan.multiplicationFanHom degree).realMap
      (fan.multiplicationFanHom degree).map_lattice
      (fun _ member => cone.smul_mem (Nat.cast_nonneg degree) member) second.toAdd at characters
  rw [fan.toricMultiplication_dualSemigroup, fan.toricMultiplication_dualSemigroup] at characters
  have same : first.toAdd = second.toAdd := by
    apply Subtype.ext
    ext vector
    have values := congrArg (fun character : dualSemigroup fan.lattice cone =>
      (character : Lattice →+ ℤ) vector) characters
    exact (nsmul_right_injective positive.ne') (by simpa using values)
  exact congrArg ofAdd same

theorem toricMultiplicationChart_surjective (fan : Fan embedding) {degree : ℕ}
    (positive : 0 < degree) (cone : fan.cones) :
    Function.Surjective (fan.toricMultiplicationChart 𝕜 degree cone) :=
  (fan.toricMultiplicationRing_isIntegral 𝕜 positive cone.val).comap_surjective
    (fan.toricMultiplicationRing_injective 𝕜 positive cone.val)

theorem toricMultiplication_surjective (fan : Fan embedding) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) :
    Function.Surjective (fan.toricMultiplication 𝕜 regular degree) := by
  intro point
  obtain ⟨cone, local_point, realization⟩ := fan.exists_affineToricChartι_apply_eq 𝕜 regular point
  obtain ⟨preimage, mapped⟩ := fan.toricMultiplicationChart_surjective 𝕜 positive cone local_point
  refine ⟨fan.affineToricChartι 𝕜 regular cone preimage, ?_⟩
  have chart := congrArg (fun morphism : fan.affineToricChart 𝕜 cone ⟶
      fan.algebraicRealization 𝕜 regular => morphism preimage)
    (fan.affineToricChartι_comp_toricMultiplication 𝕜 regular positive cone)
  simpa only [Scheme.Hom.comp_apply, mapped, realization] using chart

theorem toricMultiplicationRing_basisCone_expand (fan : Fan embedding) (degree : ℕ)
    {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (polynomial : affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :
    fan.basisConeCoordinateRingEquiv 𝕜 basis
      (fan.toricMultiplicationRing 𝕜 degree _ polynomial) =
        MvPolynomial.expand degree (fan.basisConeCoordinateRingEquiv 𝕜 basis polynomial) := by
  refine MonoidAlgebra.induction_linear polynomial ?_ ?_ ?_
  · simp
  · intro first second first_eq second_eq
    simp only [map_add, first_eq, second_eq]
  · intro character coefficient
    change fan.basisConeCoordinateRingEquiv 𝕜 basis
      (fan.toricMultiplicationRing 𝕜 degree _ (MonoidAlgebra.single (ofAdd character.toAdd) coefficient)) = _
    rw [fan.toricMultiplicationRing_single 𝕜]
    simp [basisConeCoordinateRingEquiv, MonoidAlgebra.domCongr]
    have inverse_single : ∀ exponent : Fin dimension →₀ ℕ,
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv 𝕜 𝕜 (Fin dimension →₀ ℕ)).symm
          (MonoidAlgebra.single (ofAdd exponent) coefficient) = MvPolynomial.monomial exponent coefficient := by
      intro exponent
      apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv 𝕜 𝕜 (Fin dimension →₀ ℕ)).injective
      simp only [AlgEquiv.apply_symm_apply]
      exact (AddMonoidAlgebra.toMultiplicativeAlgEquiv_single exponent coefficient).symm
    rw [← ofAdd_nsmul, inverse_single, inverse_single, MvPolynomial.expand_monomial]

end TauCeti.Toric.Fan
