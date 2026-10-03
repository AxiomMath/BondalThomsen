module

public import BondalThomsen.Toric.Projective.MonomialStructure
public import BondalThomsen.Toric.Positivity.GlobalSectionsFinite
public import BondalThomsen.Toric.Scheme.BasisChart

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Module Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

attribute [local instance] MvPolynomial.gradedAlgebra

variable {Index Ring : Type} [CommRing Ring] [Algebra 𝕜 Ring]

theorem projectiveAwayEvaluation_surjective_iff_adjoin
    (coordinates : Index → Ring) (denominator : Index)
    (denominator_value : coordinates denominator = 1) :
    Function.Surjective (projectiveAwayEvaluation 𝕜 (algebraMap 𝕜 Ring) coordinates
      (MvPolynomial.X denominator) (1 : Ringˣ)
      (by simpa only [MvPolynomial.eval₂Hom_X', Units.val_one] using denominator_value)) ↔
      Algebra.adjoin 𝕜 (Set.range coordinates) = ⊤ := by
  classical
  let pullback := projectiveAwayEvaluation 𝕜 (algebraMap 𝕜 Ring) coordinates
    (MvPolynomial.X denominator) (1 : Ringˣ)
    (by simpa only [MvPolynomial.eval₂Hom_X', Units.val_one] using denominator_value)
  have fraction_value (power : ℕ) (numerator : MvPolynomial Index 𝕜)
      (homogeneous : numerator ∈ MvPolynomial.homogeneousSubmodule Index 𝕜 (power • 1)) :
      pullback (HomogeneousLocalization.Away.mk _
        (MvPolynomial.isHomogeneous_X 𝕜 denominator) power numerator homogeneous) =
          MvPolynomial.aeval coordinates numerator := by
    dsimp [pullback]
    rw [projectiveAwayEvaluation_mk]
    simp only [inv_one, Units.val_one, one_pow, mul_one]
    rfl
  constructor
  · intro surjective
    apply top_unique
    intro value _
    obtain ⟨fraction, rfl⟩ := surjective value
    obtain ⟨power, numerator, homogeneous, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective _
        (MvPolynomial.isHomogeneous_X 𝕜 denominator) fraction
    rw [fraction_value, ← MvPolynomial.aeval_range]
    exact ⟨numerator, rfl⟩
  · intro generated value
    have belongs : value ∈ Algebra.adjoin 𝕜 (Set.range coordinates) := by
      rw [generated]
      trivial
    change ∃ fraction, pullback fraction = value
    induction belongs using Algebra.adjoin_induction with
    | mem value member =>
        obtain ⟨index, rfl⟩ := member
        refine ⟨HomogeneousLocalization.Away.mk _
          (MvPolynomial.isHomogeneous_X 𝕜 denominator) 1 (MvPolynomial.X index)
          (by simpa using MvPolynomial.isHomogeneous_X 𝕜 index), ?_⟩
        rw [fraction_value]
        exact MvPolynomial.aeval_X coordinates index
    | algebraMap scalar =>
        refine ⟨HomogeneousLocalization.Away.mk _
          (MvPolynomial.isHomogeneous_X 𝕜 denominator) 0 (MvPolynomial.C scalar)
          (by simp), ?_⟩
        rw [fraction_value]
        exact MvPolynomial.aeval_C coordinates scalar
    | add first second _ _ first_preimage second_preimage =>
        obtain ⟨first_fraction, first_value⟩ := first_preimage
        obtain ⟨second_fraction, second_value⟩ := second_preimage
        exact ⟨first_fraction + second_fraction, by rw [map_add, first_value, second_value]⟩
    | mul first second _ _ first_preimage second_preimage =>
        obtain ⟨first_fraction, first_value⟩ := first_preimage
        obtain ⟨second_fraction, second_value⟩ := second_preimage
        exact ⟨first_fraction * second_fraction, by rw [map_mul, first_value, second_value]⟩

end BondalThomsen

namespace TauCeti.Toric.Fan

attribute [local instance] MvPolynomial.gradedAlgebra

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem allDivisorMonomialCharacters_finite (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    Finite (fan.globalDivisorSectionExponents divisor) :=
  (fan.globalDivisorSectionExponents_finite complete regular divisor).to_subtype

noncomputable def allDivisorMonomialSheafBasis (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    Basis (fan.globalDivisorSectionExponents divisor) 𝕜
      Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, ⊤) :=
  (fan.globalDivisorLaurentSectionBasis 𝕜 divisor).map
    (fan.invariantDivisorSheafGlobalSectionsEquiv 𝕜 complete regular divisor)

noncomputable def allDivisorMonomialProjectiveSpace (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)

variable (fan : Fan embedding) {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor)

noncomputable def basisConeDualStep (index : Fin dimension) :
    dualSemigroup fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) :=
  (fan.basisConeDualSemigroupEquiv basis).symm (Finsupp.single index 1)

omit [FiniteDimensional ℝ Ambient] in
theorem basisConeDualStep_apply (index coordinate : Fin dimension) :
    (fan.basisConeDualStep basis index : Lattice →+ ℤ) (basis coordinate) =
      if index = coordinate then 1 else 0 := by
  classical
  simp [basisConeDualStep, basisConeDualSemigroupEquiv, Finsupp.single_apply, eq_comm]

omit [FiniteDimensional ℝ Ambient] in
theorem basisConeDualStepMonomial_eq_variable (index : Fin dimension) :
    MonoidAlgebra.single (ofAdd (fan.basisConeDualStep basis index)) (1 : 𝕜) =
      (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm (MvPolynomial.X index) := by
  apply (fan.basisConeCoordinateRingEquiv 𝕜 basis).injective
  rw [AlgEquiv.apply_symm_apply, basisConeCoordinateRingEquiv, AlgEquiv.trans_apply,
    MonoidAlgebra.domCongr_single]
  simp only [AddEquiv.toMultiplicative_apply_apply, toAdd_ofAdd,
    basisConeDualStep, AddEquiv.apply_symm_apply]
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv 𝕜 𝕜 (Fin dimension →₀ ℕ)).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (AddMonoidAlgebra.toMultiplicativeAlgEquiv_single _ _).symm

noncomputable def allDivisorMonomialRatio (exponent : fan.globalDivisorSectionExponents divisor) :
    affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) :=
  fan.globalDivisorChartCoefficient 𝕜 basis cone_basis divisor
    (fan.globalDivisorLaurentSectionBasis 𝕜 divisor exponent)

omit [FiniteDimensional ℝ Ambient] in
theorem allDivisorMonomialRatio_reconstruct
    (exponent : fan.globalDivisorSectionExponents divisor) :
    fan.coneCharacterSectionMap 𝕜
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))
      (fan.coneDivisorCharacter basis cone_basis divisor)
      (fan.allDivisorMonomialRatio 𝕜 basis cone_basis divisor exponent) =
        MonoidAlgebra.single exponent.val 1 := by
  rw [allDivisorMonomialRatio, globalDivisorChartCoefficient_reconstruct,
    globalDivisorLaurentSectionBasis_val]

def BasisDivisorStepsAdmissible : Prop :=
  ∀ index : Fin dimension, ∀ ray : fan.Ray,
    -divisor ray ≤ (fan.coneDivisorCharacter basis cone_basis divisor +
      (fan.basisConeDualStep basis index : Lattice →+ ℤ)) ray.val

noncomputable def basisDivisorStepExponent
    (steps : fan.BasisDivisorStepsAdmissible basis cone_basis divisor) (index : Fin dimension) :
    fan.globalDivisorSectionExponents divisor :=
  ⟨ofAdd (fan.coneDivisorCharacter basis cone_basis divisor +
    (fan.basisConeDualStep basis index : Lattice →+ ℤ)), steps index⟩

omit [FiniteDimensional ℝ Ambient] in
theorem allDivisorMonomialRatio_step
    (steps : fan.BasisDivisorStepsAdmissible basis cone_basis divisor) (index : Fin dimension) :
    fan.allDivisorMonomialRatio 𝕜 basis cone_basis divisor
      (fan.basisDivisorStepExponent basis cone_basis divisor steps index) =
        (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm (MvPolynomial.X index) := by
  rw [← fan.basisConeDualStepMonomial_eq_variable 𝕜 basis index]
  apply fan.coneCharacterSectionMap_injective 𝕜 _
    (fan.coneDivisorCharacter basis cone_basis divisor)
  rw [allDivisorMonomialRatio_reconstruct, coneCharacterSectionMap_single]
  rfl

omit [FiniteDimensional ℝ Ambient] in
theorem allDivisorMonomialRatios_generate_of_steps
    (steps : fan.BasisDivisorStepsAdmissible basis cone_basis divisor) :
    Algebra.adjoin 𝕜 (Set.range (fan.allDivisorMonomialRatio 𝕜 basis cone_basis divisor)) = ⊤ := by
  let generated := Algebra.adjoin 𝕜 (Set.range (fan.allDivisorMonomialRatio 𝕜 basis cone_basis divisor))
  have variable_mem (index : Fin dimension) :
      (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm (MvPolynomial.X index) ∈ generated := by
    rw [← fan.allDivisorMonomialRatio_step 𝕜 basis cone_basis divisor steps index]
    exact Algebra.subset_adjoin ⟨_, rfl⟩
  have polynomial_mem (polynomial : MvPolynomial (Fin dimension) 𝕜) :
      (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm polynomial ∈ generated := by
    induction polynomial using MvPolynomial.induction_on with
    | C scalar =>
        change (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm (algebraMap 𝕜 _ scalar) ∈ generated
        rw [AlgEquiv.commutes]
        exact generated.algebraMap_mem scalar
    | add first second first_mem second_mem =>
        rw [map_add]
        exact generated.add_mem first_mem second_mem
    | mul_X polynomial index polynomial_mem =>
        rw [map_mul]
        exact generated.mul_mem polynomial_mem (variable_mem index)
  apply top_unique
  intro value _
  simpa using polynomial_mem ((fan.basisConeCoordinateRingEquiv 𝕜 basis) value)

noncomputable def basisDivisorDenominator
    (admissible : ∀ ray : fan.Ray,
      -divisor ray ≤ fan.coneDivisorCharacter basis cone_basis divisor ray.val) :
    fan.globalDivisorSectionExponents divisor :=
  ⟨ofAdd (fan.coneDivisorCharacter basis cone_basis divisor), admissible⟩

omit [FiniteDimensional ℝ Ambient] in
theorem allDivisorMonomialRatio_denominator
    (admissible : ∀ ray : fan.Ray,
      -divisor ray ≤ fan.coneDivisorCharacter basis cone_basis divisor ray.val) :
    fan.allDivisorMonomialRatio 𝕜 basis cone_basis divisor
      (fan.basisDivisorDenominator basis cone_basis divisor admissible) = 1 := by
  apply fan.coneCharacterSectionMap_injective 𝕜 _
    (fan.coneDivisorCharacter basis cone_basis divisor)
  rw [allDivisorMonomialRatio_reconstruct]
  change _ = (fan.coneDivisorSectionGenerator 𝕜 basis cone_basis divisor : fan.LaurentCharacterAlgebra 𝕜)
  rw [fan.coneDivisorSectionGenerator_val 𝕜]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def allDivisorMonomialChartRingMap
    (admissible : ∀ ray : fan.Ray,
      -divisor ray ≤ fan.coneDivisorCharacter basis cone_basis divisor ray.val) :
    HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (fan.globalDivisorSectionExponents divisor) 𝕜)
      (MvPolynomial.X (fan.basisDivisorDenominator basis cone_basis divisor admissible)) →+*
        affineCoordinateRing 𝕜 fan.lattice
          (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) :=
  BondalThomsen.projectiveAwayEvaluation 𝕜 (algebraMap 𝕜 _)
    (fan.allDivisorMonomialRatio 𝕜 basis cone_basis divisor)
    (MvPolynomial.X (fan.basisDivisorDenominator basis cone_basis divisor admissible)) 1
    (by simpa using fan.allDivisorMonomialRatio_denominator 𝕜 basis cone_basis divisor admissible)

omit [FiniteDimensional ℝ Ambient] in
theorem allDivisorMonomialChartRingMap_surjective_of_steps
    (admissible : ∀ ray : fan.Ray,
      -divisor ray ≤ fan.coneDivisorCharacter basis cone_basis divisor ray.val)
    (steps : fan.BasisDivisorStepsAdmissible basis cone_basis divisor) :
    Function.Surjective (fan.allDivisorMonomialChartRingMap 𝕜 basis cone_basis divisor admissible) :=
  (BondalThomsen.projectiveAwayEvaluation_surjective_iff_adjoin 𝕜 _ _
    (fan.allDivisorMonomialRatio_denominator 𝕜 basis cone_basis divisor admissible)).mpr
      (fan.allDivisorMonomialRatios_generate_of_steps 𝕜 basis cone_basis divisor steps)

noncomputable def allDivisorMonomialAffineChartMap
    (admissible : ∀ ray : fan.Ray,
      -divisor ray ≤ fan.coneDivisorCharacter basis cone_basis divisor ray.val) :=
  Spec.map (CommRingCat.ofHom
    (fan.allDivisorMonomialChartRingMap 𝕜 basis cone_basis divisor admissible))

omit [FiniteDimensional ℝ Ambient] in
theorem allDivisorMonomialAffineChartMap_isClosedImmersion_of_steps
    (admissible : ∀ ray : fan.Ray,
      -divisor ray ≤ fan.coneDivisorCharacter basis cone_basis divisor ray.val)
    (steps : fan.BasisDivisorStepsAdmissible basis cone_basis divisor) :
    IsClosedImmersion (fan.allDivisorMonomialAffineChartMap 𝕜 basis cone_basis divisor admissible) :=
  IsClosedImmersion.spec_of_surjective _
    (fan.allDivisorMonomialChartRingMap_surjective_of_steps 𝕜 basis cone_basis divisor admissible steps)

omit [FiniteDimensional ℝ Ambient] in
theorem coneDivisorCharacter_nsmul (multiple : ℕ) :
    fan.coneDivisorCharacter basis cone_basis (multiple • divisor) =
      multiple • fan.coneDivisorCharacter basis cone_basis divisor := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  simp

def BasisDivisorStrictSupport : Prop :=
  ∀ ray : fan.Ray, ray.val ∉ Set.range basis →
    -divisor ray < fan.coneDivisorCharacter basis cone_basis divisor ray.val

omit [FiniteDimensional ℝ Ambient] in
theorem basisDivisor_admissible_of_strictSupport
    (strict_support : fan.BasisDivisorStrictSupport basis cone_basis divisor) :
    ∀ ray : fan.Ray, -divisor ray ≤ fan.coneDivisorCharacter basis cone_basis divisor ray.val := by
  intro ray
  by_cases generator : ray.val ∈ Set.range basis
  · obtain ⟨index, same⟩ := generator
    have same_ray : fan.basisRay basis cone_basis index = ray := Subtype.ext same
    rw [← same, fan.coneDivisorCharacter_basis, same_ray]
  · exact (strict_support ray generator).le

omit [FiniteDimensional ℝ Ambient] in
theorem basisDivisor_multiple_admissible_of_strictSupport
    (strict_support : fan.BasisDivisorStrictSupport basis cone_basis divisor) (multiple : ℕ) :
    ∀ ray : fan.Ray,
      -(multiple • divisor) ray ≤
        fan.coneDivisorCharacter basis cone_basis (multiple • divisor) ray.val := by
  intro ray
  rw [fan.coneDivisorCharacter_nsmul basis cone_basis divisor multiple]
  simp only [Finsupp.smul_apply, AddMonoidHom.nsmul_apply, Int.nsmul_eq_mul]
  have bound := fan.basisDivisor_admissible_of_strictSupport basis cone_basis divisor strict_support ray
  have multiplied := mul_le_mul_of_nonneg_left bound (show (0 : ℤ) ≤ multiple by positivity)
  simpa only [mul_neg] using multiplied

omit [FiniteDimensional ℝ Ambient] in
theorem basisDivisorStepsAdmissible_large_multiples
    (strict_support : fan.BasisDivisorStrictSupport basis cone_basis divisor) :
    ∃ threshold : ℕ, 0 < threshold ∧ ∀ multiple : ℕ, threshold ≤ multiple →
      fan.BasisDivisorStepsAdmissible basis cone_basis (multiple • divisor) := by
  obtain ⟨bound, bounds⟩ := Finite.exists_le
    (fun pair : Fin dimension × fan.Ray =>
      ((fan.basisConeDualStep basis pair.1 : Lattice →+ ℤ) pair.2.val).natAbs)
  refine ⟨bound + 1, by omega, ?_⟩
  intro multiple large index ray
  rw [fan.coneDivisorCharacter_nsmul basis cone_basis divisor multiple]
  simp only [Finsupp.smul_apply, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
    Int.nsmul_eq_mul]
  by_cases generator : ray.val ∈ Set.range basis
  · obtain ⟨coordinate, same⟩ := generator
    have same_ray : fan.basisRay basis cone_basis coordinate = ray := Subtype.ext same
    have local_value : fan.coneDivisorCharacter basis cone_basis divisor ray.val = -divisor ray := by
      rw [← same, fan.coneDivisorCharacter_basis, same_ray]
    have step_nonnegative :=
      (fan.mem_dualSemigroup_basisCone_iff basis _).mp
        (fan.basisConeDualStep basis index).property coordinate
    rw [same] at step_nonnegative
    rw [local_value]
    nlinarith
  · have gap_positive : 1 ≤ fan.coneDivisorCharacter basis cone_basis divisor ray.val + divisor ray := by
      have strict := strict_support ray generator
      omega
    have step_bound : -(bound : ℤ) ≤
        (fan.basisConeDualStep basis index : Lattice →+ ℤ) ray.val := by
      have absolute_bound :
          (((fan.basisConeDualStep basis index : Lattice →+ ℤ) ray.val).natAbs : ℤ) ≤ bound := by
        exact_mod_cast bounds (index, ray)
      have negative_bound := Int.le_natAbs (a := -((fan.basisConeDualStep basis index : Lattice →+ ℤ) ray.val))
      rw [Int.natAbs_neg] at negative_bound
      omega
    have large_integer : (bound : ℤ) ≤ multiple := by exact_mod_cast (by omega : bound ≤ multiple)
    have multiple_nonnegative : (0 : ℤ) ≤ multiple := by positivity
    have gap_multiple := mul_le_mul_of_nonneg_left gap_positive multiple_nonnegative
    nlinarith

end TauCeti.Toric.Fan
