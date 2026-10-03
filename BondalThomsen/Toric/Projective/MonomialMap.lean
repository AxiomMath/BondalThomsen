module

public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Toric.Positivity.GlobalGenerationCriterion
public import BondalThomsen.Toric.Scheme.Separated
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped BigOperators

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Index : Type} {Ring : Type} [CommRing Ring]

theorem homogeneousCoordinateEvaluation_scale
    (coordinates : Index → Ring) (scalar : Ring)
    (polynomial : MvPolynomial Index 𝕜) (degree : ℕ)
    (homogeneous : polynomial.IsHomogeneous degree) (constants : 𝕜 →+* Ring) :
    MvPolynomial.eval₂Hom constants (fun index => scalar * coordinates index) polynomial =
      scalar ^ degree * MvPolynomial.eval₂Hom constants coordinates polynomial := by
  classical
  rw [← polynomial.support_sum_monomial_coeff, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro exponent member
  simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum,
    ← homogeneous.degree_eq_sum_deg_support member]
  ring

noncomputable def projectiveAwayEvaluation
    (constants : 𝕜 →+* Ring) (coordinates : Index → Ring)
    (denominator : MvPolynomial Index 𝕜) (denominator_unit : Ringˣ)
    (unit_value : MvPolynomial.eval₂Hom constants coordinates denominator = denominator_unit) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule Index 𝕜) denominator →+* Ring :=
  (Localization.awayLift (MvPolynomial.eval₂Hom constants coordinates) denominator
    (unit_value ▸ denominator_unit.isUnit)).comp
      (algebraMap _ (Localization.Away denominator))

theorem projectiveAwayEvaluation_mk
    (constants : 𝕜 →+* Ring) (coordinates : Index → Ring)
    (denominator : MvPolynomial Index 𝕜) (denominator_unit : Ringˣ)
    (unit_value : MvPolynomial.eval₂Hom constants coordinates denominator = denominator_unit)
    {degree : ℕ} (homogeneous : denominator ∈ MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (power : ℕ) (numerator : MvPolynomial Index 𝕜)
    (numerator_degree : numerator ∈ MvPolynomial.homogeneousSubmodule Index 𝕜 (power • degree)) :
    projectiveAwayEvaluation 𝕜 constants coordinates denominator denominator_unit unit_value
      (HomogeneousLocalization.Away.mk _ homogeneous power numerator numerator_degree) =
        MvPolynomial.eval₂Hom constants coordinates numerator *
          (denominator_unit⁻¹ : Ringˣ) ^ power := by
  unfold projectiveAwayEvaluation
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have inverse : MvPolynomial.eval₂Hom constants coordinates denominator *
      (denominator_unit⁻¹ : Ringˣ) = 1 := by rw [unit_value]; simp
  exact Localization.awayLift_mk _ _ _ _ inverse power

theorem projectiveAwayEvaluation_scale
    (constants : 𝕜 →+* Ring) (coordinates : Index → Ring) (scalar : Ringˣ)
    (denominator : MvPolynomial Index 𝕜) {degree : ℕ}
    (homogeneous : denominator ∈ MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (denominator_unit : Ringˣ)
    (unit_value : MvPolynomial.eval₂Hom constants coordinates denominator = denominator_unit) :
    projectiveAwayEvaluation 𝕜 constants (fun index => scalar * coordinates index)
      denominator (scalar ^ degree * denominator_unit)
      (by rw [homogeneousCoordinateEvaluation_scale 𝕜 _ _ _ _
        (MvPolynomial.mem_homogeneousSubmodule _ _ |>.mp homogeneous), unit_value]; simp) =
        projectiveAwayEvaluation 𝕜 constants coordinates denominator denominator_unit unit_value := by
  ext fraction
  obtain ⟨power, numerator, numerator_degree, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ homogeneous fraction
  rw [projectiveAwayEvaluation_mk, projectiveAwayEvaluation_mk,
    homogeneousCoordinateEvaluation_scale 𝕜 _ _ _ _
      (MvPolynomial.mem_homogeneousSubmodule _ _ |>.mp numerator_degree)]
  simp only [nsmul_eq_mul, mul_inv_rev, Units.inv_pow_eq_pow_inv, Units.val_mul, mul_pow, pow_mul, Nat.cast_id]
  have cancel : (scalar : Ring) ^ (power * degree) *
      ((scalar⁻¹ : Ringˣ) : Ring) ^ (degree * power) = 1 := by
    rw [Nat.mul_comm power degree, ← mul_pow]
    simp
  calc
    _ = ((scalar : Ring) ^ (power * degree) *
        ((scalar⁻¹ : Ringˣ) : Ring) ^ (degree * power)) *
          (MvPolynomial.eval₂Hom constants coordinates numerator *
            ((denominator_unit⁻¹ : Ringˣ) : Ring) ^ power) := by ring
    _ = _ := by rw [cancel, one_mul]

theorem projectiveAwayEvaluation_awayMap
    (constants : 𝕜 →+* Ring) (coordinates : Index → Ring)
    (first second : MvPolynomial Index 𝕜) {first_degree second_degree : ℕ}
    (first_homogeneous : first ∈ MvPolynomial.homogeneousSubmodule Index 𝕜 first_degree)
    (second_homogeneous : second ∈ MvPolynomial.homogeneousSubmodule Index 𝕜 second_degree)
    (first_unit second_unit : Ringˣ)
    (first_value : MvPolynomial.eval₂Hom constants coordinates first = first_unit)
    (second_value : MvPolynomial.eval₂Hom constants coordinates second = second_unit) :
    (projectiveAwayEvaluation 𝕜 constants coordinates (first * second) (first_unit * second_unit)
      (by rw [map_mul, first_value, second_value]; rfl)).comp
        (HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule Index 𝕜)
          second_homogeneous rfl) =
      projectiveAwayEvaluation 𝕜 constants coordinates first first_unit first_value := by
  ext fraction
  obtain ⟨power, numerator, numerator_degree, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ first_homogeneous fraction
  simp only [RingHom.comp_apply, HomogeneousLocalization.awayMap_mk]
  rw [projectiveAwayEvaluation_mk, projectiveAwayEvaluation_mk, map_mul, map_pow, second_value]
  simp only [mul_inv_rev, Units.val_mul, mul_pow]
  calc
    _ = (MvPolynomial.eval₂Hom constants coordinates numerator *
        ((first_unit⁻¹ : Ringˣ) : Ring) ^ power) *
          ((second_unit : Ring) ^ power * ((second_unit⁻¹ : Ringˣ) : Ring) ^ power) := by ring
    _ = _ := by rw [← mul_pow]; simp

noncomputable def projectiveCoordinateMap
    (constants : 𝕜 →+* Ring) (coordinates : Index → Ring) (index : Index)
    (coordinate_unit : Ringˣ) (unit_value : coordinates index = coordinate_unit) :
    Spec (CommRingCat.of Ring) ⟶ Proj (MvPolynomial.homogeneousSubmodule Index 𝕜) :=
  Spec.map (CommRingCat.ofHom
    (projectiveAwayEvaluation 𝕜 constants coordinates (MvPolynomial.X index) coordinate_unit
      (by simpa using unit_value))) ≫
        Proj.awayι _ _ (MvPolynomial.isHomogeneous_X 𝕜 index) (by omega)

theorem projectiveAwayMap_congr
    (constants : 𝕜 →+* Ring) (coordinates : Index → Ring)
    (first second : MvPolynomial Index 𝕜) (first_unit second_unit : Ringˣ)
    (first_value : MvPolynomial.eval₂Hom constants coordinates first = first_unit)
    (second_value : MvPolynomial.eval₂Hom constants coordinates second = second_unit)
    {degree : ℕ} (first_homogeneous : first ∈ MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (second_homogeneous : second ∈ MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (positive : 0 < degree) (same_denominator : first = second) (same_unit : first_unit = second_unit) :
    Spec.map (CommRingCat.ofHom (projectiveAwayEvaluation 𝕜 constants coordinates first first_unit first_value)) ≫
        Proj.awayι _ first first_homogeneous positive =
      Spec.map (CommRingCat.ofHom (projectiveAwayEvaluation 𝕜 constants coordinates second second_unit second_value)) ≫
        Proj.awayι _ second second_homogeneous positive := by
  subst second
  subst second_unit
  rfl

theorem projectiveCoordinateMap_scale
    (constants : 𝕜 →+* Ring) (first second : Index → Ring) (scalar : Ringˣ)
    (same : ∀ index, second index = scalar * first index)
    (first_index second_index : Index) (first_unit second_unit : Ringˣ)
    (first_value : first first_index = first_unit)
    (second_value : second second_index = second_unit) :
    projectiveCoordinateMap 𝕜 constants first first_index first_unit first_value =
      projectiveCoordinateMap 𝕜 constants second second_index second_unit second_value := by
  let other_unit := scalar⁻¹ * second_unit
  have other_value : first second_index = other_unit := by
    rw [same second_index] at second_value
    change first second_index = (scalar⁻¹ : Ringˣ) * second_unit
    rw [← second_value]
    simp [← mul_assoc]
  let product_unit := first_unit * other_unit
  have product_value : MvPolynomial.eval₂Hom constants first
      (MvPolynomial.X first_index * MvPolynomial.X second_index) = product_unit := by
    simp only [map_mul, MvPolynomial.eval₂Hom_X', first_value, other_value, product_unit,
      Units.val_mul]
  let product_evaluation := projectiveAwayEvaluation 𝕜 constants first
    (MvPolynomial.X first_index * MvPolynomial.X second_index) product_unit product_value
  have first_factor := projectiveAwayEvaluation_awayMap 𝕜 constants first
    (MvPolynomial.X first_index) (MvPolynomial.X second_index)
    (MvPolynomial.isHomogeneous_X 𝕜 first_index) (MvPolynomial.isHomogeneous_X 𝕜 second_index)
    first_unit other_unit (by simpa using first_value) (by simpa using other_value)
  have second_scaled : MvPolynomial.eval₂Hom constants second
      (MvPolynomial.X second_index * MvPolynomial.X first_index) =
        scalar ^ 2 * (other_unit * first_unit) := by
    simp only [map_mul, MvPolynomial.eval₂Hom_X', same, first_value, other_value]
    ring
  have scaled := projectiveAwayEvaluation_scale 𝕜 constants first scalar
    (MvPolynomial.X second_index * MvPolynomial.X first_index)
    (SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X 𝕜 second_index)
      (MvPolynomial.isHomogeneous_X 𝕜 first_index)) (other_unit * first_unit)
    (by simp [other_value, first_value])
  have second_factor := projectiveAwayEvaluation_awayMap 𝕜 constants second
    (MvPolynomial.X second_index) (MvPolynomial.X first_index)
    (MvPolynomial.isHomogeneous_X 𝕜 second_index) (MvPolynomial.isHomogeneous_X 𝕜 first_index)
    second_unit (scalar * first_unit) (by simpa using second_value)
    (by simp [same, first_value])
  have second_function : second = fun index => scalar * first index := funext same
  have scaled_unit : second_unit * (scalar * first_unit) =
      scalar ^ 2 * (other_unit * first_unit) := by
    dsimp [other_unit]
    simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  unfold projectiveCoordinateMap
  rw [← first_factor, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι]
  rw [← second_factor, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι]
  simp only [second_function, scaled_unit]
  rw [scaled]
  exact projectiveAwayMap_congr 𝕜 constants first _ _ _ _ _ _ _ _ (by omega)
    (mul_comm _ _) (mul_comm _ _)

end BondalThomsen

namespace BondalThomsen

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem projectiveAwayEvaluation_map {Index Ring TargetRing : Type}
    [CommRing Ring] [CommRing TargetRing]
    (restriction : Ring →+* TargetRing) (constants : 𝕜 →+* Ring) (coordinates : Index → Ring)
    (denominator : MvPolynomial Index 𝕜) {degree : ℕ}
    (homogeneous : denominator ∈ MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (denominator_unit : Ringˣ)
    (unit_value : MvPolynomial.eval₂Hom constants coordinates denominator = denominator_unit) :
    restriction.comp (projectiveAwayEvaluation 𝕜 constants coordinates denominator denominator_unit unit_value) =
      projectiveAwayEvaluation 𝕜 (restriction.comp constants) (fun index => restriction (coordinates index))
        denominator (Units.map restriction denominator_unit)
        (by rw [← MvPolynomial.map_eval₂Hom, unit_value]; rfl) := by
  ext fraction
  obtain ⟨power, numerator, numerator_degree, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ homogeneous fraction
  simp only [RingHom.comp_apply, projectiveAwayEvaluation_mk, map_mul, map_pow,
    MvPolynomial.map_eval₂Hom, ← map_inv, Units.coe_map]
  rfl

theorem projectiveCoordinateMap_map {Index Ring TargetRing : Type}
    [CommRing Ring] [CommRing TargetRing]
    (restriction : Ring →+* TargetRing) (constants : 𝕜 →+* Ring) (coordinates : Index → Ring)
    (index : Index) (coordinate_unit : Ringˣ) (unit_value : coordinates index = coordinate_unit) :
    Spec.map (CommRingCat.ofHom restriction) ≫
        projectiveCoordinateMap 𝕜 constants coordinates index coordinate_unit unit_value =
      projectiveCoordinateMap 𝕜 (restriction.comp constants) (fun other => restriction (coordinates other))
        index (Units.map restriction coordinate_unit) (by rw [unit_value]; rfl) := by
  unfold projectiveCoordinateMap
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    projectiveAwayEvaluation_map 𝕜 _ _ _ _ (MvPolynomial.isHomogeneous_X 𝕜 index)]

end BondalThomsen

namespace TauCeti.Toric.Fan

open TauCeti.Toric Module Multiplicative

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def divisorProjectiveRatio (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (support : fan.HasRaySupportInequalities divisor)
    (chart generator : Fin (Nat.card fan.cones)) :
    affineCoordinateRing 𝕜 fan.lattice (fan.divisorLocalCone 𝕜 complete regular chart).val :=
  fan.globalDivisorChartCoefficient 𝕜
    (fan.divisorSectionChartBasis complete regular chart).val.2
    (fan.divisorSectionChartBasis complete regular chart).property.1 divisor
    ⟨fan.characterLaurentMonomial 𝕜 (fan.divisorLocalCharacter 𝕜 complete regular divisor generator),
      fan.divisorLocalCharacter_monomial_mem_global 𝕜 complete regular divisor support generator⟩

noncomputable def divisorProjectiveTransitionUnit (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (first second : Fin (Nat.card fan.cones)) :
    (affineCoordinateRing 𝕜 fan.lattice
      ((fan.divisorLocalCone 𝕜 complete regular first).val ⊓
        (fan.divisorLocalCone 𝕜 complete regular second).val))ˣ := by
  exact fan.coneDivisorTransitionUnit 𝕜
    (fan.divisorSectionChartBasis complete regular first).val.2
    (fan.divisorSectionChartBasis complete regular first).property.1
    (fan.divisorSectionChartBasis complete regular second).val.2
    (fan.divisorSectionChartBasis complete regular second).property.1 divisor

noncomputable def divisorProjectiveChartCover (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).OpenCover where
  I₀ := Fin (Nat.card fan.cones)
  X chart := fan.affineToricChart 𝕜 (fan.divisorLocalCone 𝕜 complete regular chart)
  f chart := fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro point
    have contained : point ∈ ⨆ chart,
        (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange := by
      change point ∈ ⨆ chart,
        (fan.affineToricChartι 𝕜 regular ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).cone chart)).opensRange
      rw [(fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).covers.iSup_eq_top]
      trivial
    obtain ⟨chart, local_point, same⟩ := TopologicalSpace.Opens.mem_iSup.mp contained
    exact ⟨chart, local_point, same⟩

end TauCeti.Toric.Fan
