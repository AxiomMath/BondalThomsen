module

public import BondalThomsen.Fan.PrimitiveRelationExistence
public import BondalThomsen.Toric.Divisor.DivisorArithmetic

@[expose] public section

open Finset Module

namespace TauCeti.Toric.Fan

section CoefficientIntersection

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def PrimitiveLatticeRelation.divisorIntersection
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) (divisor : fan.InvariantRayDivisor) : ℤ :=
  (∑ ray : left, divisor ray.val) -
    ∑ ray : right, (relation.coefficients ray : ℤ) * divisor ray.val

end CoefficientIntersection

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def badCoordinateZeroRays (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (bad_ray : fan.Ray) : Finset fan.Ray := by
  classical
  exact (univ.filter fun index => basis.repr bad_ray.val index ≤ 0).image
    (fan.basisRay basis cone_basis)

noncomputable def badCoordinateDivisor (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (bad_ray : fan.Ray) :
    fan.InvariantRayDivisor := by
  classical
  exact fan.invariantDivisorOfCoefficients fun ray =>
    if ray ∈ fan.badCoordinateZeroRays basis cone_basis bad_ray then 0 else 1

theorem badCoordinateDivisor_coefficients (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (bad_ray ray : fan.Ray) :
    0 ≤ fan.badCoordinateDivisor basis cone_basis bad_ray ray ∧
      fan.badCoordinateDivisor basis cone_basis bad_ray ray ≤ 1 := by
  classical
  simp only [badCoordinateDivisor, invariantDivisorOfCoefficients_apply]
  split_ifs <;> omega

theorem mem_badCoordinateZeroRays_iff (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (bad_ray ray : fan.Ray) :
    ray ∈ fan.badCoordinateZeroRays basis cone_basis bad_ray ↔
      ∃ index, basis.repr bad_ray.val index ≤ 0 ∧ basis index = ray.val := by
  classical
  simp only [badCoordinateZeroRays, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨index, nonpositive, same⟩
    exact ⟨index, nonpositive, congrArg Subtype.val same⟩
  · rintro ⟨index, nonpositive, same⟩
    exact ⟨index, nonpositive, Subtype.ext same⟩

theorem badCoordinateDivisor_basisRay (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (bad_ray : fan.Ray) (index : Fin dimension) :
    fan.badCoordinateDivisor basis cone_basis bad_ray (fan.basisRay basis cone_basis index) =
      if 0 < basis.repr bad_ray.val index then 1 else 0 := by
  classical
  have member : fan.basisRay basis cone_basis index ∈
      fan.badCoordinateZeroRays basis cone_basis bad_ray ↔
      basis.repr bad_ray.val index ≤ 0 := by
    rw [fan.mem_badCoordinateZeroRays_iff]
    simp only [basisRay_val, basis.injective.eq_iff]
    simp
  simp only [badCoordinateDivisor, invariantDivisorOfCoefficients_apply, member]
  split_ifs <;> omega

noncomputable def coneDivisorCharacter (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor) :
    Lattice →+ ℤ :=
  (basis.constr ℤ (fun index => -divisor (fan.basisRay basis cone_basis index))).toAddMonoidHom

@[simp] theorem coneDivisorCharacter_basis (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor)
    (index : Fin dimension) :
    fan.coneDivisorCharacter basis cone_basis divisor (basis index) =
      -divisor (fan.basisRay basis cone_basis index) := by
  exact basis.constr_basis ℤ _ index

theorem badCoordinateDivisor_character_value (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (bad_ray : fan.Ray) :
    fan.coneDivisorCharacter basis cone_basis
        (fan.badCoordinateDivisor basis cone_basis bad_ray) bad_ray.val =
      -(∑ index, max (basis.repr bad_ray.val index) 0) := by
  classical
  change (basis.constr ℤ _ : Lattice →ₗ[ℤ] ℤ) bad_ray.val = _
  rw [Basis.constr_apply_fintype, ← sum_neg_distrib]
  apply sum_congr rfl
  intro index _
  rw [fan.badCoordinateDivisor_basisRay]
  change basis.repr bad_ray.val index *
      -(if 0 < basis.repr bad_ray.val index then 1 else 0) =
    -max (basis.repr bad_ray.val index) 0
  split_ifs with positive
  · rw [max_eq_left positive.le]
    ring
  · rw [max_eq_right (by omega)]
    ring

theorem badCoordinateDivisor_badRay (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (bad_ray : fan.Ray) :
    fan.badCoordinateDivisor basis cone_basis bad_ray bad_ray = 1 := by
  classical
  have outside : bad_ray ∉ fan.badCoordinateZeroRays basis cone_basis bad_ray := by
    intro member
    obtain ⟨index, nonpositive, same⟩ :=
      (fan.mem_badCoordinateZeroRays_iff basis cone_basis bad_ray bad_ray).mp member
    have coordinate : basis.repr bad_ray.val index = 1 := by
      rw [← same]
      simp
    omega
  simp [badCoordinateDivisor, outside]

theorem badCoordinateDivisor_violates_support (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (bad_ray : fan.Ray)
    (nondeep : ¬ BondalThomsen.DeepCoordinates (fun index => basis.repr bad_ray.val index)) :
    fan.coneDivisorCharacter basis cone_basis
        (fan.badCoordinateDivisor basis cone_basis bad_ray) bad_ray.val <
      -fan.badCoordinateDivisor basis cone_basis bad_ray bad_ray := by
  rw [fan.badCoordinateDivisor_character_value,
    fan.badCoordinateDivisor_badRay basis cone_basis bad_ray]
  change ¬ (∑ index, max (basis.repr bad_ray.val index) 0) ≤ 1 at nondeep
  omega

theorem primitiveCollection_meets_badCoordinateDivisor (fan : TauCeti.Toric.Fan embedding)
    (regular : fan.IsRegular) {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (bad_ray : fan.Ray) {left : Finset fan.Ray}
    (primitive : fan.IsPrimitiveCollection left) :
    ∃ ray : left, fan.badCoordinateDivisor basis cone_basis bad_ray ray.val = 1 := by
  classical
  by_contra no_witness
  apply primitive.2.1
  apply fan.finiteRayHull_mem_of_basis_generators regular basis cone_basis left
  intro ray member
  have zero_member : ray ∈ fan.badCoordinateZeroRays basis cone_basis bad_ray := by
    by_contra outside
    apply no_witness
    exact ⟨⟨ray, member⟩, by simp [badCoordinateDivisor, outside]⟩
  obtain ⟨index, _, same⟩ :=
    (fan.mem_badCoordinateZeroRays_iff basis cone_basis bad_ray ray).mp zero_member
  exact ⟨index, same⟩

theorem primitiveCollection_badCoordinateDivisor_sum_ge_one
    (fan : TauCeti.Toric.Fan embedding) (regular : fan.IsRegular) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (bad_ray : fan.Ray) {left : Finset fan.Ray} (primitive : fan.IsPrimitiveCollection left) :
    1 ≤ ∑ ray : left, fan.badCoordinateDivisor basis cone_basis bad_ray ray.val := by
  obtain ⟨chosen, coefficient⟩ :=
    fan.primitiveCollection_meets_badCoordinateDivisor regular basis cone_basis bad_ray primitive
  rw [← coefficient]
  exact single_le_sum (fun ray _ =>
    (fan.badCoordinateDivisor_coefficients basis cone_basis bad_ray ray.val).1) (mem_univ chosen)

theorem PrimitiveLatticeRelation.coefficient_sum_ge_two_of_badCoordinateDivisor_negative
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) (regular : fan.IsRegular)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (bad_ray : fan.Ray)
    (negative : relation.divisorIntersection
      (fan.badCoordinateDivisor basis cone_basis bad_ray) < 0) :
    2 ≤ ∑ ray : right, relation.coefficients ray := by
  have left_bound := fan.primitiveCollection_badCoordinateDivisor_sum_ge_one
    regular basis cone_basis bad_ray relation.primitive_collection
  have right_bound :
      (∑ ray : right, (relation.coefficients ray : ℤ) *
        fan.badCoordinateDivisor basis cone_basis bad_ray ray.val) ≤
      ∑ ray : right, (relation.coefficients ray : ℤ) := by
    apply sum_le_sum
    intro ray _
    have bounded := (fan.badCoordinateDivisor_coefficients basis cone_basis bad_ray ray.val).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left bounded
      (show (0 : ℤ) ≤ relation.coefficients ray by positivity)
  have total_bound : (2 : ℤ) ≤ ∑ ray : right, (relation.coefficients ray : ℤ) := by
    unfold PrimitiveLatticeRelation.divisorIntersection at negative
    omega
  exact_mod_cast total_bound

end TauCeti.Toric.Fan

namespace BondalThomsen

open TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

def ToricNefSupportCriterion (fan : TauCeti.Toric.Fan embedding) (dimension : ℕ)
    (nef : fan.InvariantRayDivisor → Prop) : Prop :=
  ∀ divisor, nef divisor → ∀ basis : Basis (Fin dimension) ℤ Lattice,
    ∀ cone_basis : fan.IsConeBasis basis, ∀ ray : fan.Ray,
      -divisor ray ≤ fan.coneDivisorCharacter basis cone_basis divisor ray.val

def ExtremalPrimitiveNegativeWitness (fan : TauCeti.Toric.Fan embedding)
    (nef : fan.InvariantRayDivisor → Prop)
    (extremal : ∀ left right : Finset fan.Ray, PrimitiveLatticeRelation fan left right → Prop) :
    Prop :=
  ∀ divisor, ¬ nef divisor → ∃ left right : Finset fan.Ray,
    ∃ relation : PrimitiveLatticeRelation fan left right,
      extremal left right relation ∧ relation.divisorIntersection divisor < 0

theorem proposition_4_1_ii_implies_i (fan : TauCeti.Toric.Fan embedding)
    (regular : fan.IsRegular) (dimension : ℕ) (nef : fan.InvariantRayDivisor → Prop)
    (extremal : ∀ left right : Finset fan.Ray, PrimitiveLatticeRelation fan left right → Prop)
    (support_criterion : ToricNefSupportCriterion fan dimension nef)
    (negative_witness : ExtremalPrimitiveNegativeWitness fan nef extremal)
    (small_extremal : ∀ left right (relation : PrimitiveLatticeRelation fan left right),
      extremal left right relation → ∑ ray : right, relation.coefficients ray ≤ 1) :
    fan.IsDeep dimension := by
  intro basis cone_basis ray
  by_contra nondeep
  have nonnef : ¬ nef (fan.badCoordinateDivisor basis cone_basis ray) := by
    intro is_nef
    exact not_le_of_gt (fan.badCoordinateDivisor_violates_support basis cone_basis ray nondeep)
      (support_criterion _ is_nef basis cone_basis ray)
  obtain ⟨left, right, relation, is_extremal, negative⟩ := negative_witness _ nonnef
  have large := relation.coefficient_sum_ge_two_of_badCoordinateDivisor_negative
    regular basis cone_basis ray negative
  have small := small_extremal left right relation is_extremal
  omega

end BondalThomsen
