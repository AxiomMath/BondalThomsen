module

public import BondalThomsen.Toric.Positivity.ActualAmpleStrictSupportCriterion
public import BondalThomsen.Fan.PrimitiveRelationExistence
public import BondalThomsen.Fan.Interior

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module Set Finset
open scoped Classical

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

def rayVertexSum (fan : Fan embedding) : Lattice :=
  letI := Fintype.ofFinite fan.Ray
  ∑ ray : fan.Ray, ray.val

def IsSpecialConeBasis (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) : Prop :=
  fan.IsConeBasis basis ∧ ∀ index, 0 ≤ basis.repr fan.rayVertexSum index

theorem exists_specialConeBasis (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {dimension : ℕ} (reference : Basis (Fin dimension) ℤ Lattice) :
    ∃ basis : Basis (Fin dimension) ℤ Lattice, fan.IsSpecialConeBasis basis := by
  obtain ⟨size, basis, coneBasis, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (embedding fan.rayVertexSum)
  have sizeEquality : size = dimension := by
    have referenceRank := finrank_eq_card_basis reference
    have basisRank := finrank_eq_card_basis basis
    simp only [Fintype.card_fin] at referenceRank basisRank
    omega
  subst size
  exact ⟨basis, coneBasis, fan.coneBasis_repr_nonnegative basis fan.rayVertexSum contains⟩

omit [FiniteDimensional ℝ Ambient] in
theorem rayHeight_nonpositive_of_strictSupport_nongenerator
    (fan : Fan embedding) (strict : fan.HasStrictAnticanonicalConeSupport)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (ray : fan.Ray)
    (outside : ray.val ∉ Set.range basis) : basis.sumCoords ray.val ≤ 0 := by
  have inequality := strict dimension basis coneBasis ray outside
  change -1 < -basis.sumCoords ray.val at inequality
  omega

omit [FiniteDimensional ℝ Ambient] in
theorem rayHeight_le_one_of_strictSupport
    (fan : Fan embedding) (strict : fan.HasStrictAnticanonicalConeSupport)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (ray : fan.Ray) :
    basis.sumCoords ray.val ≤ 1 := by
  by_cases member : ray.val ∈ Set.range basis
  · obtain ⟨index, equality⟩ := member
    rw [← equality, basis.sumCoords_self_apply]
  · exact (fan.rayHeight_nonpositive_of_strictSupport_nongenerator
      strict basis coneBasis ray member).trans (by norm_num)

omit [FiniteDimensional ℝ Ambient] in
theorem rayHeight_eq_one_iff_of_strictSupport
    (fan : Fan embedding) (strict : fan.HasStrictAnticanonicalConeSupport)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (ray : fan.Ray) :
    basis.sumCoords ray.val = 1 ↔ ray.val ∈ Set.range basis := by
  constructor
  · intro equality
    by_contra outside
    have bounded := fan.rayHeight_nonpositive_of_strictSupport_nongenerator
      strict basis coneBasis ray outside
    omega
  · rintro ⟨index, equality⟩
    rw [← equality, basis.sumCoords_self_apply]

def coneBasisRayFinset (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis) : Finset fan.Ray :=
  Finset.univ.image (fan.basisRay basis coneBasis)

omit [FiniteDimensional ℝ Ambient] in
theorem mem_coneBasisRayFinset_iff (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis) (ray : fan.Ray) :
    ray ∈ fan.coneBasisRayFinset basis coneBasis ↔ ray.val ∈ Set.range basis := by
  classical
  change ray ∈ Finset.univ.image (fan.basisRay basis coneBasis) ↔ ray.val ∈ Set.range basis
  constructor
  · intro member
    obtain ⟨index, _, equality⟩ := Finset.mem_image.mp member
    exact ⟨index, congrArg Subtype.val equality⟩
  · rintro ⟨index, equality⟩
    exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, Subtype.ext equality⟩

omit [FiniteDimensional ℝ Ambient] in
theorem coneBasisRayFinset_height_sum (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (coneBasis : fan.IsConeBasis basis) :
    ∑ ray ∈ fan.coneBasisRayFinset basis coneBasis, basis.sumCoords ray.val = dimension := by
  rw [coneBasisRayFinset, Finset.sum_image]
  · simp only [basisRay_val, basis.sumCoords_self_apply, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · intro first _ second _ equality
    exact basis.injective (congrArg Subtype.val equality)

omit [FiniteDimensional ℝ Ambient] in
theorem specialConeBasis_total_height_nonnegative (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (special : fan.IsSpecialConeBasis basis) :
    0 ≤ basis.sumCoords fan.rayVertexSum := by
  have coordinates : basis.sumCoords fan.rayVertexSum =
      ∑ index, basis.repr fan.rayVertexSum index := by
    simp [Basis.sumCoords, Finsupp.sum_fintype]
  rw [coordinates]
  exact Finset.sum_nonneg fun index _ => special.2 index

omit [FiniteDimensional ℝ Ambient] in
theorem specialConeBasis_negative_height_budget
    (fan : Fan embedding) (strict : fan.HasStrictAnticanonicalConeSupport)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (special : fan.IsSpecialConeBasis basis) :
    letI := Fintype.ofFinite fan.Ray
    ∑ ray : fan.Ray, min (basis.sumCoords ray.val) 0 ≥ -(dimension : ℤ) := by
  let := Fintype.ofFinite fan.Ray
  let basisRays := fan.coneBasisRayFinset basis special.1
  have subset : basisRays ⊆ (Finset.univ : Finset fan.Ray) := subset_univ _
  have basisHeight : ∑ ray ∈ basisRays, basis.sumCoords ray.val = dimension :=
    fan.coneBasisRayFinset_height_sum basis special.1
  have totalNonnegative : 0 ≤ ∑ ray : fan.Ray, basis.sumCoords ray.val := by
    simpa only [rayVertexSum, map_sum] using
      fan.specialConeBasis_total_height_nonnegative basis special
  have outsideNonpositive : ∀ ray ∈ Finset.univ \ basisRays, basis.sumCoords ray.val ≤ 0 := by
    intro ray member
    apply fan.rayHeight_nonpositive_of_strictSupport_nongenerator strict basis special.1 ray
    exact fun inRange => (mem_sdiff.mp member).2
      ((fan.mem_coneBasisRayFinset_iff basis special.1 ray).mpr inRange)
  have negativeSum : ∑ ray : fan.Ray, min (basis.sumCoords ray.val) 0 =
      ∑ ray ∈ Finset.univ \ basisRays, basis.sumCoords ray.val := by
    rw [← Finset.sum_sdiff subset]
    have basisZero : ∑ ray ∈ basisRays, min (basis.sumCoords ray.val) 0 = 0 := by
      apply Finset.sum_eq_zero
      intro ray member
      obtain ⟨index, equality⟩ :=
        (fan.mem_coneBasisRayFinset_iff basis special.1 ray).mp member
      simp [← equality]
    rw [basisZero, add_zero]
    apply Finset.sum_congr rfl
    intro ray member
    exact min_eq_left (outsideNonpositive ray member)
  rw [negativeSum]
  have partition := Finset.sum_sdiff subset (f := fun ray => basis.sumCoords ray.val)
  omega

omit [FiniteDimensional ℝ Ambient] in
theorem specialConeBasis_rayHeight_bounds
    (fan : Fan embedding) (strict : fan.HasStrictAnticanonicalConeSupport)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (special : fan.IsSpecialConeBasis basis) (ray : fan.Ray) :
    -(dimension : ℤ) ≤ basis.sumCoords ray.val ∧ basis.sumCoords ray.val ≤ 1 := by
  let := Fintype.ofFinite fan.Ray
  have budget := fan.specialConeBasis_negative_height_budget strict basis special
  have sumBelow : ∑ other : fan.Ray, min (basis.sumCoords other.val) 0 ≤
      min (basis.sumCoords ray.val) 0 := by
    simpa only [Finset.sum_singleton] using
      (Finset.sum_le_sum_of_subset_of_nonpos
        (f := fun other : fan.Ray => min (basis.sumCoords other.val) (0 : ℤ))
        (show ({ray} : Finset fan.Ray) ⊆ Finset.univ from singleton_subset_iff.mpr (mem_univ ray))
        fun other _ _ => min_le_right _ _)
  exact ⟨budget.trans (sumBelow.trans (min_le_left _ _)),
    fan.rayHeight_le_one_of_strictSupport strict basis special.1 ray⟩

end TauCeti.Toric.Fan
