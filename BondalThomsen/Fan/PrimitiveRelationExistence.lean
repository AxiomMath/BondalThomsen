module

public import BondalThomsen.Fan.PrimitiveRelationBasis
public import BondalThomsen.Fan.ConeCoordinates

@[expose] public section

open Finset Set Module Classical

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in

theorem coneBasis_repr_nonnegative (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (vector : Lattice)
    (contains : embedding vector ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    ∀ index, 0 ≤ basis.repr vector index := by
  let real_basis := fan.lattice.isBaseChange.basis basis
  have real_basis_eq : (fun index => embedding (basis index)) = real_basis := by
    funext index
    exact (fan.lattice.isBaseChange.basis_apply basis index).symm
  have real_contains : embedding vector ∈ PointedCone.hull ℝ (Set.range real_basis) := by
    rwa [real_basis_eq] at contains
  intro index
  have nonnegative := (BondalThomsen.mem_basisCone_iff real_basis (embedding vector)).mp real_contains index
  change 0 ≤ real_basis.repr (embedding.toIntLinearMap vector) index at nonnegative
  rw [fan.lattice.isBaseChange.basis_repr_comp_apply] at nonnegative
  change 0 ≤ (basis.repr vector index : ℝ) at nonnegative
  exact_mod_cast nonnegative

omit [FiniteDimensional ℝ Ambient] in

theorem mem_coneBasis_of_repr_nonnegative (_fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (vector : Lattice)
    (nonnegative : ∀ index, 0 ≤ basis.repr vector index) :
    embedding vector ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index))) := by
  rw [← basis.sum_repr vector, map_sum]
  apply Submodule.sum_mem
  intro index _member
  rw [map_zsmul]
  rw [← Int.cast_smul_eq_zsmul ℝ]
  change (basis.repr vector index : ℝ) • embedding (basis index) ∈
    PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))
  exact PointedCone.smul_mem _ (by exact_mod_cast nonnegative index)
    (PointedCone.subset_hull ⟨index, rfl⟩)

omit [FiniteDimensional ℝ Ambient] in

theorem finiteRayHull_mem_of_basis_generators (fan : TauCeti.Toric.Fan embedding)
    (regular : fan.IsRegular) {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (rays : Finset fan.Ray)
    (generators : ∀ ray ∈ rays, ∃ index, basis index = ray.val) :
    fan.finiteRayHull rays ∈ fan.cones := by
  let all_rays := Finset.univ.image (fan.basisRay basis cone_basis)
  have all_hull : fan.finiteRayHull all_rays =
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) := by
    change PointedCone.hull ℝ
      ((fun ray : fan.Ray => embedding ray.val) '' (all_rays : Set fan.Ray)) = _
    congr 1
    ext vector
    simp [all_rays]
  have contained : rays ⊆ all_rays := by
    intro ray member
    obtain ⟨index, same⟩ := generators ray member
    exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, Subtype.ext same⟩
  apply fan.finiteRayHull_mem_of_subset regular (all_hull.symm ▸ cone_basis) contained

omit [FiniteDimensional ℝ Ambient] in

theorem IsPrimitiveCollection.basisRay_sum_coordinate_nonpositive
    {fan : TauCeti.Toric.Fan embedding} {left : Finset fan.Ray}
    (primitive : fan.IsPrimitiveCollection left) (regular : fan.IsRegular)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (nonnegative : ∀ index, 0 ≤ basis.repr (∑ ray : left, ray.val.val) index)
    (chosen : left) (chosen_index : Fin dimension) (chosen_eq : basis chosen_index = chosen.val.val) :
    basis.repr (∑ ray : left, ray.val.val) chosen_index ≤ 0 := by
  by_contra contrary
  have positive : 0 < basis.repr (∑ ray : left, ray.val.val) chosen_index := by omega
  let remaining : Lattice := ∑ ray : {ray : left // ray ≠ chosen}, ray.val.val.val
  have remaining_eq : remaining = (∑ ray : left, ray.val.val) - chosen.val.val := by
    have split := Fintype.sum_eq_add_sum_subtype_ne (fun ray : left => ray.val.val) chosen
    exact eq_sub_iff_add_eq.mpr ((add_comm remaining chosen.val.val).trans split.symm)
  have remaining_nonnegative : ∀ index, 0 ≤ basis.repr remaining index := by
    intro index
    rw [remaining_eq, map_sub, Finsupp.sub_apply, ← chosen_eq, Basis.repr_self_apply]
    split_ifs with same
    · subst index
      omega
    · simpa using nonnegative index
  let cone := PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))
  let other_rays := left.erase chosen.val
  have other_member : fan.finiteRayHull other_rays ∈ fan.cones :=
    primitive.proper_subset_hull_mem (Finset.erase_ssubset chosen.property)
  have remaining_in_other : embedding remaining ∈ fan.finiteRayHull other_rays := by
    dsimp [remaining]
    rw [map_sum]
    apply Submodule.sum_mem
    intro ray _member
    apply PointedCone.subset_hull
    refine ⟨ray.val.val, Finset.mem_erase.mpr ⟨?_, ray.val.property⟩, rfl⟩
    intro same
    exact ray.property (Subtype.ext same)
  have remaining_in_cone : embedding remaining ∈ cone :=
    fan.mem_coneBasis_of_repr_nonnegative basis remaining remaining_nonnegative
  have intersection_face := fan.inf_isFaceOf_left other_member cone_basis
  have each_in_other : ∀ ray : {ray : left // ray ≠ chosen},
      embedding ray.val.val.val ∈ fan.finiteRayHull other_rays := by
    intro ray
    apply PointedCone.subset_hull
    refine ⟨ray.val.val, Finset.mem_erase.mpr ⟨?_, ray.val.property⟩, rfl⟩
    intro same
    exact ray.property (Subtype.ext same)
  have sum_in_intersection :
      ∑ ray : {ray : left // ray ≠ chosen}, embedding ray.val.val.val ∈
        fan.finiteRayHull other_rays ⊓ cone := by
    rw [← map_sum]
    exact ⟨remaining_in_other, remaining_in_cone⟩
  have all_generators : ∀ ray ∈ left, ∃ index, basis index = ray.val := by
    intro ray member
    by_cases same : ray = chosen.val
    · subst ray
      exact ⟨chosen_index, chosen_eq⟩
    · let other : {ray : left // ray ≠ chosen} :=
        ⟨⟨ray, member⟩, fun same_subtype => same (congrArg Subtype.val same_subtype)⟩
      have contains := (intersection_face.mem_of_sum_mem each_in_other sum_in_intersection other).2
      exact fan.ray_eq_basis_of_mem_coneBasis basis cone_basis ray contains
  exact primitive.2.1 (fan.finiteRayHull_mem_of_basis_generators regular basis cone_basis left all_generators)

theorem IsPrimitiveCollection.exists_primitiveLatticeRelation
    {fan : TauCeti.Toric.Fan embedding} {left : Finset fan.Ray}
    (primitive : fan.IsPrimitiveCollection left) (complete : fan.IsComplete)
    (regular : fan.IsRegular) :
    ∃ right : Finset fan.Ray, Nonempty (PrimitiveLatticeRelation fan left right) := by
  let vector : Lattice := ∑ ray : left, ray.val.val
  obtain ⟨dimension, basis, cone_basis, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (embedding vector)
  have nonnegative := fan.coneBasis_repr_nonnegative basis vector contains
  let support : Finset (Fin dimension) := Finset.univ.filter (fun index => 0 < basis.repr vector index)
  let right := support.image (fan.basisRay basis cone_basis)
  have basisRay_injective : Function.Injective (fan.basisRay basis cone_basis) := by
    intro first second same
    exact basis.injective (congrArg Subtype.val same)
  have indices_exists : ∀ ray : right, ∃ index : support,
      fan.basisRay basis cone_basis index.val = ray.val := by
    intro ray
    obtain ⟨index, member, same⟩ := Finset.mem_image.mp ray.property
    exact ⟨⟨index, member⟩, same⟩
  let index_of : right → support := fun ray => (indices_exists ray).choose
  have index_eq : ∀ ray : right, fan.basisRay basis cone_basis (index_of ray).val = ray.val :=
    fun ray => (indices_exists ray).choose_spec
  let coefficients : right → ℕ := fun ray => (basis.repr vector (index_of ray).val).toNat
  have positive_coefficients : ∀ ray, 0 < coefficients ray := by
    intro ray
    have positive := (Finset.mem_filter.mp (index_of ray).property).2
    dsimp [coefficients]
    omega
  have right_cone : fan.finiteRayHull right ∈ fan.cones := by
    apply fan.finiteRayHull_mem_of_basis_generators regular basis cone_basis right
    intro ray member
    obtain ⟨index, _index_member, same⟩ := Finset.mem_image.mp member
    exact ⟨index, congrArg Subtype.val same⟩
  have disjoint : Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro ray left_member right_member
    obtain ⟨index, index_member, same⟩ := Finset.mem_image.mp right_member
    have basis_eq : basis index = ray.val := congrArg Subtype.val same
    have nonpositive := primitive.basisRay_sum_coordinate_nonpositive regular basis cone_basis
      nonnegative ⟨ray, left_member⟩ index basis_eq
    change basis.repr vector index ≤ 0 at nonpositive
    have positive := (Finset.mem_filter.mp index_member).2
    omega
  let support_to_right : support → right := fun index =>
    ⟨fan.basisRay basis cone_basis index.val, Finset.mem_image.mpr ⟨index.val, index.property, rfl⟩⟩
  have support_bijective : Function.Bijective support_to_right := by
    constructor
    · intro first second same
      apply Subtype.ext
      exact basisRay_injective (congrArg Subtype.val same)
    · intro ray
      exact ⟨index_of ray, Subtype.ext (index_eq ray)⟩
  let equivalence : support ≃ right := Equiv.ofBijective support_to_right support_bijective
  have inverse_index : ∀ index : support, index_of (equivalence index) = index := by
    intro index
    apply Subtype.ext
    apply basisRay_injective
    exact index_eq (equivalence index)
  have lattice_eq : vector = ∑ ray : right, (coefficients ray : ℤ) • ray.val.val := by
    rw [← equivalence.sum_comp (fun ray : right => (coefficients ray : ℤ) • ray.val.val)]
    have term_eq : ∀ index : support,
        (coefficients (equivalence index) : ℤ) • (equivalence index).val.val =
          basis.repr vector index.val • basis index.val := by
      intro index
      change (((basis.repr vector (index_of (equivalence index)).val).toNat : ℤ) •
        basis index.val) = _
      rw [inverse_index]
      rw [Int.toNat_of_nonneg (nonnegative index.val)]
    simp_rw [term_eq]
    rw [← Finset.sum_subtype support (fun index => Iff.rfl)
      (fun index => basis.repr vector index • basis index)]
    rw [Finset.sum_filter]
    calc
      vector = ∑ index, basis.repr vector index • basis index := (basis.sum_repr vector).symm
      _ = ∑ index, if 0 < basis.repr vector index then
          basis.repr vector index • basis index else 0 := by
        apply Finset.sum_congr rfl
        intro index _member
        split_ifs with positive
        · rfl
        · have zero : basis.repr vector index = 0 := by
            have lower := nonnegative index
            omega
          simp [zero]
  exact ⟨right, ⟨⟨primitive, disjoint, coefficients, positive_coefficients, right_cone, lattice_eq⟩⟩⟩

end TauCeti.Toric.Fan
