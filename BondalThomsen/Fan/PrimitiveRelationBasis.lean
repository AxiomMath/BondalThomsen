module

public import BondalThomsen.DeepFan.PrimitiveRelations
public import BondalThomsen.Fan.Completeness
public import BondalThomsen.Fan.RegularBasisCone

@[expose] public section

open Finset Set Module Classical

namespace TauCeti.Toric.Fan

section Algebraic

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem ray_eq_basis_of_mem_coneBasis (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (ray : fan.Ray)
    (contains : embedding ray.val ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    ∃ index, basis index = ray.val := by
  have ray_le : PointedCone.hull ℝ {embedding ray.val} ≤
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr contains)
  have face := fan.isFaceOf_of_le cone_basis ray.property.2 ray_le
  obtain ⟨index, same⟩ := TauCeti.Toric.primitive_eq_basis_of_ray_face fan.lattice
    basis ray.val ray.property.1 face (fan.isToricCone cone_basis).salient
  exact ⟨index, same.symm⟩

def PrimitiveLatticeRelation.DropOneConeIncidence
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (_relation : PrimitiveLatticeRelation fan left right) (distinguished : left) : Prop :=
  fan.finiteRayHull (left.erase distinguished.val ∪ right) ∈ fan.cones

theorem PrimitiveLatticeRelation.exists_coneBasisWitness_of_membership
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) (distinguished : left)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (left_contains : ∀ ray : {ray : left // ray ≠ distinguished},
      embedding ray.val.val.val ∈ PointedCone.hull ℝ
        (Set.range (fun index => embedding (basis index))))
    (right_contains : ∀ ray : right,
      embedding ray.val.val ∈ PointedCone.hull ℝ
        (Set.range (fun index => embedding (basis index)))) :
    Nonempty (PrimitiveRelationConeBasis relation distinguished dimension) := by
  let selected_ray : {ray : left // ray ≠ distinguished} ⊕ right → fan.Ray :=
    Sum.elim (fun ray => ray.val.val) (fun ray => ray.val)
  have selected_injective : Function.Injective selected_ray := by
    intro first second same
    cases first with
    | inl first =>
      cases second with
      | inl second =>
        exact congrArg Sum.inl (Subtype.ext (Subtype.ext same))
      | inr second =>
        have in_right : first.val.val ∈ right := by
          change first.val.val = second.val at same
          rw [same]
          exact second.property
        exact False.elim ((Finset.disjoint_left.mp relation.disjoint) first.val.property in_right)
    | inr first =>
      cases second with
      | inl second =>
        have in_right : second.val.val ∈ right := by
          change first.val = second.val.val at same
          rw [← same]
          exact first.property
        exact False.elim ((Finset.disjoint_left.mp relation.disjoint) second.val.property in_right)
      | inr second => exact congrArg Sum.inr (Subtype.ext same)
  have basis_exists : ∀ selected, ∃ index, basis index = (selected_ray selected).val := by
    intro selected
    apply fan.ray_eq_basis_of_mem_coneBasis basis cone_basis
    cases selected with
    | inl ray => exact left_contains ray
    | inr ray => exact right_contains ray
  let index := fun selected => (basis_exists selected).choose
  have basis_eq : ∀ selected, basis (index selected) = (selected_ray selected).val :=
    fun selected => (basis_exists selected).choose_spec
  have index_injective : Function.Injective index := by
    intro first second same
    apply selected_injective
    apply Subtype.ext
    rw [← basis_eq first, ← basis_eq second, same]
  exact ⟨⟨basis, cone_basis, ⟨index, index_injective⟩,
    fun ray => basis_eq (Sum.inl ray), fun ray => basis_eq (Sum.inr ray)⟩⟩

theorem PrimitiveRelationConeBasis.exists_rational_pairing
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    {relation : PrimitiveLatticeRelation fan left right} {distinguished : left}
    {dimension : ℕ} (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (left_values : {ray : left // ray ≠ distinguished} → ℚ) (right_values : right → ℚ) :
    ∃ pairing : Lattice →+ ℚ,
      (∀ ray : {ray : left // ray ≠ distinguished}, pairing ray.val.val.val = left_values ray) ∧
      (∀ ray : right, pairing ray.val.val = right_values ray) ∧
      pairing distinguished.val.val =
        (∑ ray : right, (relation.coefficients ray : ℚ) * right_values ray) -
          ∑ ray : {ray : left // ray ≠ distinguished}, left_values ray := by
  let values := Sum.elim left_values right_values
  let extended := Function.extend cone_basis.indices values (fun _ => (0 : ℚ))
  let pairing : Lattice →+ ℚ := (cone_basis.basis.constr ℚ extended).toAddMonoidHom
  have on_indices : ∀ selected, extended (cone_basis.indices selected) = values selected :=
    fun selected => congrFun (Function.extend_comp cone_basis.indices.injective values
      (fun _ => (0 : ℚ))) selected
  have on_left : ∀ ray : {ray : left // ray ≠ distinguished},
      pairing ray.val.val.val = left_values ray := by
    intro ray
    rw [← cone_basis.left_eq ray]
    change (cone_basis.basis.constr ℚ extended)
      (cone_basis.basis (cone_basis.indices (Sum.inl ray))) = left_values ray
    rw [Basis.constr_basis, on_indices]
    rfl
  have on_right : ∀ ray : right, pairing ray.val.val = right_values ray := by
    intro ray
    rw [← cone_basis.right_eq ray]
    change (cone_basis.basis.constr ℚ extended)
      (cone_basis.basis (cone_basis.indices (Sum.inr ray))) = right_values ray
    rw [Basis.constr_basis, on_indices]
    rfl
  refine ⟨pairing, on_left, on_right, ?_⟩
  rw [cone_basis.distinguished_eq, map_sub, map_sum, map_sum]
  simp only [← cone_basis.left_eq, ← cone_basis.right_eq] at on_left on_right
  simp only [map_zsmul, zsmul_eq_mul, on_left, on_right, Int.cast_natCast]

end Algebraic

section Complete

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem PrimitiveLatticeRelation.exists_coneBasisWitness_of_cone_incidence
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) (distinguished : left)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {dimension : ℕ}
    (reference : Basis (Fin dimension) ℤ Lattice)
    (cone : PointedCone ℝ Ambient) (cone_member : cone ∈ fan.cones)
    (left_contains : ∀ ray : {ray : left // ray ≠ distinguished}, embedding ray.val.val.val ∈ cone)
    (right_contains : ∀ ray : right, embedding ray.val.val ∈ cone) :
    Nonempty (PrimitiveRelationConeBasis relation distinguished dimension) := by
  obtain ⟨size, basis, cone_basis, above⟩ := fan.exists_coneBasis_above complete regular cone cone_member
  have size_eq : size = dimension := by
    have basis_rank := finrank_eq_card_basis basis
    have reference_rank := finrank_eq_card_basis reference
    simp only [Fintype.card_fin] at basis_rank reference_rank
    omega
  subst size
  exact relation.exists_coneBasisWitness_of_membership distinguished basis cone_basis
    (fun ray => above.le (left_contains ray)) (fun ray => above.le (right_contains ray))

theorem PrimitiveLatticeRelation.exists_coneBasisWitness_of_dropOneCone
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) (distinguished : left)
    (complete : fan.IsComplete) (regular : fan.IsRegular) {dimension : ℕ}
    (reference : Basis (Fin dimension) ℤ Lattice)
    (incidence : relation.DropOneConeIncidence distinguished) :
    Nonempty (PrimitiveRelationConeBasis relation distinguished dimension) := by
  apply relation.exists_coneBasisWitness_of_cone_incidence distinguished complete regular reference
    (fan.finiteRayHull (left.erase distinguished.val ∪ right)) incidence
  · intro ray
    apply PointedCone.subset_hull
    refine ⟨ray.val.val, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, ray.val.property⟩), rfl⟩
    intro same
    exact ray.property (Subtype.ext same)
  · intro ray
    exact PointedCone.subset_hull
      ⟨ray.val, Finset.mem_union_right _ ray.property, rfl⟩

end Complete

end TauCeti.Toric.Fan
