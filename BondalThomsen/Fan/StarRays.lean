module

public import BondalThomsen.Fan.StarFan

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in

theorem projected_basis_generator_isRay (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (ray : fan.Ray) (removed : Fin dimension) (equality : basis removed = ray.val)
    (index : {index : Fin dimension // index ≠ removed}) :
    TauCeti.IsPrimitive ((Submodule.span ℤ {ray.val}).mkQ (basis index.val)) ∧
      PointedCone.hull ℝ {fan.starProjection ray (embedding (basis index.val))} ∈
        (fan.star ray).cones := by
  let quotient_basis := basisVectorQuotient basis removed ray.val equality
  have primitive : TauCeti.IsPrimitive (quotient_basis index) := quotient_basis.isPrimitive index
  have contains : embedding ray.val ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) := by
    rw [← equality]
    exact PointedCone.subset_hull ⟨removed, rfl⟩
  have cone_member : PointedCone.hull ℝ (Set.range (fun index =>
      fan.starEmbedding ray (quotient_basis index))) ∈ (fan.star ray).cones := by
    rw [← fan.starConeBasis_eq_hull basis ray removed equality]
    exact ⟨_, ⟨cone_basis, contains⟩, rfl⟩
  have independent : LinearIndependent ℝ (fun index =>
      fan.starEmbedding ray (quotient_basis index)) := by
    convert ((fan.star ray).lattice.isBaseChange.basis quotient_basis).linearIndependent using 1
    funext index
    exact ((fan.star ray).lattice.isBaseChange.basis_apply quotient_basis index).symm
  have face := PointedCone.isFaceOf_hull_image independent rfl {index}
  have ray_member := (fan.star ray).mem_of_isFaceOf cone_member face
  refine ⟨?_, ?_⟩
  · simpa only [quotient_basis, basisVectorQuotient_apply] using primitive
  · simpa only [Set.image_singleton, quotient_basis, basisVectorQuotient_apply,
      starEmbedding_mkQ] using ray_member

theorem projected_ray_eq_basis (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (ray other : fan.Ray)
    (nonzero : (Submodule.span ℤ {ray.val}).mkQ other.val ≠ 0) :
    ∃ basis : Basis (Fin dimension) ℤ Lattice, fan.IsConeBasis basis ∧
      ∃ removed : Fin dimension, basis removed = ray.val ∧
        ∃ chosen : Fin dimension, chosen ≠ removed ∧
          (Submodule.span ℤ {ray.val}).mkQ other.val =
            (Submodule.span ℤ {ray.val}).mkQ (basis chosen) := by
  obtain ⟨basis, cone_basis, removed, equality, scalar, positive, contains⟩ :=
    fan.exists_coneBasis_ray_perturbation complete regular deep reference ray (embedding other.val)
  let real_basis := fan.lattice.isBaseChange.basis basis
  have real_range : Set.range (fun index => embedding (basis index)) = Set.range real_basis := by
    apply congrArg Set.range
    funext index
    exact (fan.lattice.isBaseChange.basis_apply basis index).symm
  have coordinates_nonnegative : ∀ index,
      0 ≤ real_basis.repr (embedding ray.val + scalar • embedding other.val) index := by
    apply (mem_basisCone_iff real_basis _).mp
    rwa [← real_range]
  have nonnegative : ∀ index, index ≠ removed → 0 ≤ basis.repr other.val index := by
    intro index distinct
    have bound := coordinates_nonnegative index
    rw [← equality] at bound
    change 0 ≤ real_basis.repr
      (embedding.toIntLinearMap (basis removed) + scalar • embedding.toIntLinearMap other.val)
        index at bound
    rw [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
      fan.lattice.isBaseChange.basis_repr_comp_apply,
      fan.lattice.isBaseChange.basis_repr_comp_apply] at bound
    simp only [Basis.repr_self_apply, Ne.symm distinct,
      ite_false, map_zero, zero_add] at bound
    have real_bound : 0 ≤ (basis.repr other.val index : ℝ) :=
      (mul_nonneg_iff_of_pos_left positive).mp bound
    exact_mod_cast real_bound
  have killed : (Submodule.span ℤ {ray.val}).mkQ (basis removed) = 0 := by
    rw [equality, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨chosen, distinct, projected_eq⟩ := projected_deep_vector_eq_basis basis removed
    (Submodule.span ℤ {ray.val}).mkQ killed other.val (deep basis cone_basis other)
      nonnegative nonzero
  exact ⟨basis, cone_basis, removed, equality, chosen, distinct, projected_eq⟩

theorem projected_ray_isRay (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (ray other : fan.Ray)
    (nonzero : (Submodule.span ℤ {ray.val}).mkQ other.val ≠ 0) :
    TauCeti.IsPrimitive ((Submodule.span ℤ {ray.val}).mkQ other.val) ∧
      PointedCone.hull ℝ {(fan.starEmbedding ray
        ((Submodule.span ℤ {ray.val}).mkQ other.val))} ∈ (fan.star ray).cones := by
  obtain ⟨basis, cone_basis, removed, equality, chosen, distinct, projected_eq⟩ :=
    fan.projected_ray_eq_basis complete regular deep reference ray other nonzero
  rw [projected_eq]
  simpa only [starEmbedding_mkQ] using
    fan.projected_basis_generator_isRay basis cone_basis ray removed equality ⟨chosen, distinct⟩

theorem starRay_eq_projected_ray (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (ray : fan.Ray)
    (other : (fan.star ray).Ray) :
    ∃ source : fan.Ray, other.val = (Submodule.span ℤ {ray.val}).mkQ source.val := by
  obtain ⟨original, ⟨original_member, contains⟩, projected_eq⟩ := other.property.2
  obtain ⟨size, basis, cone_basis, removed, equality, original_face⟩ :=
    fan.exists_coneBasis_above_containing_ray complete regular ray original original_member contains
  let quotient_basis := basisVectorQuotient basis removed ray.val equality
  have ray_face : (PointedCone.hull ℝ {fan.starEmbedding ray other.val}).IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => fan.starEmbedding ray
        (quotient_basis index)))) := by
    rw [← fan.starConeBasis_eq_hull basis ray removed equality]
    have descends := rayQuotient_map_isFaceOf _ original_face contains
    change (PointedCone.map (fan.starProjection ray) original).IsFaceOf
      (PointedCone.map (fan.starProjection ray) _) at descends
    rw [projected_eq] at descends
    exact descends
  have toric := fan.starConeBasis_isRegular basis ray removed equality cone_basis
  rw [fan.starConeBasis_eq_hull basis ray removed equality] at toric
  obtain ⟨index, vector_eq⟩ := TauCeti.Toric.primitive_eq_basis_of_ray_face
    (fan.star ray).lattice quotient_basis other.val other.property.1 ray_face toric.salient
  exact ⟨fan.basisRay basis cone_basis index.val,
    vector_eq.trans (basisVectorQuotient_apply basis removed ray.val equality index)⟩

theorem starRay_deep_in_quotientBasis (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (ray : fan.Ray) (removed : Fin dimension)
    (equality : basis removed = ray.val) (other : (fan.star ray).Ray) :
    DeepCoordinates (fun index =>
      (basisVectorQuotient basis removed ray.val equality).repr other.val index) := by
  obtain ⟨source, source_eq⟩ := fan.starRay_eq_projected_ray complete regular ray other
  rw [source_eq]
  simp only [basisVectorQuotient_repr]
  exact (deep basis cone_basis source).comp Subtype.val Subtype.val_injective

end TauCeti.Toric.Fan
