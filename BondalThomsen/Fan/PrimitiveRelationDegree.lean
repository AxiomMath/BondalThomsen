module

public import BondalThomsen.Fan.PrimitiveRelationUniqueness
public import BondalThomsen.DeepFan.BadPrimitivePair

@[expose] public section

open Finset Set Module Classical

namespace TauCeti.Toric.Fan

section Algebraic

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def PrimitiveLatticeRelation.degree
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) : ℤ :=
  (Fintype.card left : ℤ) - (∑ ray : right, relation.coefficients ray : ℕ)

theorem PrimitiveLatticeRelation.degree_eq_sum_support_gaps
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) (datum : Lattice →+ ℤ)
    (right_values : ∀ ray : right, datum ray.val.val = -1) :
    relation.degree = ∑ ray : left, (1 + datum ray.val.val) := by
  have evaluated : (∑ ray : left, datum ray.val.val) =
      -((∑ ray : right, relation.coefficients ray : ℕ) : ℤ) := by
    have mapped := congrArg datum relation.lattice_eq
    simpa only [map_sum, map_zsmul, right_values, zsmul_eq_mul, mul_neg_one,
      sum_neg_distrib, Nat.cast_sum, Int.cast_id] using mapped
  rw [sum_add_distrib, evaluated]
  simp [PrimitiveLatticeRelation.degree, sub_eq_add_neg]

theorem PrimitiveLatticeRelation.degree_pos_of_support
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) (datum : Lattice →+ ℤ)
    (right_values : ∀ ray : right, datum ray.val.val = -1)
    (left_bounds : ∀ ray : left, -1 ≤ datum ray.val.val)
    (strict_left : ∃ ray : left, -1 < datum ray.val.val) :
    0 < relation.degree := by
  obtain ⟨chosen, strict⟩ := strict_left
  rw [relation.degree_eq_sum_support_gaps datum right_values]
  have bound : 1 + datum chosen.val.val ≤ ∑ ray : left, (1 + datum ray.val.val) :=
    Finset.single_le_sum (f := fun ray : left => 1 + datum ray.val.val)
      (fun ray _ => by have lower := left_bounds ray; omega)
      (Finset.mem_univ chosen)
  omega

theorem PrimitiveLatticeRelation.degree_pos_iff_coefficient_sum_lt
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) :
    0 < relation.degree ↔ (∑ ray : right, relation.coefficients ray) < Fintype.card left := by
  unfold PrimitiveLatticeRelation.degree
  omega

def HasStrictAnticanonicalConeSupport (fan : TauCeti.Toric.Fan embedding) : Prop :=
  ∀ dimension : ℕ, ∀ basis : Basis (Fin dimension) ℤ Lattice,
    fan.IsConeBasis basis → ∀ ray : fan.Ray, ray.val ∉ Set.range basis →
      (-1 : ℤ) < (-basis.sumCoords.toAddMonoidHom) ray.val

end Algebraic

section ConeBasis

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem IsPrimitiveCollection.exists_nongenerator_of_coneBasis
    {fan : TauCeti.Toric.Fan embedding} {left : Finset fan.Ray}
    (primitive : fan.IsPrimitiveCollection left) (regular : fan.IsRegular)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) :
    ∃ ray : left, ray.val.val ∉ Set.range basis := by
  by_contra absent
  apply primitive.2.1
  apply fan.finiteRayHull_mem_of_basis_generators regular basis cone_basis left
  intro ray member
  have contains : ray.val ∈ Set.range basis := by
    by_contra outside
    exact absent ⟨⟨ray, member⟩, outside⟩
  exact contains

theorem PrimitiveLatticeRelation.right_generators_of_sum_mem_coneBasis
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (contains : embedding (∑ ray : left, ray.val.val) ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index)))) :
    ∀ ray : right, ∃ index, basis index = ray.val.val := by
  intro ray
  apply fan.ray_eq_basis_of_mem_coneBasis basis cone_basis ray.val
  exact relation.rightCone_le_of_sum_mem cone_basis contains
    (PointedCone.subset_hull ⟨ray.val, ray.property, rfl⟩)

theorem PrimitiveLatticeRelation.degree_pos_of_strict_coneBasis_support
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) (regular : fan.IsRegular)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis)
    (contains : embedding (∑ ray : left, ray.val.val) ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (basis index))))
    (strict_support : ∀ ray : fan.Ray, ray.val ∉ Set.range basis →
      (-1 : ℤ) < (-basis.sumCoords.toAddMonoidHom) ray.val) :
    0 < relation.degree := by
  let datum : Lattice →+ ℤ := -basis.sumCoords.toAddMonoidHom
  have on_generators : ∀ vector ∈ Set.range basis, datum vector = -1 := by
    rintro _ ⟨index, rfl⟩
    simp [datum]
  apply relation.degree_pos_of_support datum
  · intro ray
    obtain ⟨index, same⟩ := relation.right_generators_of_sum_mem_coneBasis basis cone_basis contains ray
    exact on_generators _ ⟨index, same⟩
  · intro ray
    by_cases generator : ray.val.val ∈ Set.range basis
    · rw [on_generators _ generator]
    · exact (strict_support ray.val generator).le
  · obtain ⟨ray, outside⟩ := relation.primitive_collection.exists_nongenerator_of_coneBasis
      regular basis cone_basis
    exact ⟨ray, strict_support ray.val outside⟩

theorem PrimitiveRelationConeBasis.sum_mem_coneBasis
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    {relation : PrimitiveLatticeRelation fan left right} {distinguished : left} {dimension : ℕ}
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension) :
    embedding (∑ ray : left, ray.val.val) ∈ PointedCone.hull ℝ
      (Set.range (fun index => embedding (cone_basis.basis index))) := by
  rw [relation.embedded_lattice_eq]
  apply Submodule.sum_mem
  intro ray _
  apply PointedCone.smul_mem _ (Nat.cast_nonneg _)
  apply PointedCone.subset_hull
  exact ⟨cone_basis.indices (Sum.inr ray), congrArg embedding (cone_basis.right_eq ray)⟩

theorem PrimitiveRelationConeBasis.degree_pos_of_strict_support
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    {relation : PrimitiveLatticeRelation fan left right} {distinguished : left} {dimension : ℕ}
    (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension)
    (regular : fan.IsRegular)
    (strict_support : ∀ ray : fan.Ray, ray.val ∉ Set.range cone_basis.basis →
      (-1 : ℚ) < cone_basis.anticanonicalDatum ray.val) : 0 < relation.degree := by
  apply relation.degree_pos_of_strict_coneBasis_support regular cone_basis.basis
    cone_basis.cone_basis cone_basis.sum_mem_coneBasis
  intro ray outside
  have bound := strict_support ray outside
  change (-1 : ℚ) < ((-cone_basis.basis.sumCoords.toAddMonoidHom) ray.val : ℤ) at bound
  exact_mod_cast bound

end ConeBasis

section Complete

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem PrimitiveLatticeRelation.degree_pos_of_strict_support
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (strict_support : fan.HasStrictAnticanonicalConeSupport) : 0 < relation.degree := by
  obtain ⟨dimension, basis, cone_basis, contains⟩ := fan.exists_coneBasis_containing
    complete regular (embedding (∑ ray : left, ray.val.val))
  exact relation.degree_pos_of_strict_coneBasis_support regular basis cone_basis contains
    (strict_support dimension basis cone_basis)

end Complete

end TauCeti.Toric.Fan
