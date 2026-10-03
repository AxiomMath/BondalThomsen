module

public import BondalThomsen.Fan.Polytope
public import BondalThomsen.Ports.ClosedCones
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Baire.Lemmas

@[expose] public section

namespace BondalThomsen

open Set

variable {Ambient Index : Type*} [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Finite Index]

theorem dense_avoiding_proper_subspaces (subspaces : Index → Submodule ℝ Ambient)
    (proper : ∀ index, subspaces index ≠ ⊤) :
    Dense {point : Ambient | ∀ index, point ∉ subspaces index} := by
  have empty_interior : ∀ index, interior (subspaces index : Set Ambient) = ∅ := by
    intro index
    apply Set.not_nonempty_iff_eq_empty.mp
    intro nonempty
    exact proper index ((subspaces index).eq_top_of_nonempty_interior' nonempty)
  have dense := dense_iInter_of_isOpen
    (fun index => (subspaces index).closed_of_finiteDimensional.isOpen_compl)
    (fun index => interior_eq_empty_iff_dense_compl.mp (empty_interior index))
  have avoiding_eq : {point : Ambient | ∀ index, point ∉ subspaces index} =
      ⋂ index, (subspaces index : Set Ambient)ᶜ := by ext point; simp
  rw [avoiding_eq]
  exact dense

end BondalThomsen

namespace TauCeti.Toric.Fan

open Set Module
open TauCeti.Toric

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in

theorem exists_integralBasis_of_fullSpan (fan : TauCeti.Toric.Fan embedding)
    (cone : PointedCone ℝ Ambient) (regular : IsRegularCone embedding cone)
    (full_span : Submodule.span ℝ (cone : Set Ambient) = ⊤) :
    ∃ size : ℕ, ∃ basis : Basis (Fin size) ℤ Lattice,
      cone = PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) := by
  classical
  obtain ⟨size, basis, ray_indices, extending⟩ := regular.exists_basis
  let real_basis := fan.lattice.isBaseChange.basis basis
  have generator_eq : ∀ ray : ToricRay cone,
      primitiveGenerator fan.lattice regular.toIsToricCone ray = basis (ray_indices ray) := by
    intro ray
    exact ((extending.isPrimitiveGenerator_apply ray).eq_primitiveGenerator
      fan.lattice regular.toIsToricCone).symm
  have onto : Function.Surjective ray_indices := by
    intro index
    by_contra absent
    have not_index : ∀ ray : ToricRay cone, ray_indices ray ≠ index := by
      intro ray equality
      exact absent ⟨ray, equality⟩
    have generators_in_kernel :
        embedding '' Set.range (primitiveGenerator fan.lattice regular.toIsToricCone) ⊆
          (real_basis.coord index).ker := by
      rintro vector ⟨generator, ⟨ray, rfl⟩, rfl⟩
      rw [generator_eq]
      change real_basis.repr (embedding (basis (ray_indices ray))) index = 0
      change real_basis.repr (embedding.toIntLinearMap (basis (ray_indices ray))) index = 0
      rw [← fan.lattice.isBaseChange.basis_apply basis]
      simp [real_basis, Ne.symm (not_index ray)]
    have cone_in_kernel : (cone : Set Ambient) ⊆ (real_basis.coord index).ker := by
      intro vector contains
      rw [← regular.toIsToricCone.hull_primitiveGenerator fan.lattice] at contains
      exact (Submodule.span_le.mpr generators_in_kernel)
        (PointedCone.hull_le_span ℝ _ contains)
    have span_in_kernel := Submodule.span_le.mpr cone_in_kernel
    rw [full_span] at span_in_kernel
    have coordinate_zero := span_in_kernel (Submodule.mem_top : real_basis index ∈ ⊤)
    change real_basis.repr (real_basis index) index = 0 at coordinate_zero
    simp at coordinate_zero
  refine ⟨size, basis, ?_⟩
  rw [← regular.toIsToricCone.hull_primitiveGenerator fan.lattice]
  congr 1
  ext vector
  constructor
  · rintro ⟨generator, ⟨ray, rfl⟩, rfl⟩
    exact ⟨ray_indices ray, congrArg embedding (generator_eq ray).symm⟩
  · rintro ⟨index, rfl⟩
    obtain ⟨ray, rfl⟩ := onto index
    exact ⟨primitiveGenerator fan.lattice regular.toIsToricCone ray,
      ⟨ray, rfl⟩, congrArg embedding (generator_eq ray)⟩

omit [FiniteDimensional ℝ Ambient] in

theorem cone_isClosed (fan : TauCeti.Toric.Fan embedding) (cone : PointedCone ℝ Ambient)
    (member : cone ∈ fan.cones) : IsClosed (cone : Set Ambient) :=
  LeanPool.Erdos81PaperIContrib.PointedCone.FG.isClosed (fan.isToricCone member).fg

theorem exists_fullSpan_cone (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (point : Ambient) :
    ∃ cone ∈ fan.cones, point ∈ cone ∧ Submodule.span ℝ (cone : Set Ambient) = ⊤ := by
  let proper_cones := {cone : fan.cones //
    Submodule.span ℝ (cone.val : Set Ambient) ≠ ⊤}
  let full_cones := {cone : fan.cones //
    Submodule.span ℝ (cone.val : Set Ambient) = ⊤}
  let full_union : Set Ambient := ⋃ cone : full_cones, (cone.val.val : Set Ambient)
  have generic := BondalThomsen.dense_avoiding_proper_subspaces
    (fun cone : proper_cones => Submodule.span ℝ (cone.val.val : Set Ambient))
    (fun cone => cone.property)
  have full_dense : Dense full_union := by
    apply generic.mono
    intro vector avoids
    obtain ⟨cone, member, contains⟩ := fan.isComplete_iff.mp complete vector
    have full_span : Submodule.span ℝ (cone : Set Ambient) = ⊤ := by
      by_contra proper
      exact avoids (⟨⟨cone, member⟩, proper⟩ : proper_cones)
        (Submodule.subset_span contains)
    exact Set.mem_iUnion.mpr ⟨(⟨⟨cone, member⟩, full_span⟩ : full_cones), contains⟩
  have full_closed : IsClosed full_union :=
    isClosed_iUnion_of_finite fun cone : full_cones =>
      fan.cone_isClosed cone.val.val cone.val.property
  have member : point ∈ full_union := by
    rw [← full_closed.closure_eq, full_dense.closure_eq]
    trivial
  obtain ⟨cone, contains⟩ := Set.mem_iUnion.mp member
  exact ⟨cone.val.val, cone.val.property, contains, cone.property⟩

theorem exists_coneBasis_containing (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (point : Ambient) :
    ∃ size : ℕ, ∃ basis : Basis (Fin size) ℤ Lattice,
      fan.IsConeBasis basis ∧
        point ∈ PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) := by
  obtain ⟨cone, member, contains, full_span⟩ := fan.exists_fullSpan_cone complete point
  obtain ⟨size, basis, cone_eq⟩ :=
    fan.exists_integralBasis_of_fullSpan cone (regular member) full_span
  refine ⟨size, basis, ?_, cone_eq ▸ contains⟩
  change PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones
  rwa [← cone_eq]

theorem exists_coneBasis_above (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (cone : PointedCone ℝ Ambient) (member : cone ∈ fan.cones) :
    ∃ size : ℕ, ∃ basis : Basis (Fin size) ℤ Lattice, fan.IsConeBasis basis ∧
      cone.IsFaceOf (PointedCone.hull ℝ
        (Set.range (fun index => embedding (basis index)))) := by
  classical
  let toric := fan.isToricCone member
  let := ToricRay.finite_of_fg toric.fg
  let generators := fun ray : ToricRay cone => embedding
    (primitiveGenerator fan.lattice toric ray)
  let := Fintype.ofFinite (ToricRay cone)
  obtain ⟨size, basis, basis_member, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (∑ ray, generators ray)
  let containing := PointedCone.hull ℝ
    (Set.range (fun index => embedding (basis index)))
  have intersection_face := fan.inf_isFaceOf_left member basis_member
  have generator_membership : ∀ ray, generators ray ∈ cone := fun ray =>
    ray.1.isFaceOf.le (primitiveGenerator_mem fan.lattice toric ray)
  have sum_in_intersection : ∑ ray, generators ray ∈ cone ⊓ containing :=
    ⟨Submodule.sum_mem _ (fun ray _ => generator_membership ray), contains⟩
  have generators_in_containing : ∀ ray, generators ray ∈ containing := fun ray =>
    (intersection_face.mem_of_sum_mem generator_membership sum_in_intersection ray).2
  have cone_le : cone ≤ containing := by
    rw [← toric.hull_primitiveGenerator fan.lattice]
    apply Submodule.span_le.mpr
    rintro vector ⟨generator, ⟨ray, rfl⟩, rfl⟩
    exact generators_in_containing ray
  exact ⟨size, basis, basis_member, fan.isFaceOf_of_le basis_member member cone_le⟩

end TauCeti.Toric.Fan
