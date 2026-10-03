module

public import BondalThomsen.Fan.PrimitiveRelationExistence

@[expose] public section

open Finset Set Module Classical

namespace TauCeti.Toric.Fan

section Algebraic

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem PrimitiveLatticeRelation.embedded_lattice_eq
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) :
    embedding (∑ ray : left, ray.val.val) =
      ∑ ray : right, (relation.coefficients ray : ℝ) • embedding ray.val.val := by
  rw [relation.lattice_eq, map_sum]
  congr 1
  funext ray
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast]

theorem PrimitiveLatticeRelation.sum_mem_rightCone
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right) :
    embedding (∑ ray : left, ray.val.val) ∈ fan.finiteRayHull right := by
  rw [relation.embedded_lattice_eq]
  apply Submodule.sum_mem
  intro ray _
  exact (fan.finiteRayHull right).smul_mem (Nat.cast_nonneg _)
    (PointedCone.subset_hull ⟨ray.val, ray.property, rfl⟩)

theorem PrimitiveLatticeRelation.face_eq_of_sum_mem
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right)
    {face : PointedCone ℝ Ambient} (is_face : face.IsFaceOf (fan.finiteRayHull right))
    (contains : embedding (∑ ray : left, ray.val.val) ∈ face) :
    face = fan.finiteRayHull right := by
  apply le_antisymm is_face.le
  apply Submodule.span_le.mpr
  rintro _ ⟨ray, member, rfl⟩
  rw [relation.embedded_lattice_eq] at contains
  exact is_face.mem_of_sum_smul_mem
    (fun selected : right => PointedCone.subset_hull
      ⟨selected.val, selected.property, rfl⟩)
    (fun selected => Nat.cast_nonneg (relation.coefficients selected)) contains
    ⟨ray, member⟩ (by exact_mod_cast relation.positive ⟨ray, member⟩)

theorem PrimitiveLatticeRelation.rightCone_le_of_sum_mem
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (relation : PrimitiveLatticeRelation fan left right)
    {cone : PointedCone ℝ Ambient} (cone_member : cone ∈ fan.cones)
    (contains : embedding (∑ ray : left, ray.val.val) ∈ cone) :
    fan.finiteRayHull right ≤ cone := by
  have same := relation.face_eq_of_sum_mem
    (fan.inf_isFaceOf_left relation.right_cone cone_member)
    ⟨relation.sum_mem_rightCone, contains⟩
  exact same ▸ inf_le_right

theorem PrimitiveLatticeRelation.rightCone_eq_of_same_left
    {fan : TauCeti.Toric.Fan embedding} {left first_right second_right : Finset fan.Ray}
    (first : PrimitiveLatticeRelation fan left first_right)
    (second : PrimitiveLatticeRelation fan left second_right) :
    fan.finiteRayHull first_right = fan.finiteRayHull second_right :=
  le_antisymm (first.rightCone_le_of_sum_mem second.right_cone second.sum_mem_rightCone)
    (second.rightCone_le_of_sum_mem first.right_cone first.sum_mem_rightCone)

theorem ray_mem_of_mem_finiteRayHull (fan : TauCeti.Toric.Fan embedding)
    (rays : Finset fan.Ray) (cone_member : fan.finiteRayHull rays ∈ fan.cones)
    (ray : fan.Ray) (contains : embedding ray.val ∈ fan.finiteRayHull rays) :
    ray ∈ rays := by
  have nonzero : embedding ray.val ≠ 0 := by
    simpa only [map_zero] using fan.lattice.injective.ne ray.property.1.ne_zero
  have ray_le : PointedCone.hull ℝ {embedding ray.val} ≤ fan.finiteRayHull rays :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr contains)
  have ray_face := fan.isFaceOf_of_le cone_member ray.property.2 ray_le
  let actual_ray := ToricRay.faceEmbedding ray_face (ToricRay.hullSingleton nonzero)
  have cone_eq : fan.finiteRayHull rays = PointedCone.hull ℝ
      (Set.range (fun selected : rays => embedding selected.val.val)) := by
    change PointedCone.hull ℝ ((fun selected : fan.Ray => embedding selected.val) ''
      (rays : Set fan.Ray)) = _
    rw [Set.image_eq_range]
    rfl
  have generator_exists : ∃ selected : rays, embedding selected.val.val ∈ actual_ray := by
    by_contra absent
    have empty : {selected : rays | embedding selected.val.val ∈ actual_ray} = ∅ := by
      ext selected
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun member => absent ⟨selected, member⟩
    have face_eq := actual_ray.1.eq_hull_image cone_eq
    change actual_ray.toPointedCone = PointedCone.hull ℝ
      ((fun selected : rays => embedding selected.val.val) ''
        {selected | embedding selected.val.val ∈ actual_ray}) at face_eq
    rw [empty, Set.image_empty] at face_eq
    exact actual_ray.toPointedCone_ne_bot (face_eq.trans Submodule.span_empty)
  obtain ⟨selected, selected_contains⟩ := generator_exists
  have same : ray.val = selected.val.val :=
    (show IsPrimitiveGenerator embedding actual_ray ray.val from
      ⟨PointedCone.subset_hull (Set.mem_singleton _), ray.property.1⟩).unique fan.lattice
        ((fan.isToricCone cone_member).salient.anti actual_ray.1.isFaceOf.le)
        ⟨selected_contains, selected.val.property.1⟩
  have same_ray : ray = selected.val := Subtype.ext same
  exact same_ray ▸ selected.property

theorem finiteRayHull_injective_on_cones (fan : TauCeti.Toric.Fan embedding)
    {first second : Finset fan.Ray} (first_cone : fan.finiteRayHull first ∈ fan.cones)
    (second_cone : fan.finiteRayHull second ∈ fan.cones)
    (same : fan.finiteRayHull first = fan.finiteRayHull second) : first = second := by
  apply Finset.Subset.antisymm
  · intro ray member
    apply fan.ray_mem_of_mem_finiteRayHull second second_cone ray
    rw [← same]
    exact PointedCone.subset_hull ⟨ray, member, rfl⟩
  · intro ray member
    apply fan.ray_mem_of_mem_finiteRayHull first first_cone ray
    rw [same]
    exact PointedCone.subset_hull ⟨ray, member, rfl⟩

theorem PrimitiveLatticeRelation.right_eq_of_same_left
    {fan : TauCeti.Toric.Fan embedding} {left first_right second_right : Finset fan.Ray}
    (first : PrimitiveLatticeRelation fan left first_right)
    (second : PrimitiveLatticeRelation fan left second_right) : first_right = second_right :=
  fan.finiteRayHull_injective_on_cones first.right_cone second.right_cone
    (first.rightCone_eq_of_same_left second)

theorem finiteRayHull_generators_linearIndependent (fan : TauCeti.Toric.Fan embedding)
    (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (cone_member : fan.finiteRayHull rays ∈ fan.cones) :
    LinearIndependent ℝ (fun ray : rays => embedding ray.val.val) := by
  let cone := fan.finiteRayHull rays
  have cone_regular : IsRegularCone embedding cone := regular cone_member
  have ray_face : ∀ ray : rays, (PointedCone.hull ℝ {embedding ray.val.val}).IsFaceOf cone := by
    intro ray
    apply fan.isFaceOf_of_le cone_member ray.val.property.2
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (PointedCone.subset_hull ⟨ray.val, ray.property, rfl⟩))
  have nonzero : ∀ ray : rays, embedding ray.val.val ≠ 0 := by
    intro ray
    simpa only [map_zero] using fan.lattice.injective.ne ray.val.property.1.ne_zero
  let cone_ray : rays → ToricRay cone := fun ray =>
    ToricRay.faceEmbedding (ray_face ray) (ToricRay.hullSingleton (nonzero ray))
  have injective : Function.Injective cone_ray := by
    intro first second same
    apply Subtype.ext
    apply fan.ray_hull_injective
    exact congrArg ToricRay.toPointedCone same
  have generator_eq : (fun ray : rays => embedding ray.val.val) =
      (fun ray : ToricRay cone => embedding
        (primitiveGenerator fan.lattice cone_regular.toIsToricCone ray)) ∘ cone_ray := by
    funext ray
    have primitive : IsPrimitiveGenerator embedding (cone_ray ray) ray.val.val :=
      ⟨PointedCone.subset_hull (Set.mem_singleton _), ray.val.property.1⟩
    exact congrArg embedding (primitive.eq_primitiveGenerator
      fan.lattice cone_regular.toIsToricCone)
  rw [generator_eq]
  exact (cone_regular.linearIndependent_primitiveGenerator fan.lattice).comp cone_ray injective

theorem PrimitiveLatticeRelation.coefficients_eq_of_same_right
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (first second : PrimitiveLatticeRelation fan left right) (regular : fan.IsRegular) :
    first.coefficients = second.coefficients := by
  have independent := fan.finiteRayHull_generators_linearIndependent regular right first.right_cone
  have same : (∑ ray : right, (first.coefficients ray : ℝ) • embedding ray.val.val) =
      ∑ ray : right, (second.coefficients ray : ℝ) • embedding ray.val.val :=
    first.embedded_lattice_eq.symm.trans second.embedded_lattice_eq
  funext ray
  exact_mod_cast independent.eq_coords_of_eq same ray

theorem PrimitiveLatticeRelation.eq_of_same_right
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    (first second : PrimitiveLatticeRelation fan left right) (regular : fan.IsRegular) :
    first = second := by
  have same := first.coefficients_eq_of_same_right second regular
  cases first
  cases second
  cases same
  rfl

theorem primitiveLatticeRelation_subsingleton (fan : TauCeti.Toric.Fan embedding)
    (regular : fan.IsRegular) (left : Finset fan.Ray) :
    Subsingleton (Σ right : Finset fan.Ray, PrimitiveLatticeRelation fan left right) := by
  constructor
  rintro ⟨first_right, first⟩ ⟨second_right, second⟩
  have same := first.right_eq_of_same_left second
  subst second_right
  exact congrArg (Sigma.mk first_right) (first.eq_of_same_right second regular)

end Algebraic

end TauCeti.Toric.Fan
