module

public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Basic.Real.Basic
public import BondalThomsen.Fan.QuotientBasis
import Mathlib.Tactic.Abel

@[expose] public section

namespace BondalThomsen

open Set

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space]

theorem face_eq_of_fullSpan {face cone : PointedCone ℝ Space} (is_face : face.IsFaceOf cone)
    (full_span : Submodule.span ℝ (face : Set Space) = ⊤) : face = cone := by
  apply le_antisymm is_face.le
  intro point member
  have in_span : point ∈ Submodule.span ℝ (face : Set Space) := by
    rw [full_span]
    trivial
  obtain ⟨positive, positive_member, negative, negative_member, equality⟩ :=
    PointedCone.mem_span.mp in_span
  have sum_member : point + negative ∈ face := by
    rw [equality, sub_add_cancel]
    exact positive_member
  exact is_face.mem_of_add_mem_left member (is_face.le negative_member) sum_member

theorem pointedCone_map_hull {Target : Type*} [AddCommGroup Target] [Module ℝ Target]
    (linear : Space →ₗ[ℝ] Target) (generators : Set Space) :
    PointedCone.map linear (PointedCone.hull ℝ generators) =
      PointedCone.hull ℝ (linear '' generators) :=
  Submodule.map_span _ _

theorem rayQuotient_map_ray (vector : Space) :
    PointedCone.map (Submodule.span ℝ {vector}).mkQ (PointedCone.hull ℝ {vector}) = ⊥ := by
  rw [pointedCone_map_hull, Set.image_singleton]
  have killed : (Submodule.span ℝ {vector}).mkQ vector = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [killed]
  exact Submodule.span_zero

theorem basisRayQuotient_cone {Index : Type*} [Fintype Index] [DecidableEq Index]
    (basis : Module.Basis Index ℝ Space) (removed : Index) :
    PointedCone.map (Submodule.span ℝ {basis removed}).mkQ
      (PointedCone.hull ℝ (Set.range basis)) =
      PointedCone.hull ℝ (Set.range (basisRayQuotient basis removed)) := by
  rw [pointedCone_map_hull]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro point ⟨_, ⟨index, rfl⟩, rfl⟩
    by_cases same : index = removed
    · subst index
      have killed : (Submodule.span ℝ {basis removed}).mkQ (basis removed) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Set.mem_singleton _)
      rw [killed]
      exact Submodule.zero_mem _
    · rw [← basisRayQuotient_apply basis removed ⟨index, same⟩]
      exact PointedCone.subset_hull ⟨⟨index, same⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro point ⟨index, rfl⟩
    rw [basisRayQuotient_apply]
    exact PointedCone.subset_hull ⟨basis index.val, ⟨index.val, rfl⟩, rfl⟩

theorem basisVectorQuotient_cone {Index : Type*} [Fintype Index] [DecidableEq Index]
    (basis : Module.Basis Index ℝ Space) (removed : Index) (vector : Space)
    (equality : basis removed = vector) :
    PointedCone.map (Submodule.span ℝ {vector}).mkQ
      (PointedCone.hull ℝ (Set.range basis)) =
      PointedCone.hull ℝ (Set.range (basisVectorQuotient basis removed vector equality)) := by
  subst vector
  rw [basisRayQuotient_cone]
  apply congrArg (PointedCone.hull ℝ)
  apply congrArg Set.range
  funext index
  rw [basisVectorQuotient_apply, basisRayQuotient_apply]

theorem rayQuotient_commonLift (vector first second : Space)
    (equality : (Submodule.span ℝ {vector}).mkQ first =
      (Submodule.span ℝ {vector}).mkQ second) :
    ∃ first_scalar second_scalar : ℝ, 0 ≤ first_scalar ∧ 0 ≤ second_scalar ∧
      first + first_scalar • vector = second + second_scalar • vector := by
  have difference : first - second ∈ Submodule.span ℝ {vector} :=
    (Submodule.Quotient.eq _).mp equality
  obtain ⟨scalar, scalar_eq⟩ := Submodule.mem_span_singleton.mp difference
  have first_eq : first = second + scalar • vector := by
    rw [scalar_eq]
    abel
  by_cases nonnegative : 0 ≤ scalar
  · exact ⟨0, scalar, le_rfl, nonnegative, by simpa using first_eq⟩
  · refine ⟨-scalar, 0, neg_nonneg.mpr (le_of_not_ge nonnegative), le_rfl, ?_⟩
    rw [first_eq]
    simp

theorem rayQuotient_map_inf (vector : Space) (first second : PointedCone ℝ Space)
    (first_contains : vector ∈ first) (second_contains : vector ∈ second) :
    PointedCone.map (Submodule.span ℝ {vector}).mkQ (first ⊓ second) =
      PointedCone.map (Submodule.span ℝ {vector}).mkQ first ⊓
        PointedCone.map (Submodule.span ℝ {vector}).mkQ second := by
  apply PointedCone.ext
  intro point
  constructor
  · rintro ⟨lifted, ⟨first_member, second_member⟩, equality⟩
    exact ⟨⟨lifted, first_member, equality⟩, ⟨lifted, second_member, equality⟩⟩
  · rintro ⟨⟨first_lift, first_member, first_eq⟩,
      ⟨second_lift, second_member, second_eq⟩⟩
    obtain ⟨first_scalar, second_scalar, first_nonnegative, second_nonnegative, same⟩ :=
      rayQuotient_commonLift vector first_lift second_lift (first_eq.trans second_eq.symm)
    refine ⟨first_lift + first_scalar • vector, ⟨?_, ?_⟩, ?_⟩
    · exact first.add_mem first_member (first.smul_mem first_nonnegative first_contains)
    · rw [same]
      exact second.add_mem second_member (second.smul_mem second_nonnegative second_contains)
    · simp only [map_add, first_eq]
      have killed : (Submodule.span ℝ {vector}).mkQ vector = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Set.mem_singleton _)
      simp [killed]

theorem rayQuotient_face_saturated (vector : Space) {face cone : PointedCone ℝ Space}
    (is_face : face.IsFaceOf cone) (contains : vector ∈ face) {point : Space}
    (member : point ∈ cone)
    (projected : (Submodule.span ℝ {vector}).mkQ point ∈
      PointedCone.map (Submodule.span ℝ {vector}).mkQ face) : point ∈ face := by
  obtain ⟨lifted, lifted_member, equality⟩ := projected
  obtain ⟨first_scalar, second_scalar, first_nonnegative, second_nonnegative, same⟩ :=
    rayQuotient_commonLift vector point lifted equality.symm
  have sum_member : point + first_scalar • vector ∈ face := by
    rw [same]
    exact face.add_mem lifted_member (face.smul_mem second_nonnegative contains)
  exact is_face.mem_of_add_mem_left member
    (cone.smul_mem first_nonnegative (is_face.le contains)) sum_member

theorem rayQuotient_map_isFaceOf (vector : Space) {face cone : PointedCone ℝ Space}
    (is_face : face.IsFaceOf cone) (contains : vector ∈ face) :
    (PointedCone.map (Submodule.span ℝ {vector}).mkQ face).IsFaceOf
      (PointedCone.map (Submodule.span ℝ {vector}).mkQ cone) := by
  refine ⟨?_, ?_⟩
  · rintro point ⟨lifted, member, equality⟩
    exact ⟨lifted, is_face.le member, equality⟩
  · intro first second scalar first_member second_member positive sum_member
    obtain ⟨first_lift, first_in_cone, first_eq⟩ := first_member
    obtain ⟨second_lift, second_in_cone, second_eq⟩ := second_member
    change (Submodule.span ℝ {vector}).mkQ first_lift = first at first_eq
    change (Submodule.span ℝ {vector}).mkQ second_lift = second at second_eq
    have sum_in_cone : scalar • first_lift + second_lift ∈ cone :=
      cone.add_mem (cone.smul_mem positive.le first_in_cone) second_in_cone
    have sum_projected : (Submodule.span ℝ {vector}).mkQ
        (scalar • first_lift + second_lift) ∈
        PointedCone.map (Submodule.span ℝ {vector}).mkQ face := by
      simpa only [map_add, map_smul, first_eq, second_eq] using sum_member
    exact ⟨first_lift, is_face.mem_of_smul_add_mem first_in_cone second_in_cone positive
      (rayQuotient_face_saturated vector is_face contains sum_in_cone sum_projected), first_eq⟩

theorem rayQuotient_face_lift (vector : Space) (cone : PointedCone ℝ Space)
    (contains : vector ∈ cone) (face : PointedCone ℝ
      (Space ⧸ Submodule.span ℝ {vector}))
    (is_face : face.IsFaceOf (PointedCone.map (Submodule.span ℝ {vector}).mkQ cone)) :
    ∃ lifted : PointedCone ℝ Space, lifted.IsFaceOf cone ∧ vector ∈ lifted ∧
      PointedCone.map (Submodule.span ℝ {vector}).mkQ lifted = face := by
  let projection := (Submodule.span ℝ {vector}).mkQ
  let lifted := cone ⊓ PointedCone.comap projection face
  have lifted_face : lifted.IsFaceOf cone := by
    refine ⟨inf_le_left, ?_⟩
    intro first second scalar first_member second_member positive sum_member
    refine ⟨?_, ?_⟩
    · exact first_member
    · apply is_face.mem_of_smul_add_mem
        (show projection first ∈ PointedCone.map projection cone from ⟨first, first_member, rfl⟩)
        (show projection second ∈ PointedCone.map projection cone from ⟨second, second_member, rfl⟩)
        positive
      have projected_member := sum_member.2
      change projection (scalar • first + second) ∈ face at projected_member
      simpa only [map_add, map_smul] using projected_member
  refine ⟨lifted, lifted_face, ⟨contains, ?_⟩, ?_⟩
  · change projection vector ∈ face
    have killed : projection vector = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span (Set.mem_singleton _)
    rw [killed]
    exact face.zero_mem
  · apply PointedCone.ext
    intro point
    constructor
    · rintro ⟨representative, ⟨_, member⟩, rfl⟩
      exact member
    · intro member
      obtain ⟨representative, in_cone, equality⟩ := is_face.le member
      change projection representative = point at equality
      exact ⟨representative, ⟨in_cone, by change projection representative ∈ face; rwa [equality]⟩,
        equality⟩

theorem rayQuotient_map_salient (vector : Space) (cone : PointedCone ℝ Space)
    (ray_face : (PointedCone.hull ℝ {vector}).IsFaceOf cone) :
    (PointedCone.map (Submodule.span ℝ {vector}).mkQ cone : ConvexCone ℝ
      (Space ⧸ Submodule.span ℝ {vector})).Salient := by
  intro point member nonzero negative_member
  obtain ⟨first, first_member, first_eq⟩ := member
  obtain ⟨second, second_member, second_eq⟩ := negative_member
  change (Submodule.span ℝ {vector}).mkQ first = point at first_eq
  change (Submodule.span ℝ {vector}).mkQ second = -point at second_eq
  have projected_zero : (Submodule.span ℝ {vector}).mkQ (first + second) = 0 := by
    rw [map_add, first_eq, second_eq, add_neg_cancel]
  have sum_in_ray : first + second ∈ PointedCone.hull ℝ {vector} := by
    apply rayQuotient_face_saturated vector ray_face
      (PointedCone.subset_hull (Set.mem_singleton _)) (cone.add_mem first_member second_member)
    rw [rayQuotient_map_ray, projected_zero]
    exact Submodule.zero_mem _
  have first_in_ray := ray_face.mem_of_add_mem_left first_member second_member sum_in_ray
  have zero_image : (Submodule.span ℝ {vector}).mkQ first ∈
      PointedCone.map (Submodule.span ℝ {vector}).mkQ (PointedCone.hull ℝ {vector}) :=
    ⟨first, first_in_ray, rfl⟩
  rw [rayQuotient_map_ray] at zero_image
  have zero_equality : (Submodule.span ℝ {vector}).mkQ first = 0 := zero_image
  exact nonzero (first_eq.symm.trans zero_equality)

end BondalThomsen
