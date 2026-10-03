module

public import BondalThomsen.Fan.Basic

@[expose] public section

namespace TauCeti.Toric

open Set Module

variable {Lattice Ambient Index : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient} [Fintype Index] [DecidableEq Index]

omit [Fintype Index] [DecidableEq Index] in

theorem toricRay_contains_basis_generator (basis : Basis Index ℤ Lattice)
    (cone : PointedCone ℝ Ambient)
    (cone_eq : cone = PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))
    (ray : ToricRay cone) : ∃ index, embedding (basis index) ∈ ray := by
  by_contra absent
  have empty : {index : Index | embedding (basis index) ∈ ray} = ∅ := by
    ext index
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun member => absent ⟨index, member⟩
  have face_eq := ray.1.eq_hull_image cone_eq
  change ray.toPointedCone = PointedCone.hull ℝ
    ((fun index => embedding (basis index)) '' {index | embedding (basis index) ∈ ray}) at face_eq
  rw [empty, Set.image_empty] at face_eq
  exact ray.toPointedCone_ne_bot (face_eq.trans Submodule.span_empty)

omit [Fintype Index] [DecidableEq Index] in

theorem primitive_eq_basis_of_ray_face (lattice : IsIntegralLattice embedding)
    (basis : Basis Index ℤ Lattice) (vector : Lattice) (primitive : TauCeti.IsPrimitive vector)
    (ray_face : (PointedCone.hull ℝ {embedding vector}).IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (salient : (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) :
      ConvexCone ℝ Ambient).Salient) : ∃ index, vector = basis index := by
  have nonzero : embedding vector ≠ 0 := by
    simpa only [map_zero] using lattice.injective.ne primitive.ne_zero
  let ray := ToricRay.faceEmbedding ray_face (ToricRay.hullSingleton nonzero)
  obtain ⟨index, contains⟩ := toricRay_contains_basis_generator basis _ rfl ray
  refine ⟨index, ?_⟩
  exact (show IsPrimitiveGenerator embedding ray vector from
    ⟨PointedCone.subset_hull (Set.mem_singleton _), primitive⟩).unique lattice
      (salient.anti ray.1.isFaceOf.le)
      ⟨contains, basis.isPrimitive index⟩

omit [DecidableEq Index] in

theorem isRegularCone_of_basisHull (lattice : IsIntegralLattice embedding)
    (basis : Basis Index ℤ Lattice) (cone : PointedCone ℝ Ambient)
    (toric : IsToricCone embedding cone)
    (cone_eq : cone = PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) :
    IsRegularCone embedding cone := by
  classical
  have has_generator := toricRay_contains_basis_generator basis cone cone_eq
  let ray_index := fun ray : ToricRay cone => (has_generator ray).choose
  have ray_contains : ∀ ray : ToricRay cone, embedding (basis (ray_index ray)) ∈ ray :=
    fun ray => (has_generator ray).choose_spec
  have ray_eq : ∀ ray : ToricRay cone, ray.toPointedCone =
      PointedCone.hull ℝ {embedding (basis (ray_index ray))} := by
    intro ray
    exact ray.eq_hull_singleton (toric.salient.anti ray.1.isFaceOf.le)
      (ray_contains ray) (by
        simpa only [map_zero] using lattice.injective.ne (basis.ne_zero (ray_index ray)))
  have injective : Function.Injective ray_index := by
    intro first second same
    apply SetLike.coe_injective
    exact congrArg (fun pointed : PointedCone ℝ Ambient => (pointed : Set Ambient))
      ((ray_eq first).trans (by rw [same, ← ray_eq second]))
  let indices : ToricRay cone ↪ Fin (Fintype.card Index) :=
    ⟨fun ray => Fintype.equivFin Index (ray_index ray),
      fun first second same => injective ((Fintype.equivFin Index).injective same)⟩
  refine ⟨toric, Fintype.card Index, basis.reindex (Fintype.equivFin Index), indices, ⟨?_⟩⟩
  intro ray
  change IsPrimitiveGenerator embedding ray
    ((basis.reindex (Fintype.equivFin Index)) (Fintype.equivFin Index (ray_index ray)))
  rw [Basis.reindex_apply, Equiv.symm_apply_apply]
  exact ⟨ray_contains ray, basis.isPrimitive (ray_index ray)⟩

omit [Fintype Index] in

theorem basisCone_change_coordinates (lattice : IsIntegralLattice embedding)
    {OtherIndex : Type*} [Fintype OtherIndex]
    (first : Basis Index ℤ Lattice) (second : Basis OtherIndex ℤ Lattice)
    (same_cone : PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) =
      PointedCone.hull ℝ (Set.range (fun index => embedding (second index))))
    (salient : (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) :
      ConvexCone ℝ Ambient).Salient) :
    ∃ matching : Index → OtherIndex, Function.Injective matching ∧
      ∀ vector index, first.repr vector index = second.repr vector (matching index) := by
  classical
  have independent : LinearIndependent ℝ (fun index => embedding (first index)) := by
    convert (lattice.isBaseChange.basis first).linearIndependent using 1
    funext index
    exact (lattice.isBaseChange.basis_apply first index).symm
  have matching_exists : ∀ index, ∃ other, first index = second other := by
    intro index
    have face := PointedCone.isFaceOf_hull_image independent rfl {index}
    simp only [Set.image_singleton] at face
    rw [same_cone] at face
    exact primitive_eq_basis_of_ray_face lattice second (first index)
      (first.isPrimitive index) face (same_cone ▸ salient)
  let matching := fun index => (matching_exists index).choose
  have same_vectors : ∀ index, first index = second (matching index) :=
    fun index => (matching_exists index).choose_spec
  have injective : Function.Injective matching := by
    intro first_index second_index same
    apply first.injective
    rw [same_vectors, same_vectors, same]
  refine ⟨matching, injective, ?_⟩
  intro vector index
  have same_functional : first.coord index = second.coord (matching index) := by
    apply first.ext
    intro original
    rw [same_vectors original]
    simp only [Basis.coord_apply, Basis.repr_self_apply]
    simp only [Function.Injective.eq_iff injective]
    rw [← same_vectors original]
    simp [Finsupp.single_apply]
  exact DFunLike.congr_fun same_functional vector

end TauCeti.Toric
