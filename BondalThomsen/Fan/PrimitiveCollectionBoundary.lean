module

public import BondalThomsen.Fan.Basic
public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Generation
public import BondalThomsen.Ports.TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic

@[expose] public section

open Set Module

namespace BondalThomsen

def IsMinimalNonface {Vertex : Type*} (complex : PreAbstractSimplicialComplex Vertex)
    (vertices : Finset Vertex) : Prop :=
  vertices.Nonempty ∧ vertices ∉ complex ∧
    ∀ subset : Finset Vertex, subset.Nonempty → subset ⊂ vertices → subset ∈ complex

theorem IsMinimalNonface.two_le_card {Vertex : Type*}
    {complex : PreAbstractSimplicialComplex Vertex} {vertices : Finset Vertex}
    (minimal : IsMinimalNonface complex vertices)
    (singletons : ∀ vertex : Vertex, ({vertex} : Finset Vertex) ∈ complex) :
    2 ≤ vertices.card := by
  have positive := Finset.card_pos.mpr minimal.1
  by_contra small
  have cardinality : vertices.card = 1 := by omega
  obtain ⟨vertex, same⟩ := Finset.card_eq_one.mp cardinality
  exact minimal.2.1 (same ▸ singletons vertex)

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

def finiteRayHull (fan : TauCeti.Toric.Fan embedding) (rays : Finset fan.Ray) :
    PointedCone ℝ Ambient :=
  PointedCone.hull ℝ ((fun ray : fan.Ray => embedding ray.val) '' (rays : Set fan.Ray))

@[simp] theorem finiteRayHull_empty (fan : TauCeti.Toric.Fan embedding) :
    fan.finiteRayHull ∅ = ⊥ := by
  simp only [finiteRayHull, Finset.coe_empty, Set.image_empty]
  exact Submodule.span_empty

@[simp] theorem finiteRayHull_singleton (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    fan.finiteRayHull {ray} = PointedCone.hull ℝ {embedding ray.val} := by
  classical
  simp [finiteRayHull]

theorem finiteRayHull_mem_of_subset (fan : TauCeti.Toric.Fan embedding)
    (regular : fan.IsRegular) {rays subset : Finset fan.Ray}
    (cone_member : fan.finiteRayHull rays ∈ fan.cones) (contained : subset ⊆ rays) :
    fan.finiteRayHull subset ∈ fan.cones := by
  classical
  let cone := fan.finiteRayHull rays
  have cone_regular : TauCeti.Toric.IsRegularCone embedding cone := regular cone_member
  let generators := fun ray : TauCeti.Toric.ToricRay cone =>
    embedding (TauCeti.Toric.primitiveGenerator fan.lattice cone_regular.toIsToricCone ray)
  let selected := (fun ray : fan.Ray => embedding ray.val) '' (subset : Set fan.Ray)
  have in_range : selected ⊆ Set.range generators := by
    rintro point ⟨ray, ray_member, rfl⟩
    have hull_le : PointedCone.hull ℝ {embedding ray.val} ≤ cone := by
      apply Submodule.span_mono
      intro vector vector_member
      have vector_eq := Set.mem_singleton_iff.mp vector_member
      exact ⟨ray, contained ray_member, vector_eq.symm⟩
    have face := fan.isFaceOf_of_le cone_member ray.property.2 hull_le
    have nonzero : embedding ray.val ≠ 0 := by
      simpa only [map_zero] using fan.lattice.injective.ne ray.property.1.ne_zero
    let cone_ray := TauCeti.Toric.ToricRay.faceEmbedding face
      (TauCeti.Toric.ToricRay.hullSingleton nonzero)
    have primitive : TauCeti.Toric.IsPrimitiveGenerator embedding cone_ray ray.val :=
      ⟨PointedCone.subset_hull (Set.mem_singleton _), ray.property.1⟩
    have same := primitive.eq_primitiveGenerator fan.lattice cone_regular.toIsToricCone
    exact ⟨cone_ray, congrArg embedding same.symm⟩
  have generated_eq : generators '' generators ⁻¹' selected = selected :=
    Set.image_preimage_eq_of_subset in_range
  have cone_eq : cone = PointedCone.hull ℝ (Set.range generators) := by
    change cone = PointedCone.hull ℝ
      (Set.range ((fun vector : Lattice => embedding vector) ∘
        TauCeti.Toric.primitiveGenerator fan.lattice cone_regular.toIsToricCone))
    rw [Set.range_comp]
    exact (cone_regular.toIsToricCone.hull_primitiveGenerator fan.lattice).symm
  have face := PointedCone.isFaceOf_hull_image
    (cone_regular.linearIndependent_primitiveGenerator fan.lattice) cone_eq
    (generators ⁻¹' selected)
  rw [generated_eq] at face
  exact fan.mem_of_isFaceOf cone_member face

def rayComplex (fan : TauCeti.Toric.Fan embedding) (regular : fan.IsRegular) :
    PreAbstractSimplicialComplex fan.Ray where
  faces := {rays | rays.Nonempty ∧ fan.finiteRayHull rays ∈ fan.cones}
  isRelLowerSet_faces := by
    rintro rays ⟨nonempty, member⟩
    exact ⟨nonempty, fun subset contained subset_nonempty =>
      ⟨subset_nonempty, fan.finiteRayHull_mem_of_subset regular member contained⟩⟩

@[simp] theorem mem_rayComplex (fan : TauCeti.Toric.Fan embedding) (regular : fan.IsRegular)
    (rays : Finset fan.Ray) : rays ∈ fan.rayComplex regular ↔
      rays.Nonempty ∧ fan.finiteRayHull rays ∈ fan.cones := Iff.rfl

theorem singleton_mem_rayComplex (fan : TauCeti.Toric.Fan embedding)
    (regular : fan.IsRegular) (ray : fan.Ray) : {ray} ∈ fan.rayComplex regular := by
  classical
  rw [mem_rayComplex, finiteRayHull_singleton]
  exact ⟨Finset.singleton_nonempty ray, ray.property.2⟩

def IsPrimitiveCollection (fan : TauCeti.Toric.Fan embedding) (rays : Finset fan.Ray) : Prop :=
  rays.Nonempty ∧ fan.finiteRayHull rays ∉ fan.cones ∧
    ∀ subset : Finset fan.Ray, subset.Nonempty → subset ⊂ rays →
      fan.finiteRayHull subset ∈ fan.cones

theorem IsPrimitiveCollection.proper_subset_hull_mem
    {fan : TauCeti.Toric.Fan embedding} {rays : Finset fan.Ray}
    (primitive : fan.IsPrimitiveCollection rays) {subset : Finset fan.Ray}
    (proper : subset ⊂ rays) : fan.finiteRayHull subset ∈ fan.cones := by
  by_cases nonempty : subset.Nonempty
  · exact primitive.2.2 subset nonempty proper
  · have empty : subset = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    obtain ⟨ray, _member⟩ := primitive.1
    rw [empty, finiteRayHull_empty]
    exact fan.bot_mem ray.property.2

theorem isPrimitiveCollection_iff_minimalNonface (fan : TauCeti.Toric.Fan embedding)
    (regular : fan.IsRegular) (rays : Finset fan.Ray) :
    fan.IsPrimitiveCollection rays ↔ BondalThomsen.IsMinimalNonface (fan.rayComplex regular) rays := by
  constructor
  · rintro ⟨nonempty, not_cone, proper⟩
    exact ⟨nonempty, fun member => not_cone member.2,
      fun subset subset_nonempty subset_proper =>
        ⟨subset_nonempty, proper subset subset_nonempty subset_proper⟩⟩
  · rintro ⟨nonempty, not_face, proper⟩
    exact ⟨nonempty, fun member => not_face ⟨nonempty, member⟩,
      fun subset subset_nonempty subset_proper => (proper subset subset_nonempty subset_proper).2⟩

theorem IsPrimitiveCollection.two_le_card {fan : TauCeti.Toric.Fan embedding}
    {rays : Finset fan.Ray} (primitive : fan.IsPrimitiveCollection rays)
    (regular : fan.IsRegular) : 2 ≤ rays.card :=
  ((fan.isPrimitiveCollection_iff_minimalNonface regular rays).mp primitive).two_le_card
    (fan.singleton_mem_rayComplex regular)

end TauCeti.Toric.Fan
