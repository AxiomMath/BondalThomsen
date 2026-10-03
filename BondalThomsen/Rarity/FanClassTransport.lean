module

public import BondalThomsen.DeepFan.SchemeTernaryFiniteness

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module Set

namespace BondalThomsen.ToricTransport

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

def IntegralRayFanEquiv.refl (fan : TauCeti.Toric.Fan embedding) :
    IntegralRayFanEquiv fan fan where
  lattice := LinearEquiv.refl ℤ Lattice
  ambient := LinearEquiv.refl ℝ Ambient
  embeddings _vector := rfl
  rays := Equiv.refl fan.Ray
  ray_vectors _ray := rfl
  cones cone := by simp only [LinearEquiv.refl_toLinearMap, PointedCone.map_id]

def IntegralRayFanEquiv.trans
    {source middle target : TauCeti.Toric.Fan embedding}
    (first : IntegralRayFanEquiv source middle)
    (second : IntegralRayFanEquiv middle target) : IntegralRayFanEquiv source target where
  lattice := first.lattice.trans second.lattice
  ambient := first.ambient.trans second.ambient
  embeddings vector := by
    change second.ambient (first.ambient (embedding vector)) = _
    rw [first.embeddings, second.embeddings]
    rfl
  rays := first.rays.trans second.rays
  ray_vectors ray := by
    change second.lattice (first.lattice ray.val) = _
    rw [first.ray_vectors, second.ray_vectors]
    rfl
  cones cone := by
    rw [first.cones, second.cones, PointedCone.map_map]
    rfl

def integralFanSetoid : Setoid (TauCeti.Toric.Fan embedding) where
  r source target := Nonempty (IntegralRayFanEquiv source target)
  iseqv := ⟨fun fan => ⟨IntegralRayFanEquiv.refl fan⟩,
    fun ⟨equivalence⟩ => ⟨equivalence.symm⟩,
    fun ⟨first⟩ ⟨second⟩ => ⟨first.trans second⟩⟩

abbrev IntegralFanClass (embedding : Lattice →+ Ambient) :=
  Quotient (integralFanSetoid (embedding := embedding))

def integralFanClass (fan : TauCeti.Toric.Fan embedding) : IntegralFanClass embedding :=
  Quotient.mk _ fan

theorem integralFanClass_eq_iff (source target : TauCeti.Toric.Fan embedding) :
    integralFanClass source = integralFanClass target ↔
      Nonempty (IntegralRayFanEquiv source target) := Quotient.eq

theorem integralFanClass_eq_of_equiv {source target : TauCeti.Toric.Fan embedding}
    (equivalence : IntegralRayFanEquiv source target) :
    integralFanClass source = integralFanClass target := Quotient.sound ⟨equivalence⟩

variable [FiniteDimensional ℝ Ambient]

theorem nonempty_integralRayFanEquiv_of_primitive_ray_sets
    (source target : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (sourceComplete : source.IsComplete) (sourceRegular : source.IsRegular)
    (sourceDeep : source.IsDeep dimension) (targetComplete : target.IsComplete)
    (targetRegular : target.IsRegular) (targetDeep : target.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (lattice : Lattice ≃ₗ[ℤ] Lattice)
    (raySets : Set.range (fun ray : source.Ray => lattice ray.val) =
      Set.range (fun ray : target.Ray => ray.val)) :
    Nonempty (IntegralRayFanEquiv source target) := by
  have ambientRays : latticeEquivReal source target lattice '' source.rayGenerators =
      target.rayGenerators := by
    ext vector
    constructor
    · rintro ⟨_, ⟨ray, rfl⟩, rfl⟩
      have member : lattice ray.val ∈ Set.range (fun ray : target.Ray => ray.val) := by
        rw [← raySets]
        exact ⟨ray, rfl⟩
      obtain ⟨targetRay, equality⟩ := member
      exact ⟨targetRay, by simpa only [latticeEquivReal_embedding] using
        (congrArg embedding equality)⟩
    · rintro ⟨ray, rfl⟩
      have member : ray.val ∈ Set.range (fun ray : source.Ray => lattice ray.val) := by
        rw [raySets]
        exact ⟨ray, rfl⟩
      obtain ⟨sourceRay, equality⟩ := member
      exact ⟨embedding sourceRay.val, ⟨sourceRay, rfl⟩,
        by simpa only [latticeEquivReal_embedding] using congrArg embedding equality⟩
  obtain ⟨equivalence, _, _⟩ := exists_integralRayFanEquiv_of_rayGenerators_image source target
    sourceComplete sourceRegular sourceDeep targetComplete targetRegular targetDeep reference
    lattice (latticeEquivReal source target lattice) (latticeEquivReal_embedding source target lattice)
    ambientRays
  exact ⟨equivalence⟩

theorem integralFanClass_eq_of_rayMatrix_row_equivalence
    {Label : Type*} (source target : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (sourceComplete : source.IsComplete) (sourceRegular : source.IsRegular)
    (sourceDeep : source.IsDeep dimension) (targetComplete : target.IsComplete)
    (targetRegular : target.IsRegular) (targetDeep : target.IsDeep dimension)
    (sourceBasis targetBasis : Basis (Fin dimension) ℤ Lattice)
    (sourceLabels : Label ≃ source.Ray) (targetLabels : Label ≃ target.Ray)
    (operation : (Matrix (Fin dimension) (Fin dimension) ℤ)ˣ)
    (equality : targetBasis.toMatrix (fun label => (targetLabels label).val) =
      (operation : Matrix (Fin dimension) (Fin dimension) ℤ) *
        sourceBasis.toMatrix (fun label => (sourceLabels label).val)) :
    integralFanClass source = integralFanClass target := by
  classical
  let coordinates := Matrix.toLinearEquiv (Pi.basisFun ℤ (Fin dimension))
    (operation : Matrix (Fin dimension) (Fin dimension) ℤ)
    ((Matrix.isUnit_iff_isUnit_det _).mp operation.isUnit)
  let lattice := (sourceBasis.equivFun.trans coordinates).trans targetBasis.equivFun.symm
  have rayVectors : ∀ label, lattice (sourceLabels label).val = (targetLabels label).val := by
    intro label
    apply targetBasis.equivFun.injective
    ext row
    have entry := congrFun (congrFun equality row) label
    rw [Matrix.mul_apply] at entry
    simpa [lattice, coordinates, LinearEquiv.trans_apply, Basis.equivFun_apply,
      Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Basis.toMatrix_apply, Finsupp.single_apply, eq_comm] using entry.symm
  have raySets : Set.range (fun ray : source.Ray => lattice ray.val) =
      Set.range (fun ray : target.Ray => ray.val) := by
    ext vector
    constructor
    · rintro ⟨ray, rfl⟩
      obtain ⟨label, rfl⟩ := sourceLabels.surjective ray
      exact ⟨targetLabels label, (rayVectors label).symm⟩
    · rintro ⟨ray, rfl⟩
      obtain ⟨label, rfl⟩ := targetLabels.surjective ray
      exact ⟨sourceLabels label, rayVectors label⟩
  exact (integralFanClass_eq_iff source target).mpr
    (nonempty_integralRayFanEquiv_of_primitive_ray_sets source target sourceComplete sourceRegular
      sourceDeep targetComplete targetRegular targetDeep sourceBasis lattice raySets)

end BondalThomsen.ToricTransport
