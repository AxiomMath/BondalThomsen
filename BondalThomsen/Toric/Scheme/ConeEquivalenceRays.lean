module

public import BondalThomsen.Toric.Scheme.RayEquivalenceRigidity
public import BondalThomsen.Ports.TauCeti.Algebra.Module.Primitive

@[expose] public section

namespace BondalThomsen.ToricTransport

open Module Set

variable {SourceLattice TargetLattice SourceAmbient TargetAmbient : Type*}
    [AddCommGroup SourceLattice] [AddCommGroup TargetLattice]
    [NormedAddCommGroup SourceAmbient] [NormedAddCommGroup TargetAmbient]
    [NormedSpace ℝ SourceAmbient] [NormedSpace ℝ TargetAmbient]
    {source_embedding : SourceLattice →+ SourceAmbient}
    {target_embedding : TargetLattice →+ TargetAmbient}
    {source : TauCeti.Toric.Fan source_embedding}
    {target : TauCeti.Toric.Fan target_embedding}

theorem map_primitive_ray_hull
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector))
    (vector : SourceLattice) :
    PointedCone.map ambient.toLinearMap (PointedCone.hull ℝ {source_embedding vector}) =
      PointedCone.hull ℝ {target_embedding (lattice vector)} := by
  rw [map_hull_eq]
  simp only [Set.image_singleton]
  change PointedCone.hull ℝ {ambient (source_embedding vector)} = _
  rw [embeddings]

theorem primitive_ray_membership_iff
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector))
    (cones : ∀ cone : PointedCone ℝ SourceAmbient,
      cone ∈ source.cones ↔ PointedCone.map ambient.toLinearMap cone ∈ target.cones)
    (vector : SourceLattice) :
    (TauCeti.IsPrimitive (lattice vector) ∧
      PointedCone.hull ℝ {target_embedding (lattice vector)} ∈ target.cones) ↔
      (TauCeti.IsPrimitive vector ∧
        PointedCone.hull ℝ {source_embedding vector} ∈ source.cones) := by
  rw [lattice.isPrimitive_iff, ← map_primitive_ray_hull lattice ambient embeddings vector,
    ← cones]

def coneRayEquiv
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector))
    (cones : ∀ cone : PointedCone ℝ SourceAmbient,
      cone ∈ source.cones ↔ PointedCone.map ambient.toLinearMap cone ∈ target.cones) :
    source.Ray ≃ target.Ray :=
  Equiv.subtypeEquiv lattice.toEquiv
    (fun vector => (primitive_ray_membership_iff lattice ambient embeddings cones vector).symm)

@[simp] theorem coneRayEquiv_val
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector))
    (cones : ∀ cone : PointedCone ℝ SourceAmbient,
      cone ∈ source.cones ↔ PointedCone.map ambient.toLinearMap cone ∈ target.cones)
    (ray : source.Ray) :
    (coneRayEquiv lattice ambient embeddings cones ray).val = lattice ray.val := rfl

@[simp] theorem coneRayEquiv_symm_val
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector))
    (cones : ∀ cone : PointedCone ℝ SourceAmbient,
      cone ∈ source.cones ↔ PointedCone.map ambient.toLinearMap cone ∈ target.cones)
    (ray : target.Ray) :
    ((coneRayEquiv lattice ambient embeddings cones).symm ray).val = lattice.symm ray.val := rfl

def IntegralRayFanEquiv.ofConeTransport
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice)
    (ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector))
    (cones : ∀ cone : PointedCone ℝ SourceAmbient,
      cone ∈ source.cones ↔ PointedCone.map ambient.toLinearMap cone ∈ target.cones) :
    IntegralRayFanEquiv source target where
  lattice := lattice
  ambient := ambient
  embeddings := embeddings
  rays := coneRayEquiv lattice ambient embeddings cones
  ray_vectors _ := rfl
  cones := cones

end BondalThomsen.ToricTransport
