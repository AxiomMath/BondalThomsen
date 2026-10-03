module

public import BondalThomsen.ProjectiveBundle.RayClassRigidity
public import BondalThomsen.ProjectiveBundle.NefSupport
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

namespace BondalThomsen.ToricTransport

open Module Set

variable {SourceLattice TargetLattice SourceAmbient TargetAmbient : Type*}
    [AddCommGroup SourceLattice] [AddCommGroup TargetLattice]
    [NormedAddCommGroup SourceAmbient] [NormedAddCommGroup TargetAmbient]
    [NormedSpace ℝ SourceAmbient] [NormedSpace ℝ TargetAmbient]
    {source_embedding : SourceLattice →+ SourceAmbient}
    {target_embedding : TargetLattice →+ TargetAmbient}

structure IntegralRayFanEquiv
    (source : TauCeti.Toric.Fan source_embedding)
    (target : TauCeti.Toric.Fan target_embedding) where
  lattice : SourceLattice ≃ₗ[ℤ] TargetLattice
  ambient : SourceAmbient ≃ₗ[ℝ] TargetAmbient
  embeddings : ∀ vector, ambient (source_embedding vector) = target_embedding (lattice vector)
  rays : source.Ray ≃ target.Ray
  ray_vectors : ∀ ray : source.Ray, lattice ray.val = (rays ray).val
  cones : ∀ cone : PointedCone ℝ SourceAmbient,
    cone ∈ source.cones ↔ PointedCone.map ambient.toLinearMap cone ∈ target.cones

variable {source : TauCeti.Toric.Fan source_embedding}
    {target : TauCeti.Toric.Fan target_embedding}

theorem map_hull_eq (linear : SourceAmbient →ₗ[ℝ] TargetAmbient) (vectors : Set SourceAmbient) :
    PointedCone.map linear (PointedCone.hull ℝ vectors) =
      PointedCone.hull ℝ (linear '' vectors) := by
  exact Submodule.map_span (linear.restrictScalars (Nonneg ℝ)) vectors

theorem map_symm_map (linear : SourceAmbient ≃ₗ[ℝ] TargetAmbient)
    (cone : PointedCone ℝ SourceAmbient) :
    PointedCone.map linear.symm.toLinearMap (PointedCone.map linear.toLinearMap cone) = cone := by
  ext point
  simp only [PointedCone.mem_map]
  constructor
  · rintro ⟨image, ⟨original, member, rfl⟩, equality⟩
    have original_eq : original = point := by
      change linear.symm (linear original) = point at equality
      simpa only [LinearEquiv.symm_apply_apply] using equality
    exact original_eq ▸ member
  · intro member
    exact ⟨linear point, ⟨point, member, rfl⟩, linear.symm_apply_apply point⟩

def IntegralRayFanEquiv.symm (equivalence : IntegralRayFanEquiv source target) :
    IntegralRayFanEquiv target source where
  lattice := equivalence.lattice.symm
  ambient := equivalence.ambient.symm
  embeddings vector := by
    have equality := equivalence.embeddings (equivalence.lattice.symm vector)
    rw [LinearEquiv.apply_symm_apply] at equality
    rw [← equality, LinearEquiv.symm_apply_apply]
  rays := equivalence.rays.symm
  ray_vectors ray := by
    have equality := equivalence.ray_vectors (equivalence.rays.symm ray)
    rw [Equiv.apply_symm_apply] at equality
    rw [← equality, LinearEquiv.symm_apply_apply]
  cones cone := by
    have membership := equivalence.cones (PointedCone.map equivalence.ambient.symm.toLinearMap cone)
    have inverse_map := map_symm_map equivalence.ambient.symm cone
    simp only [LinearEquiv.symm_symm] at inverse_map
    rw [inverse_map] at membership
    exact membership.symm

theorem IntegralRayFanEquiv.map_cone_basis (equivalence : IntegralRayFanEquiv source target)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ SourceLattice)
    (cone_basis : source.IsConeBasis basis) :
    target.IsConeBasis (basis.map equivalence.lattice) := by
  have member := (equivalence.cones _).mp cone_basis
  change PointedCone.hull ℝ (Set.range (fun index => target_embedding
    ((basis.map equivalence.lattice) index))) ∈ target.cones
  rw [map_hull_eq] at member
  have same_generators : equivalence.ambient ''
      Set.range (fun index => source_embedding (basis index)) =
        Set.range (fun index => target_embedding ((basis.map equivalence.lattice) index)) := by
    ext vector
    constructor
    · rintro ⟨_, ⟨index, rfl⟩, rfl⟩
      refine ⟨index, ?_⟩
      change target_embedding ((basis.map equivalence.lattice) index) =
        equivalence.ambient (source_embedding (basis index))
      rw [Basis.map_apply, equivalence.embeddings]
    · rintro ⟨index, rfl⟩
      exact ⟨source_embedding (basis index), ⟨index, rfl⟩,
        by change equivalence.ambient (source_embedding (basis index)) =
             target_embedding ((basis.map equivalence.lattice) index)
           rw [Basis.map_apply, equivalence.embeddings]⟩
  change PointedCone.hull ℝ (equivalence.ambient ''
    Set.range (fun index => source_embedding (basis index))) ∈ target.cones at member
  simpa only [same_generators] using member

noncomputable def IntegralRayFanEquiv.divisorEquiv (equivalence : IntegralRayFanEquiv source target) :
    source.InvariantRayDivisor ≃+ target.InvariantRayDivisor := Finsupp.domCongr equivalence.rays

@[simp] theorem IntegralRayFanEquiv.divisorEquiv_apply
    (equivalence : IntegralRayFanEquiv source target) (divisor : source.InvariantRayDivisor)
    (ray : source.Ray) : equivalence.divisorEquiv divisor (equivalence.rays ray) = divisor ray := by
  simp only [IntegralRayFanEquiv.divisorEquiv, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

theorem IntegralRayFanEquiv.divisorEquiv_principal
    (equivalence : IntegralRayFanEquiv source target) (character : SourceLattice →+ ℤ) :
    equivalence.divisorEquiv (source.principalRayDivisor character) =
      target.principalRayDivisor (character.comp equivalence.lattice.symm.toAddMonoidHom) := by
  ext target_ray
  obtain ⟨ray, rfl⟩ := equivalence.rays.surjective target_ray
  rw [equivalence.divisorEquiv_apply]
  change character ray.val = character (equivalence.lattice.symm (equivalence.rays ray).val)
  rw [← equivalence.ray_vectors, LinearEquiv.symm_apply_apply]

theorem IntegralRayFanEquiv.principal_range_map_eq
    (equivalence : IntegralRayFanEquiv source target) :
    AddSubgroup.map equivalence.divisorEquiv.toAddMonoidHom source.principalRayDivisor.range =
      target.principalRayDivisor.range := by
  ext divisor
  constructor
  · rintro ⟨_, ⟨character, rfl⟩, rfl⟩
    exact ⟨character.comp equivalence.lattice.symm.toAddMonoidHom,
      equivalence.divisorEquiv_principal character |>.symm⟩
  · rintro ⟨character, rfl⟩
    refine ⟨source.principalRayDivisor (character.comp equivalence.lattice.toAddMonoidHom),
      ⟨character.comp equivalence.lattice.toAddMonoidHom, rfl⟩, ?_⟩
    change equivalence.divisorEquiv (source.principalRayDivisor _) = _
    rw [equivalence.divisorEquiv_principal]
    congr 1
    ext vector
    exact congrArg character (equivalence.lattice.apply_symm_apply vector)

noncomputable def IntegralRayFanEquiv.classEquiv (equivalence : IntegralRayFanEquiv source target) :
    source.InvariantRayDivisorClass ≃+ target.InvariantRayDivisorClass :=
  QuotientAddGroup.congr source.principalRayDivisor.range target.principalRayDivisor.range
    equivalence.divisorEquiv equivalence.principal_range_map_eq

@[simp] theorem IntegralRayFanEquiv.classEquiv_mk
    (equivalence : IntegralRayFanEquiv source target) (divisor : source.InvariantRayDivisor) :
    equivalence.classEquiv (source.invariantRayDivisorClass divisor) =
      target.invariantRayDivisorClass (equivalence.divisorEquiv divisor) := by
  rfl

theorem IntegralRayFanEquiv.basisRay_map (equivalence : IntegralRayFanEquiv source target)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ SourceLattice)
    (cone_basis : source.IsConeBasis basis) (index : Fin dimension) :
    target.basisRay (basis.map equivalence.lattice) (equivalence.map_cone_basis basis cone_basis) index =
      equivalence.rays (source.basisRay basis cone_basis index) := by
  apply Subtype.ext
  rw [target.basisRay_val, Basis.map_apply, ← equivalence.ray_vectors, source.basisRay_val]

theorem IntegralRayFanEquiv.coneDivisorCharacter_map
    (equivalence : IntegralRayFanEquiv source target) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ SourceLattice) (cone_basis : source.IsConeBasis basis)
    (divisor : source.InvariantRayDivisor) :
    (target.coneDivisorCharacter (basis.map equivalence.lattice)
      (equivalence.map_cone_basis basis cone_basis) (equivalence.divisorEquiv divisor)).comp
        equivalence.lattice.toAddMonoidHom = source.coneDivisorCharacter basis cone_basis divisor := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  change target.coneDivisorCharacter (basis.map equivalence.lattice)
    (equivalence.map_cone_basis basis cone_basis) (equivalence.divisorEquiv divisor)
      (equivalence.lattice (basis index)) = source.coneDivisorCharacter basis cone_basis divisor (basis index)
  rw [← Basis.map_apply, target.coneDivisorCharacter_basis, source.coneDivisorCharacter_basis,
    equivalence.basisRay_map, equivalence.divisorEquiv_apply]

section Support

theorem IntegralRayFanEquiv.hasRaySupportInequalities_map
    (equivalence : IntegralRayFanEquiv source target) (divisor : source.InvariantRayDivisor)
    (support : source.HasRaySupportInequalities divisor) :
    target.HasRaySupportInequalities (equivalence.divisorEquiv divisor) := by
  intro dimension target_basis target_cone target_ray
  let basis := target_basis.map equivalence.lattice.symm
  have cone_basis : source.IsConeBasis basis := equivalence.symm.map_cone_basis target_basis target_cone
  have roundtrip : basis.map equivalence.lattice = target_basis := by
    ext index
    change equivalence.lattice (equivalence.lattice.symm (target_basis index)) = target_basis index
    exact equivalence.lattice.apply_symm_apply _
  let ray := equivalence.rays.symm target_ray
  have bound := support dimension basis cone_basis ray
  have mapped := congrArg (fun character : SourceLattice →+ ℤ => character ray.val)
    (equivalence.coneDivisorCharacter_map basis cone_basis divisor)
  change target.coneDivisorCharacter (basis.map equivalence.lattice)
    (equivalence.map_cone_basis basis cone_basis) (equivalence.divisorEquiv divisor)
      (equivalence.lattice ray.val) = source.coneDivisorCharacter basis cone_basis divisor ray.val at mapped
  have ray_eq : equivalence.rays ray = target_ray := equivalence.rays.apply_symm_apply _
  simp only [roundtrip] at mapped
  rw [equivalence.ray_vectors, ray_eq] at mapped
  have coefficient := equivalence.divisorEquiv_apply divisor ray
  rw [ray_eq] at coefficient
  rw [coefficient, mapped]
  exact bound

theorem IntegralRayFanEquiv.hasRaySupportInequalities_iff
    (equivalence : IntegralRayFanEquiv source target) (divisor : source.InvariantRayDivisor) :
    target.HasRaySupportInequalities (equivalence.divisorEquiv divisor) ↔
      source.HasRaySupportInequalities divisor := by
  constructor
  · intro support
    have original := equivalence.symm.hasRaySupportInequalities_map (equivalence.divisorEquiv divisor) support
    have inverse : equivalence.symm.divisorEquiv (equivalence.divisorEquiv divisor) = divisor := by
      change (Finsupp.domCongr equivalence.rays.symm)
        ((Finsupp.domCongr equivalence.rays) divisor) = divisor
      rw [← Finsupp.domCongr_symm]
      exact AddEquiv.symm_apply_apply _ _
    rwa [inverse] at original
  · exact equivalence.hasRaySupportInequalities_map divisor

end Support

end BondalThomsen.ToricTransport

