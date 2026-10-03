module

public import BondalThomsen.DeepFan.UnconditionalRigidity
public import BondalThomsen.Fan.SignedRayFanReconstruction
public import BondalThomsen.Toric.Scheme.FanEquivSchemeIso

@[expose] public section

open AlgebraicGeometry CategoryTheory Module

namespace BondalThomsen.ToricTransport

universe latticeUniverse

variable {SourceLattice TargetLattice : Type latticeUniverse}
    {SourceAmbient TargetAmbient : Type*}
    [AddCommGroup SourceLattice] [AddCommGroup TargetLattice]
    [NormedAddCommGroup SourceAmbient] [NormedAddCommGroup TargetAmbient]
    [NormedSpace ℝ SourceAmbient] [NormedSpace ℝ TargetAmbient]
    {source_embedding : SourceLattice →+ SourceAmbient}
    {target_embedding : TargetLattice →+ TargetAmbient}

noncomputable def latticeEquivReal
    (source : TauCeti.Toric.Fan source_embedding) (target : TauCeti.Toric.Fan target_embedding)
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice) : SourceAmbient ≃ₗ[ℝ] TargetAmbient :=
  LinearEquiv.ofLinearMap
    (source.lattice.extend target_embedding lattice.toAddMonoidHom)
    (target.lattice.extend source_embedding lattice.symm.toAddMonoidHom)
    (by
      rw [TauCeti.Toric.IsIntegralLattice.extend_comp]
      have identity : lattice.toAddMonoidHom.comp lattice.symm.toAddMonoidHom =
          AddMonoidHom.id TargetLattice := by
        ext vector
        exact lattice.apply_symm_apply vector
      rw [identity, TauCeti.Toric.IsIntegralLattice.extend_id])
    (by
      rw [TauCeti.Toric.IsIntegralLattice.extend_comp]
      have identity : lattice.symm.toAddMonoidHom.comp lattice.toAddMonoidHom =
          AddMonoidHom.id SourceLattice := by
        ext vector
        exact lattice.symm_apply_apply vector
      rw [identity, TauCeti.Toric.IsIntegralLattice.extend_id])

@[simp] theorem latticeEquivReal_embedding
    (source : TauCeti.Toric.Fan source_embedding) (target : TauCeti.Toric.Fan target_embedding)
    (lattice : SourceLattice ≃ₗ[ℤ] TargetLattice) (vector : SourceLattice) :
    latticeEquivReal source target lattice (source_embedding vector) =
      target_embedding (lattice vector) := by
  simp [latticeEquivReal, LinearEquiv.coe_ofLinearMap]

end BondalThomsen.ToricTransport

