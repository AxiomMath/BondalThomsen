module

public import BondalThomsen.Toric.Scheme.RayEquivalenceRigidity
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Scheme

@[expose] public section

open AlgebraicGeometry CategoryTheory

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ToricTransport

universe latticeUniverse

variable {SourceLattice TargetLattice : Type latticeUniverse}
    {SourceAmbient TargetAmbient : Type*}
    [AddCommGroup SourceLattice] [AddCommGroup TargetLattice]
    [NormedAddCommGroup SourceAmbient] [NormedAddCommGroup TargetAmbient]
    [NormedSpace ℝ SourceAmbient] [NormedSpace ℝ TargetAmbient]
    {source_embedding : SourceLattice →+ SourceAmbient}
    {target_embedding : TargetLattice →+ TargetAmbient}
    {source : TauCeti.Toric.Fan source_embedding}
    {target : TauCeti.Toric.Fan target_embedding}

def IntegralRayFanEquiv.toFanHom (equivalence : IntegralRayFanEquiv source target) :
    TauCeti.Toric.FanHom source target where
  latticeMap := equivalence.lattice.toAddMonoidHom
  realMap := equivalence.ambient.toLinearMap
  map_lattice := equivalence.embeddings
  map_cone cone member :=
    ⟨PointedCone.map equivalence.ambient.toLinearMap cone,
      (equivalence.cones cone).mp member, le_rfl⟩

@[simp] theorem IntegralRayFanEquiv.toFanHom_latticeMap
    (equivalence : IntegralRayFanEquiv source target) :
    equivalence.toFanHom.latticeMap = equivalence.lattice.toAddMonoidHom := rfl

@[simp] theorem IntegralRayFanEquiv.toFanHom_realMap
    (equivalence : IntegralRayFanEquiv source target) :
    equivalence.toFanHom.realMap = equivalence.ambient.toLinearMap := rfl

@[simp] theorem IntegralRayFanEquiv.symm_toFanHom_comp
    (equivalence : IntegralRayFanEquiv source target) :
    equivalence.symm.toFanHom.comp equivalence.toFanHom = TauCeti.Toric.FanHom.id source := by
  apply TauCeti.Toric.FanHom.ext
  apply AddMonoidHom.ext
  intro vector
  exact equivalence.lattice.symm_apply_apply vector

@[simp] theorem IntegralRayFanEquiv.toFanHom_comp_symm
    (equivalence : IntegralRayFanEquiv source target) :
    equivalence.toFanHom.comp equivalence.symm.toFanHom = TauCeti.Toric.FanHom.id target := by
  apply TauCeti.Toric.FanHom.ext
  apply AddMonoidHom.ext
  intro vector
  exact equivalence.lattice.apply_symm_apply vector

noncomputable def IntegralRayFanEquiv.schemeMap
    (equivalence : IntegralRayFanEquiv source target)
    (source_regular : source.IsRegular) (target_regular : target.IsRegular) :
    source.algebraicRealization 𝕜 source_regular ⟶ target.algebraicRealization 𝕜 target_regular :=
  equivalence.toFanHom.algebraicMap 𝕜 source_regular target_regular

theorem IntegralRayFanEquiv.schemeMap_comp_symm
    (equivalence : IntegralRayFanEquiv source target)
    (source_regular : source.IsRegular) (target_regular : target.IsRegular) :
    equivalence.schemeMap 𝕜 source_regular target_regular ≫
      equivalence.symm.schemeMap 𝕜 target_regular source_regular =
        𝟙 (source.algebraicRealization 𝕜 source_regular) := by
  change equivalence.toFanHom.algebraicMap 𝕜 source_regular target_regular ≫
    equivalence.symm.toFanHom.algebraicMap 𝕜 target_regular source_regular = _
  rw [← TauCeti.Toric.FanHom.algebraicMap_comp, equivalence.symm_toFanHom_comp,
    TauCeti.Toric.FanHom.algebraicMap_id]

theorem IntegralRayFanEquiv.symm_schemeMap_comp
    (equivalence : IntegralRayFanEquiv source target)
    (source_regular : source.IsRegular) (target_regular : target.IsRegular) :
    equivalence.symm.schemeMap 𝕜 target_regular source_regular ≫
      equivalence.schemeMap 𝕜 source_regular target_regular =
        𝟙 (target.algebraicRealization 𝕜 target_regular) := by
  change equivalence.symm.toFanHom.algebraicMap 𝕜 target_regular source_regular ≫
    equivalence.toFanHom.algebraicMap 𝕜 source_regular target_regular = _
  rw [← TauCeti.Toric.FanHom.algebraicMap_comp, equivalence.toFanHom_comp_symm,
    TauCeti.Toric.FanHom.algebraicMap_id]

noncomputable def IntegralRayFanEquiv.schemeIso
    (equivalence : IntegralRayFanEquiv source target)
    (source_regular : source.IsRegular) (target_regular : target.IsRegular) :
    source.algebraicRealization 𝕜 source_regular ≅ target.algebraicRealization 𝕜 target_regular where
  hom := equivalence.schemeMap 𝕜 source_regular target_regular
  inv := equivalence.symm.schemeMap 𝕜 target_regular source_regular
  hom_inv_id := equivalence.schemeMap_comp_symm 𝕜 source_regular target_regular
  inv_hom_id := equivalence.symm_schemeMap_comp 𝕜 source_regular target_regular

@[simp] theorem IntegralRayFanEquiv.schemeIso_hom
    (equivalence : IntegralRayFanEquiv source target)
    (source_regular : source.IsRegular) (target_regular : target.IsRegular) :
    (equivalence.schemeIso 𝕜 source_regular target_regular).hom =
      equivalence.schemeMap 𝕜 source_regular target_regular := rfl

@[simp] theorem IntegralRayFanEquiv.schemeIso_inv
    (equivalence : IntegralRayFanEquiv source target)
    (source_regular : source.IsRegular) (target_regular : target.IsRegular) :
    (equivalence.schemeIso 𝕜 source_regular target_regular).inv =
      equivalence.symm.schemeMap 𝕜 target_regular source_regular := rfl

variable {𝕜} in
instance IntegralRayFanEquiv.schemeMap_isIso
    (equivalence : IntegralRayFanEquiv source target)
    (source_regular : source.IsRegular) (target_regular : target.IsRegular) :
    IsIso (equivalence.schemeMap 𝕜 source_regular target_regular) := by
  change IsIso (equivalence.schemeIso 𝕜 source_regular target_regular).hom
  infer_instance

end BondalThomsen.ToricTransport
