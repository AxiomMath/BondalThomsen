module

public import BondalThomsen.LineBundle.AmpleLineBundleTensorLocalDescent

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace BondalThomsen

variable {source target : Scheme.{0}}

def ampleTensorPowerPullbackSection (map : source ⟶ target) (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf]
    (exponent : ℕ) (section_value : Γ(Scheme.Modules.tensorPow sheaf exponent, ⊤)) :
    Γ(Scheme.Modules.tensorPow ((Scheme.Modules.pullback map).obj sheaf) exponent, ⊤) :=
  Scheme.Modules.Hom.app (ampleInvertibleTensorPowerPullbackIso map sheaf exponent).hom ⊤
    (amplePullbackGlobalSection map (Scheme.Modules.tensorPow sheaf exponent) section_value)

theorem ampleTensorPowerPullbackSection_nonvanishingLocus (map : source ⟶ target)
    (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf]
    (exponent : ℕ) (section_value : Γ(Scheme.Modules.tensorPow sheaf exponent, ⊤)) :
    (Scheme.Modules.tensorPow ((Scheme.Modules.pullback map).obj sheaf) exponent).nonvanishingLocus
        (ampleTensorPowerPullbackSection map sheaf exponent section_value) =
      map ⁻¹ᵁ (Scheme.Modules.tensorPow sheaf exponent).nonvanishingLocus section_value := by
  exact (Scheme.Modules.nonvanishingLocus_iso
    (ampleInvertibleTensorPowerPullbackIso map sheaf exponent)
    (amplePullbackGlobalSection map (Scheme.Modules.tensorPow sheaf exponent) section_value)).trans
      (amplePullbackGlobalSection_nonvanishingLocus map
        (Scheme.Modules.tensorPow sheaf exponent) section_value)

end BondalThomsen

namespace AlgebraicGeometry

variable {source target : Scheme.{0}}

theorem IsAmpleAt.pullback_of_isAffineHom (map : source ⟶ target) [IsAffineHom map]
    (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf]
    (point : source) (ample : IsAmpleAt sheaf (map point)) :
    IsAmpleAt ((Scheme.Modules.pullback map).obj sheaf) point := by
  obtain ⟨exponent, positive, section_value, contains, affine⟩ := ample
  refine ⟨exponent, positive,
    BondalThomsen.ampleTensorPowerPullbackSection map sheaf exponent section_value, ?_, ?_⟩
  · rw [BondalThomsen.ampleTensorPowerPullbackSection_nonvanishingLocus]
    exact contains
  · rw [BondalThomsen.ampleTensorPowerPullbackSection_nonvanishingLocus]
    exact affine.preimage map

theorem IsAmple.pullback_of_isAffineHom (map : source ⟶ target) [IsAffineHom map]
    (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf]
    (ample : IsAmple sheaf) : IsAmple ((Scheme.Modules.pullback map).obj sheaf) := by
  let : CompactSpace target := ample.1
  refine ⟨QuasiCompact.compactSpace_of_compactSpace map, fun point => ?_⟩
  exact IsAmpleAt.pullback_of_isAffineHom map sheaf point (ample.2 (map point))

theorem IsAmpleAt.pullback_of_isClosedImmersion (map : source ⟶ target) [IsClosedImmersion map]
    (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf]
    (point : source) (ample : IsAmpleAt sheaf (map point)) :
    IsAmpleAt ((Scheme.Modules.pullback map).obj sheaf) point :=
  IsAmpleAt.pullback_of_isAffineHom map sheaf point ample

theorem IsAmple.pullback_of_isClosedImmersion (map : source ⟶ target) [IsClosedImmersion map]
    (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf]
    (ample : IsAmple sheaf) : IsAmple ((Scheme.Modules.pullback map).obj sheaf) :=
  IsAmple.pullback_of_isAffineHom map sheaf ample

end AlgebraicGeometry

