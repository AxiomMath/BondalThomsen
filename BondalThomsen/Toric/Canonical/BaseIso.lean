module

public import BondalThomsen.Toric.Canonical.Invertible
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import BondalThomsen.Fan.CompleteFanGlobalFunctions

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace BondalThomsen.CanonicalBaseIso

noncomputable def differentialBaseIso {Base NewBase Coefficients : CommRingCat}
    (baseMap : Base ⟶ Coefficients) (newMap : NewBase ⟶ Coefficients)
    (comparison : NewBase ≅ Base) (compatible : comparison.hom ≫ baseMap = newMap) :
    CommRingCat.KaehlerDifferential baseMap ≅ CommRingCat.KaehlerDifferential newMap := by
  have forwardSquare : comparison.inv ≫ newMap = baseMap ≫ 𝟙 Coefficients := by
    rw [← compatible, ← Category.assoc, comparison.inv_hom_id]
    simp
  have reverseSquare : comparison.hom ≫ baseMap = newMap ≫ 𝟙 Coefficients := by
    simpa using compatible
  let forward := CommRingCat.KaehlerDifferential.map forwardSquare ≫
    ((ModuleCat.restrictScalarsId Coefficients).app (CommRingCat.KaehlerDifferential newMap)).hom
  let reverse := CommRingCat.KaehlerDifferential.map reverseSquare ≫
    ((ModuleCat.restrictScalarsId Coefficients).app (CommRingCat.KaehlerDifferential baseMap)).hom
  refine ⟨forward, reverse, ?_, ?_⟩
  · apply CommRingCat.KaehlerDifferential.ext
    intro coefficient
    change (CommRingCat.KaehlerDifferential.map reverseSquare)
      ((CommRingCat.KaehlerDifferential.map forwardSquare)
        (CommRingCat.KaehlerDifferential.d coefficient)) = _
    rw [CommRingCat.KaehlerDifferential.map_d, CommRingCat.KaehlerDifferential.map_d]
    rfl
  · apply CommRingCat.KaehlerDifferential.ext
    intro coefficient
    change (CommRingCat.KaehlerDifferential.map forwardSquare)
      ((CommRingCat.KaehlerDifferential.map reverseSquare)
        (CommRingCat.KaehlerDifferential.d coefficient)) = _
    rw [CommRingCat.KaehlerDifferential.map_d, CommRingCat.KaehlerDifferential.map_d]
    rfl

theorem differentialBaseIso_d {Base NewBase Coefficients : CommRingCat}
    (baseMap : Base ⟶ Coefficients) (newMap : NewBase ⟶ Coefficients)
    (comparison : NewBase ≅ Base) (compatible : comparison.hom ≫ baseMap = newMap)
    (coefficient : Coefficients) :
    (differentialBaseIso baseMap newMap comparison compatible).hom
        (CommRingCat.KaehlerDifferential.d coefficient) =
      CommRingCat.KaehlerDifferential.d coefficient := by
  have forwardSquare : comparison.inv ≫ newMap = baseMap ≫ 𝟙 Coefficients := by
    rw [← compatible, ← Category.assoc, comparison.inv_hom_id]
    simp
  change (CommRingCat.KaehlerDifferential.map forwardSquare)
    (CommRingCat.KaehlerDifferential.d coefficient) = _
  exact CommRingCat.KaehlerDifferential.map_d _ _

end BondalThomsen.CanonicalBaseIso

