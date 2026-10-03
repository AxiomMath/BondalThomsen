module

public import BondalThomsen.Ports.MiyaokaMori.ModulesTensorPower
public import BondalThomsen.Ports.MiyaokaMori.NonvanishingLocusIsoInvariant

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry

def IsAmple {X : Scheme.{u}} (L : X.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] : Prop :=
  CompactSpace X ∧
    ∀ x : X, ∃ (m : ℕ) (_ : 0 < m) (s : Γ(Scheme.Modules.tensorPow L m, ⊤)),
      x ∈ (Scheme.Modules.tensorPow L m).nonvanishingLocus s ∧
        IsAffineOpen ((Scheme.Modules.tensorPow L m).nonvanishingLocus s)

def IsAmpleAt {X : Scheme.{u}} (L : X.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] (x : X) : Prop :=
  ∃ (m : ℕ) (_ : 0 < m) (s : Γ(Scheme.Modules.tensorPow L m, ⊤)),
    x ∈ (Scheme.Modules.tensorPow L m).nonvanishingLocus s ∧
      IsAffineOpen ((Scheme.Modules.tensorPow L m).nonvanishingLocus s)

theorem IsAmpleAt.of_iso {X : Scheme.{u}} {L L' : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L']
    (e : L ≅ L') {x : X} (h : IsAmpleAt L x) : IsAmpleAt L' x := by
  obtain ⟨m, hm, s, hxs, haff⟩ := h
  refine ⟨m, hm, (Scheme.Modules.tensorPowMapIso e m).hom.app ⊤ s, ?_, ?_⟩
  · exact (Scheme.Modules.mem_nonvanishingLocus_iso
      (Scheme.Modules.tensorPowMapIso e m) s x).mpr hxs
  · rw [Scheme.Modules.nonvanishingLocus_iso]
    exact haff

theorem IsAmple.of_iso {X : Scheme.{u}} {L L' : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L']
    (e : L ≅ L') (h : IsAmple L) : IsAmple L' := by
  obtain ⟨hcpt, hcov⟩ := h
  refine ⟨hcpt, fun x => ?_⟩
  obtain ⟨m, hm, s, hxs, haff⟩ := hcov x
  refine ⟨m, hm, (Scheme.Modules.tensorPowMapIso e m).hom.app ⊤ s, ?_, ?_⟩
  · exact (Scheme.Modules.mem_nonvanishingLocus_iso
      (Scheme.Modules.tensorPowMapIso e m) s x).mpr hxs
  · rw [Scheme.Modules.nonvanishingLocus_iso]
    exact haff

theorem isAmple_iff_of_iso {X : Scheme.{u}} {L L' : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L'] (e : L ≅ L') :
    IsAmple L ↔ IsAmple L' := ⟨IsAmple.of_iso e, IsAmple.of_iso e.symm⟩

end AlgebraicGeometry
