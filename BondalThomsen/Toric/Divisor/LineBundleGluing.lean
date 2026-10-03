module

public import BondalThomsen.Toric.Scheme.TransitionUnits
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.Scheme
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Multiplicative

namespace BondalThomsen

noncomputable def affineGlobalSectionsEquiv (CoordinateRing : Type*) [CommRing CoordinateRing] :
    CoordinateRing ≃+* Γ(Spec (CommRingCat.of CoordinateRing), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of CoordinateRing)).commRingCatIsoToRingEquiv.symm

end BondalThomsen

