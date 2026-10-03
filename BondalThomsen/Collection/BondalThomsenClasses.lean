module

public import BondalThomsen.FloorClasses.FloorClassFiniteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.NhdsWithin
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Picard
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace TauCeti.Toric.Fan

open TauCeti.AlgebraicGeometry

universe u

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

def bondalThomsenClasses (fan : TauCeti.Toric.Fan embedding) :
    Set fan.InvariantRayDivisorClass := Set.range fan.floorRayDivisorClass

abbrev BondalThomsenClass (fan : TauCeti.Toric.Fan embedding) :=
  ↥fan.bondalThomsenClasses

theorem bondalThomsenClasses_finite {Index : Type*} [Fintype Index]
    (fan : TauCeti.Toric.Fan embedding) (basis : Module.Basis Index ℤ Lattice) :
    fan.bondalThomsenClasses.Finite := fan.floorRayDivisorClass_range_finite basis

instance bondalThomsenClassFinite [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : TauCeti.Toric.Fan embedding) : Finite fan.BondalThomsenClass :=
  (fan.bondalThomsenClasses_finite (Module.finBasis ℤ Lattice)).to_subtype

noncomputable instance bondalThomsenClassFintype [Module.Free ℤ Lattice]
    [Module.Finite ℤ Lattice] (fan : TauCeti.Toric.Fan embedding) :
    Fintype fan.BondalThomsenClass := Fintype.ofFinite _

noncomputable def bondalThomsenClassOfPairing (fan : TauCeti.Toric.Fan embedding)
    (pairing : Lattice →+ ℚ) : fan.BondalThomsenClass :=
  ⟨fan.floorRayDivisorClass pairing, ⟨pairing, rfl⟩⟩

@[simp] theorem bondalThomsenClassOfPairing_val (fan : TauCeti.Toric.Fan embedding)
    (pairing : Lattice →+ ℚ) :
    (fan.bondalThomsenClassOfPairing pairing).val = fan.floorRayDivisorClass pairing := rfl

theorem bondalThomsenClassOfPairing_surjective (fan : TauCeti.Toric.Fan embedding) :
    Function.Surjective fan.bondalThomsenClassOfPairing := by
  rintro ⟨divisor_class, pairing, equality⟩
  exact ⟨pairing, Subtype.ext equality⟩

theorem bondalThomsenClassOfPairing_add_integral (fan : TauCeti.Toric.Fan embedding)
    (pairing : Lattice →+ ℚ) (character : Lattice →+ ℤ) :
    fan.bondalThomsenClassOfPairing (pairing + (Int.castAddHom ℚ).comp character) =
      fan.bondalThomsenClassOfPairing pairing :=
  Subtype.ext (fan.floorRayDivisorClass_add_integral pairing character)

section Realization

variable (fan : TauCeti.Toric.Fan embedding) {scheme : _root_.AlgebraicGeometry.Scheme.{u}}

noncomputable def invariantDivisorClassToLineBundleClass
    (realization : fan.InvariantRayDivisor →+ Additive (LineBundleClass scheme))
    (principal_trivial : ∀ character : Lattice →+ ℤ,
      realization (fan.principalRayDivisor character) = 0) :
    fan.InvariantRayDivisorClass →+ Additive (LineBundleClass scheme) :=
  QuotientAddGroup.lift fan.principalRayDivisor.range realization (by
    rintro divisor ⟨character, rfl⟩
    exact principal_trivial character)

@[simp] theorem invariantDivisorClassToLineBundleClass_apply
    (realization : fan.InvariantRayDivisor →+ Additive (LineBundleClass scheme))
    (principal_trivial : ∀ character : Lattice →+ ℤ,
      realization (fan.principalRayDivisor character) = 0)
    (divisor : fan.InvariantRayDivisor) :
    fan.invariantDivisorClassToLineBundleClass realization principal_trivial
      (fan.invariantRayDivisorClass divisor) = realization divisor :=
  QuotientAddGroup.lift_mk' _ _ divisor

end Realization

section CartierRealization

open TauCeti.AlgebraicGeometry.Scheme

variable (fan : TauCeti.Toric.Fan embedding) {scheme : _root_.AlgebraicGeometry.Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral scheme]

noncomputable def cartierInvariantDivisorClassRealization
    (cartier_map : fan.InvariantRayDivisor →+ CartierDivisor scheme)
    (principal_compatibility : ∀ character : Lattice →+ ℤ,
      ∃ rational_function : scheme.functionFieldˣ,
        cartier_map (fan.principalRayDivisor character) =
          principalCartierDivisor scheme rational_function) :
    fan.InvariantRayDivisorClass →+ Additive (LineBundleClass scheme) :=
  fan.invariantDivisorClassToLineBundleClass
    (CartierDivisor.toLineBundleClassHom.comp cartier_map) (by
      intro character
      obtain ⟨rational_function, principal⟩ := principal_compatibility character
      change Additive.ofMul (cartier_map (fan.principalRayDivisor character)).toLineBundleClass = 0
      rw [principal, CartierDivisor.toLineBundleClass_principalCartierDivisor]
      rfl)

end CartierRealization

end TauCeti.Toric.Fan
