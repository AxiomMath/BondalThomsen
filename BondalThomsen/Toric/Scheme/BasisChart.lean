module

public import BondalThomsen.Toric.Scheme.FiniteType
public import BondalThomsen.Fan.ConeCoordinates
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem mem_dualSemigroup_basisCone_iff (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (character : Lattice →+ ℤ) :
    character ∈ dualSemigroup fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) ↔
      ∀ index, 0 ≤ character (basis index) := by
  have image_eq : embedding '' Set.range basis =
      Set.range (fun index => embedding (basis index)) := by
    ext point
    simp
  simpa only [image_eq, Set.forall_mem_range] using
    mem_dualSemigroup_hull_image fan.lattice (Set.range basis) character

noncomputable def basisConeDualSemigroupEquiv (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) :
    dualSemigroup fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) ≃+
        (Fin dimension →₀ ℕ) := by
  classical
  exact {
    toFun := fun character => Finsupp.equivFunOnFinite.symm
      (fun index => ((character : Lattice →+ ℤ) (basis index)).toNat)
    invFun := fun coordinates => ⟨(basis.constr ℤ (fun index => (coordinates index : ℤ))).toAddMonoidHom,
      (fan.mem_dualSemigroup_basisCone_iff basis _).mpr (fun index => by simp)⟩
    left_inv := fun character => by
      have nonnegative := (fan.mem_dualSemigroup_basisCone_iff basis _).mp character.property
      apply Subtype.ext
      apply AddMonoidHom.toIntLinearMap_injective
      apply basis.ext
      intro index
      simp [nonnegative index]
    right_inv := fun coordinates => by
      ext index
      simp
    map_add' := fun first second => by
      have first_nonnegative := (fan.mem_dualSemigroup_basisCone_iff basis _).mp first.property
      have second_nonnegative := (fan.mem_dualSemigroup_basisCone_iff basis _).mp second.property
      ext index
      simp [Int.toNat_add (first_nonnegative index) (second_nonnegative index)] }

noncomputable def basisConeCoordinateRingEquiv (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) :
    affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) ≃ₐ[𝕜]
        MvPolynomial (Fin dimension) 𝕜 :=
  (MonoidAlgebra.domCongr (R := 𝕜) (A := 𝕜)
    (fan.basisConeDualSemigroupEquiv basis).toMultiplicative).trans
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv 𝕜 𝕜 (Fin dimension →₀ ℕ)).symm

end TauCeti.Toric.Fan
