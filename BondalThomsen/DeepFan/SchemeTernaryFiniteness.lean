module

public import BondalThomsen.Rarity.DeepFanSchemeCountingRigidity
public import BondalThomsen.Toric.Scheme.FanEquivSchemeIso
public import BondalThomsen.Rarity.Counting
public import Mathlib.CategoryTheory.Skeletal
public import BondalThomsen.Matroid.Binary.RankFourCoverage
public import BondalThomsen.DeepFan.Classification
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Set

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient]
    {embedding : Lattice →+ Ambient}

def ternaryCoordinates {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (vector : Lattice) : Fin dimension → SignType :=
  fun index => SignType.sign (basis.repr vector index)

noncomputable def ternaryRayCode (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) : Finset (Fin dimension → SignType) := by
  classical
  exact (Set.finite_range (fun ray : fan.Ray => ternaryCoordinates basis ray.val)).toFinset

theorem ternaryCoordinates_cast (fan : Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (ray : fan.Ray) (index : Fin dimension) :
    (ternaryCoordinates basis ray.val index : ℤ) = basis.repr ray.val index := by
  obtain negative | zero | positive := fan.deep_ray_coordinate_trichotomy_of_complete_regular
    complete regular deep basis cone_basis ray index
  · simp only [ternaryCoordinates, negative]
    rfl
  · simp only [ternaryCoordinates, zero]
    rfl
  · simp only [ternaryCoordinates, positive]
    rfl

end TauCeti.Toric.Fan
