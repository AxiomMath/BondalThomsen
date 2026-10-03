module

public import BondalThomsen.DeepFan.PrimitiveCoefficientCriterion
public import BondalThomsen.Toric.Positivity.SupportConcavity

@[expose] public section

open Finset Set Module Classical

namespace TauCeti.Toric.Fan

section Coefficients

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def anticanonicalRayDivisor (fan : TauCeti.Toric.Fan embedding) :
    fan.InvariantRayDivisor := fan.invariantDivisorOfCoefficients (fun _ => 1)

@[simp] theorem anticanonicalRayDivisor_apply (fan : TauCeti.Toric.Fan embedding)
    (ray : fan.Ray) : fan.anticanonicalRayDivisor ray = 1 := rfl

end Coefficients

section ConeCharacters

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem coneDivisorCharacter_anticanonical (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) :
    fan.coneDivisorCharacter basis cone_basis fan.anticanonicalRayDivisor =
      -basis.sumCoords.toAddMonoidHom := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  change fan.coneDivisorCharacter basis cone_basis fan.anticanonicalRayDivisor (basis index) =
    -basis.sumCoords (basis index)
  rw [fan.coneDivisorCharacter_basis, fan.anticanonicalRayDivisor_apply,
    Basis.sumCoords_self_apply]

end ConeCharacters

end TauCeti.Toric.Fan

