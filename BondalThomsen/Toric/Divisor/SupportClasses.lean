module

public import BondalThomsen.Toric.Positivity.SupportConcavity

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem coneDivisorCharacter_add (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (first second : fan.InvariantRayDivisor) :
    fan.coneDivisorCharacter basis cone_basis (first + second) =
      fan.coneDivisorCharacter basis cone_basis first +
        fan.coneDivisorCharacter basis cone_basis second := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  change fan.coneDivisorCharacter basis cone_basis (first + second) (basis index) =
    fan.coneDivisorCharacter basis cone_basis first (basis index) +
      fan.coneDivisorCharacter basis cone_basis second (basis index)
  simp only [fan.coneDivisorCharacter_basis, Finsupp.add_apply, neg_add]

theorem coneDivisorCharacter_principal (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (character : Lattice →+ ℤ) :
    fan.coneDivisorCharacter basis cone_basis (fan.principalRayDivisor character) =
      -character := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  change fan.coneDivisorCharacter basis cone_basis (fan.principalRayDivisor character)
    (basis index) = -character (basis index)
  rw [fan.coneDivisorCharacter_basis, fan.principalRayDivisor_apply, fan.basisRay_val]

end TauCeti.Toric.Fan
