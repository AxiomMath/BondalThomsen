module

public import BondalThomsen.Fan.PrimitiveRelationUniqueness

@[expose] public section

set_option autoImplicit false

open Module

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

abbrev PrimitiveRelationIndex (fan : Fan embedding) :=
  Σ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right

omit [FiniteDimensional ℝ Ambient] in
theorem primitiveRelationIndex_finite
    (fan : Fan embedding) (regular : fan.IsRegular) :
    Finite fan.PrimitiveRelationIndex := by
  let : ∀ left : Finset fan.Ray,
      Subsingleton (Σ right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right) :=
    fan.primitiveLatticeRelation_subsingleton regular
  infer_instance

end TauCeti.Toric.Fan
