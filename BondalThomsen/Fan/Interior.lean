module

public import BondalThomsen.Fan.Polytope
public import BondalThomsen.Fan.PositiveSpanning

@[expose] public section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem zero_mem_interior_rayPolytope (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (nonempty : fan.rayGenerators.Nonempty) :
    (0 : Ambient) ∈ interior fan.rayPolytope :=
  BondalThomsen.zero_mem_interior_convexHull_of_positive_spanning fan.rayGenerators
    fan.rayGenerators_finite nonempty (fan.hull_rayGenerators_eq_top complete)

omit [FiniteDimensional ℝ Ambient] in

theorem rayGenerators_nonempty_of_complete [Nontrivial Ambient]
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete) :
    fan.rayGenerators.Nonempty := by
  by_contra empty
  have generators_empty : fan.rayGenerators = ∅ := Set.not_nonempty_iff_eq_empty.mp empty
  have cone_top := fan.hull_rayGenerators_eq_top complete
  rw [generators_empty, PointedCone.hull, Submodule.span_empty] at cone_top
  exact bot_ne_top cone_top

theorem zero_mem_interior_rayPolytope_of_complete [Nontrivial Ambient]
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete) :
    (0 : Ambient) ∈ interior fan.rayPolytope :=
  fan.zero_mem_interior_rayPolytope complete (fan.rayGenerators_nonempty_of_complete complete)

end TauCeti.Toric.Fan
