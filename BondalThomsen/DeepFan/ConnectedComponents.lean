module

public import BondalThomsen.Matroid.ConnectedComponents
public import BondalThomsen.Matroid.MarkedTreeMatroidReconstruction
public import BondalThomsen.DeepFan.LowRankReductions
public import BondalThomsen.Matroid.TreeShapeMatroidInterpretation

@[expose] public section

open scoped Classical

namespace TauCeti.Toric.Fan

open Module BondalThomsen Set

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem rayMatroid_loopless_of_basis (fan : Fan embedding) {dimension : ℕ}
    (reference : Basis (Fin dimension) ℤ Lattice) : fan.rayMatroid.Loopless := by
  rw [fan.rayMatroid_eq_coordinates reference]
  apply Matroid.loopless_iff_forall_isNonloop.mpr
  intro ray member
  rw [← Matroid.indep_singleton, BondalThomsen.rayMatroid_indep_iff]
  apply LinearIndepOn.singleton
  intro coordinates_zero
  apply ray.property.1.ne_zero
  apply reference.repr.injective
  ext row
  have equality := congrFun coordinates_zero row
  simp only [Pi.zero_apply] at equality
  simp only [map_zero, Finsupp.zero_apply]
  exact_mod_cast equality

end TauCeti.Toric.Fan
