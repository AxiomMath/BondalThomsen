module

public import BondalThomsen.Fan.SmoothFanoPolytopeFiniteness
public import BondalThomsen.Fan.Determination

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Module BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in
theorem supportingFunctional_ray_le_one_of_strictSupport
    (fan : Fan embedding) (strict : fan.HasStrictAnticanonicalConeSupport)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (ray : fan.Ray) :
    fan.supportingFunctional basis (embedding ray.val) ≤ 1 := by
  rw [fan.supportingFunctional_lattice]
  have bound := fan.rayHeight_le_one_of_strictSupport strict basis coneBasis ray
  have height : (∑ index, basis.repr ray.val index : ℤ) ≤ 1 := by
    simpa [Basis.sumCoords, Finsupp.sum_fintype] using bound
  exact_mod_cast height

omit [FiniteDimensional ℝ Ambient] in
theorem supportingFunctional_ray_eq_one_iff_of_strictSupport
    (fan : Fan embedding) (strict : fan.HasStrictAnticanonicalConeSupport)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis basis) (ray : fan.Ray) :
    fan.supportingFunctional basis (embedding ray.val) = 1 ↔ ray.val ∈ Set.range basis := by
  rw [fan.supportingFunctional_lattice]
  constructor
  · intro equality
    have height : (∑ index, basis.repr ray.val index : ℤ) = 1 := by exact_mod_cast equality
    apply (fan.rayHeight_eq_one_iff_of_strictSupport strict basis coneBasis ray).mp
    simpa [Basis.sumCoords, Finsupp.sum_fintype] using height
  · rintro ⟨index, equality⟩
    rw [← equality]
    simp

end TauCeti.Toric.Fan
