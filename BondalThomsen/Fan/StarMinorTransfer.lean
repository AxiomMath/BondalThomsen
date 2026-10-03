module

public import BondalThomsen.Matroid.MinorTransport
public import BondalThomsen.Fan.StarContraction
public import BondalThomsen.Fan.Rank

@[expose] public section

namespace TauCeti.Toric.Fan

open Module

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem exists_simple_minor_star_simplification (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) {smaller : Matroid fan.Ray}
    (minor : smaller ≤m fan.rayMatroid.contract {ray}) (simple : smaller.Simple)
    {star_simple : Matroid (fan.star ray).Ray}
    (star_simplification : star_simple.IsSimplification (fan.star ray).rayMatroid) :
    ∃ transported : Matroid (fan.star ray).Ray,
      transported ≤m star_simple ∧ transported.Simple ∧
        Nonempty (Matroid.Iso smaller transported) := by
  obtain ⟨source_simple, source_minor, source_simplification⟩ :=
    (fan.starContractionRep ray).exists_isMinor_isSimplification minor simple
  let star_iso := fan.star_contraction_simplification_iso complete regular deep reference ray
    source_simplification star_simplification
  exact star_iso.exists_simple_isMinor source_minor simple

theorem exists_simple_minor_star (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) {smaller : Matroid fan.Ray}
    (minor : smaller ≤m fan.rayMatroid.contract {ray}) (simple : smaller.Simple) :
    ∃ transported : Matroid (fan.star ray).Ray,
      transported ≤m (fan.star ray).rayMatroid ∧ transported.Simple ∧
        Nonempty (Matroid.Iso smaller transported) := by
  obtain ⟨star_simple, star_simplification⟩ := (fan.starRayRep ray).exists_isSimplification
  obtain ⟨transported, transported_minor, transported_simple, transported_iso⟩ :=
    fan.exists_simple_minor_star_simplification complete regular deep reference ray minor simple
      star_simplification
  exact ⟨transported, transported_minor.trans star_simplification.2.1.isMinor,
    transported_simple, transported_iso⟩

theorem star_rayMatroid_eRank (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) : (fan.star ray).rayMatroid.eRank = (dimension - 1 : ℕ) := by
  let : IsClosed (Submodule.span ℝ {embedding ray.val} : Set Ambient) :=
    (Submodule.span ℝ {embedding ray.val}).closed_of_finiteDimensional
  obtain ⟨star_complete, star_regular, _⟩ :=
    fan.star_complete_regular_deep complete regular deep reference ray
  obtain ⟨size, basis, cone_basis, _⟩ :=
    (fan.star ray).exists_coneBasis_containing star_complete star_regular
      (0 : fan.StarAmbient ray)
  have source_dimension : finrank ℝ Ambient = dimension := by
    rw [← fan.lattice.finrank_eq]
    simpa only [Fintype.card_fin] using finrank_eq_card_basis reference
  have star_dimension : finrank ℝ (fan.StarAmbient ray) = size := by
    rw [← (fan.star ray).lattice.finrank_eq]
    simpa only [Fintype.card_fin] using finrank_eq_card_basis basis
  have dimension_drop := fan.star_finrank_add_one ray
  rw [source_dimension, star_dimension] at dimension_drop
  have size_eq : size = dimension - 1 := by omega
  simpa only [size_eq] using (fan.star ray).rayMatroid_eRank basis cone_basis

theorem star_rayMatroid_eRank_toNat_add_one (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) :
    (fan.star ray).rayMatroid.eRank.toNat + 1 = fan.rayMatroid.eRank.toNat := by
  have source_dimension : finrank ℝ Ambient = dimension := by
    rw [← fan.lattice.finrank_eq]
    simpa only [Fintype.card_fin] using finrank_eq_card_basis reference
  have dimension_drop := fan.star_finrank_add_one ray
  rw [source_dimension] at dimension_drop
  rw [fan.star_rayMatroid_eRank complete regular deep reference ray,
    fan.rayMatroid_eRank_of_complete_regular complete regular reference]
  simp only [ENat.toNat_natCast]
  omega

theorem simple_contraction_minor_star_induction (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) {smaller : Matroid fan.Ray}
    (minor : smaller ≤m fan.rayMatroid.contract {ray}) (simple : smaller.Simple) :
    (fan.star ray).IsComplete ∧ (fan.star ray).IsRegular ∧
      (fan.star ray).IsDeep (dimension - 1) ∧
      (fan.star ray).rayMatroid.eRank.toNat + 1 = fan.rayMatroid.eRank.toNat ∧
      ∃ transported : Matroid (fan.star ray).Ray,
        transported ≤m (fan.star ray).rayMatroid ∧ transported.Simple ∧
          Nonempty (Matroid.Iso smaller transported) := by
  obtain ⟨star_complete, star_regular, star_deep⟩ :=
    fan.star_complete_regular_deep complete regular deep reference ray
  exact ⟨star_complete, star_regular, star_deep,
    fan.star_rayMatroid_eRank_toNat_add_one complete regular deep reference ray,
    fan.exists_simple_minor_star complete regular deep reference ray minor simple⟩

end TauCeti.Toric.Fan
