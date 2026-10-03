module

public import BondalThomsen.Fan.FanoObstruction
public import BondalThomsen.Fan.Rank
public import BondalThomsen.DeepFan.Theorems

@[expose] public section

namespace TauCeti.Toric.Fan

open Module Set BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in

theorem simple_restriction_ground_card_le_six_of_rayMatrix
    (fan : TauCeti.Toric.Fan embedding) (basis : Basis (Fin 3) ℤ Lattice)
    (unimodular : (fan.rayMatrix basis).IsTotallyUnimodular)
    {smaller : Matroid fan.Ray} (restriction : smaller.IsRestriction fan.rayMatroid)
    (simple : smaller.Simple) : Nat.card smaller.E ≤ 6 := by
  classical
  let : Finite smaller.E := Finite.of_injective Subtype.val Subtype.val_injective
  let := Fintype.ofFinite smaller.E
  let matrix : Matrix (Fin 3) smaller.E ℤ :=
    (fan.rayMatrix basis).submatrix id Subtype.val
  let coordinate_matroid := BondalThomsen.rayMatroid (Field := ℚ)
    (fun column : smaller.E => fun row => (matrix row column : ℚ))
  have coordinate_simple : coordinate_matroid.Simple := by
    apply Matroid.simple_iff_forall_pair_indep.mpr
    intro first second _ _
    have pair := Matroid.simple_iff_forall_pair_indep.mp simple first.val second.val
      first.property second.property
    have source_pair := (restriction.indep_iff.mp pair).1
    rw [fan.rayMatroid_eq_coordinates basis, BondalThomsen.rayMatroid_indep_iff] at source_pair
    rw [show coordinate_matroid = BondalThomsen.rayMatroid (Field := ℚ)
      (fun column : smaller.E => fun row => (matrix row column : ℚ)) from rfl,
      BondalThomsen.rayMatroid_indep_iff]
    apply (show LinearIndepOn ℚ
      (fun ray : fan.Ray => fun row => (basis.repr ray.val row : ℚ))
      (Subtype.val '' ({first, second} : Set smaller.E)) by
        simpa only [Set.image_pair] using source_pair).comp_of_image
          Subtype.val_injective.injOn
  let : coordinate_matroid.Simple := coordinate_simple
  have bound := totallyUnimodular_simple_rational_card_le_six matrix
    (unimodular.submatrix id Subtype.val)
  simpa only [Nat.card_eq_fintype_card] using bound

theorem simple_restriction_ground_card_le_six (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep 3)
    (reference : Basis (Fin 3) ℤ Lattice) {smaller : Matroid fan.Ray}
    (restriction : smaller.IsRestriction fan.rayMatroid) (simple : smaller.Simple) :
    Nat.card smaller.E ≤ 6 := by
  obtain ⟨size, basis, cone_basis, _⟩ :=
    fan.exists_coneBasis_containing complete regular (0 : Ambient)
  have size_eq : size = 3 := by
    have basis_rank := finrank_eq_card_basis basis
    have reference_rank := finrank_eq_card_basis reference
    simp only [Fintype.card_fin] at basis_rank reference_rank
    omega
  subst size
  exact fan.simple_restriction_ground_card_le_six_of_rayMatrix basis
    (fan.deep_rayMatrix_totallyUnimodular complete regular deep basis cone_basis)
    restriction simple

theorem simplification_ground_card_le_six (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep 3)
    (reference : Basis (Fin 3) ℤ Lattice) {smaller : Matroid fan.Ray}
    (simplification : smaller.IsSimplification fan.rayMatroid) : Nat.card smaller.E ≤ 6 :=
  fan.simple_restriction_ground_card_le_six complete regular deep reference
    simplification.2.1 simplification.simple

theorem ray_directions_card_le_six (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep 3)
    (reference : Basis (Fin 3) ℤ Lattice) : Nat.card fan.rayDirections ≤ 6 := by
  obtain ⟨smaller, simplification⟩ := fan.rayRep.exists_isSimplification
  rw [← fan.simplification_ground_card_eq_directions simplification]
  exact fan.simplification_ground_card_le_six complete regular deep reference simplification

end TauCeti.Toric.Fan
