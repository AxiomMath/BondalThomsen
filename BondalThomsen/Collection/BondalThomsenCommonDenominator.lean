module

public import BondalThomsen.Collection.BondalThomsenClasses
public import BondalThomsen.Ports.RationalScaling

@[expose] public section

namespace BondalThomsen

theorem exists_positive_integer_scaled_pairings
    {Lattice Index Family : Type*} [AddCommGroup Lattice] [Finite Index] [Finite Family]
    (basis : Module.Basis Index ℤ Lattice) (pairings : Family → (Lattice →+ ℚ)) :
    ∃ degree : ℕ, 0 < degree ∧ ∃ characters : Family → (Lattice →+ ℤ),
      ∀ member, (Int.castAddHom ℚ).comp (characters member) = degree • pairings member := by
  classical
  let := Fintype.ofFinite Index
  let := Fintype.ofFinite Family
  let values : Set ℚ := Set.range (fun pair : Family × Index => pairings pair.1 (basis pair.2))
  obtain ⟨multiplier, nonzero, integers⟩ := finite_set_integer_scale values (Set.finite_range _)
  have scaled : ∀ pair : Family × Index, ∃ integer : ℤ,
      (multiplier : ℚ) * pairings pair.1 (basis pair.2) = (integer : ℚ) :=
    fun pair => integers _ ⟨pair, rfl⟩
  choose coefficients coefficient_eq using scaled
  let degree := multiplier.natAbs * multiplier.natAbs
  have positive : 0 < degree := Nat.mul_pos (Int.natAbs_pos.mpr nonzero)
    (Int.natAbs_pos.mpr nonzero)
  have degree_eq : (degree : ℚ) = (multiplier : ℚ) * multiplier := by
    exact_mod_cast (Int.natAbs_mul_self (a := multiplier))
  let characters : Family → (Lattice →+ ℤ) := fun member =>
    (basis.constr ℤ (fun index => multiplier * coefficients (member, index))).toAddMonoidHom
  refine ⟨degree, positive, characters, ?_⟩
  intro member
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  change ((characters member) (basis index) : ℚ) = degree • pairings member (basis index)
  simp only [characters, LinearMap.toAddMonoidHom_coe, Module.Basis.constr_basis,
    Int.cast_mul, nsmul_eq_mul]
  rw [degree_eq, mul_assoc, coefficient_eq (member, index)]

end BondalThomsen

namespace TauCeti.Toric.Fan

open scoped Classical

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def residueIntegralCharacter {Index : Type*}
    (basis : Module.Basis Index ℤ Lattice) {degree : ℕ}
    (residue : Index → Fin degree) : Lattice →+ ℤ :=
  (basis.constr ℤ (fun index => ((residue index).val : ℤ))).toAddMonoidHom

noncomputable def residueBondalThomsenClass {Index : Type*}
    (fan : Fan embedding) (basis : Module.Basis Index ℤ Lattice) (degree : ℕ)
    (residue : Index → Fin degree) : fan.BondalThomsenClass :=
  fan.bondalThomsenClassOfPairing
    ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp (residueIntegralCharacter basis residue))

theorem exists_residueBondalThomsenClass_eq {Index : Type*}
    (fan : Fan embedding) (basis : Module.Basis Index ℤ Lattice)
    {degree : ℕ} (positive : 0 < degree) (character : Lattice →+ ℤ) :
    ∃ residue : Index → Fin degree,
      fan.residueBondalThomsenClass basis degree residue =
        fan.bondalThomsenClassOfPairing
          ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character) := by
  have integer_positive : (0 : ℤ) < degree := by exact_mod_cast positive
  let residue : Index → Fin degree := fun index =>
    ⟨(character (basis index) % (degree : ℤ)).toNat,
      (Int.toNat_lt (Int.emod_nonneg _ integer_positive.ne')).mpr
        (Int.emod_lt_of_pos _ integer_positive)⟩
  let correction : Lattice →+ ℤ :=
    (basis.constr ℤ (fun index => character (basis index) / (degree : ℤ))).toAddMonoidHom
  have nonzero : (degree : ℚ) ≠ 0 := by exact_mod_cast positive.ne'
  have character_eq : (degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character =
      (degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp (residueIntegralCharacter basis residue) +
        (Int.castAddHom ℚ).comp correction := by
    apply AddMonoidHom.toIntLinearMap_injective
    apply basis.ext
    intro index
    change (degree : ℚ)⁻¹ * (character (basis index) : ℚ) =
      (degree : ℚ)⁻¹ * ((residueIntegralCharacter basis residue) (basis index) : ℚ) +
        (correction (basis index) : ℚ)
    simp only [residueIntegralCharacter, correction, Module.Basis.constr_basis,
      LinearMap.toAddMonoidHom_coe]
    have residue_eq : ((residue index).val : ℤ) = character (basis index) % (degree : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ integer_positive.ne')
    have divided := Int.emod_add_ediv_mul (character (basis index)) (degree : ℤ)
    have rational_divided :
        ((character (basis index) % (degree : ℤ) : ℤ) : ℚ) +
          ((character (basis index) / (degree : ℤ) : ℤ) : ℚ) * degree = character (basis index) := by
      exact_mod_cast divided
    rw [← Int.cast_natCast, residue_eq]
    field_simp
    simpa only [Int.cast_natCast, mul_comm] using rational_divided.symm
  refine ⟨residue, ?_⟩
  rw [character_eq, fan.bondalThomsenClassOfPairing_add_integral]
  rfl

theorem bondalThomsenClasses_common_denominator
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice] (fan : Fan embedding) :
    ∃ degree : ℕ, 0 < degree ∧ ∀ member : fan.BondalThomsenClass,
      ∃ character : Lattice →+ ℤ,
        fan.bondalThomsenClassOfPairing
          ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character) = member := by
  classical
  let pairings : fan.BondalThomsenClass → (Lattice →+ ℚ) := fun member =>
    (fan.bondalThomsenClassOfPairing_surjective member).choose
  have represented : ∀ member, fan.bondalThomsenClassOfPairing (pairings member) = member :=
    fun member => (fan.bondalThomsenClassOfPairing_surjective member).choose_spec
  obtain ⟨degree, positive, characters, scaled⟩ :=
    BondalThomsen.exists_positive_integer_scaled_pairings (Module.finBasis ℤ Lattice) pairings
  refine ⟨degree, positive, ?_⟩
  intro member
  refine ⟨characters member, ?_⟩
  rw [scaled member]
  have nonzero : (degree : ℚ) ≠ 0 := by exact_mod_cast positive.ne'
  have scaled_inverse : (degree : ℚ)⁻¹ • degree • pairings member = pairings member := by
    ext vector
    simp [nsmul_eq_mul, smul_eq_mul, nonzero]
  rw [scaled_inverse]
  exact represented member

theorem residueBondalThomsenClass_surjective_at_common_degree
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice] (fan : Fan embedding) :
    ∃ degree : ℕ, 0 < degree ∧
      Function.Surjective (fan.residueBondalThomsenClass (Module.finBasis ℤ Lattice) degree) := by
  obtain ⟨degree, positive, representatives⟩ := fan.bondalThomsenClasses_common_denominator
  refine ⟨degree, positive, ?_⟩
  intro member
  obtain ⟨character, represented⟩ := representatives member
  obtain ⟨residue, normalized⟩ :=
    fan.exists_residueBondalThomsenClass_eq (Module.finBasis ℤ Lattice) positive character
  exact ⟨residue, normalized.trans represented⟩

theorem residueBondalThomsenClass_positive_multiplicities
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice] (fan : Fan embedding) :
    ∃ degree : ℕ, 0 < degree ∧ ∀ member : fan.BondalThomsenClass,
      0 < Fintype.card {residue : Fin (Module.finrank ℤ Lattice) → Fin degree //
        fan.residueBondalThomsenClass (Module.finBasis ℤ Lattice) degree residue = member} := by
  classical
  obtain ⟨degree, positive, surjective⟩ := fan.residueBondalThomsenClass_surjective_at_common_degree
  refine ⟨degree, positive, ?_⟩
  intro member
  obtain ⟨residue, represented⟩ := surjective member
  let : Nonempty {residue : Fin (Module.finrank ℤ Lattice) → Fin degree //
      fan.residueBondalThomsenClass (Module.finBasis ℤ Lattice) degree residue = member} :=
    ⟨⟨residue, represented⟩⟩
  exact Fintype.card_pos

theorem residueBondalThomsenClass_sum_multiplicities
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice] (fan : Fan embedding) (degree : ℕ) :
    (∑ member : fan.BondalThomsenClass,
      Fintype.card {residue : Fin (Module.finrank ℤ Lattice) → Fin degree //
        fan.residueBondalThomsenClass (Module.finBasis ℤ Lattice) degree residue = member}) =
      degree ^ Module.finrank ℤ Lattice := by
  classical
  rw [← Fintype.card_sigma,
    Fintype.card_congr (Equiv.sigmaFiberEquiv
      (fan.residueBondalThomsenClass (Module.finBasis ℤ Lattice) degree))]
  simp

end TauCeti.Toric.Fan
