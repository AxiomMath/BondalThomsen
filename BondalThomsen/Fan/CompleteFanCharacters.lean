module

public import BondalThomsen.Fan.EffectiveRayDivisors
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.DenseTorus

@[expose] public section

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

open Set Module Multiplicative TauCeti.Toric

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem character_eq_zero_of_all_dualSemigroups (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (character : Lattice →+ ℤ)
    (regular_on_cones : ∀ cone ∈ fan.cones, character ∈ dualSemigroup fan.lattice cone) :
    character = 0 := by
  apply fan.character_eq_zero_of_nonnegative_rays complete character
  intro ray
  have nonnegative := (mem_dualSemigroup fan.lattice character).mp
    (regular_on_cones _ ray.property.2) (PointedCone.subset_hull (Set.mem_singleton _))
  rw [fan.lattice.realCharacter_apply] at nonnegative
  exact_mod_cast nonnegative

abbrev LaurentCharacterAlgebra (_fan : TauCeti.Toric.Fan embedding) :=
  MonoidAlgebra 𝕜 (Multiplicative (Lattice →+ ℤ))

noncomputable def coneLaurentMap (fan : TauCeti.Toric.Fan embedding)
    (cone : PointedCone ℝ Ambient) :
    affineCoordinateRing 𝕜 fan.lattice cone →ₐ[𝕜] (fan.LaurentCharacterAlgebra 𝕜) :=
  MonoidAlgebra.mapDomainAlgHom 𝕜 𝕜 (dualSemigroup fan.lattice cone).subtype.toMultiplicative

theorem coneLaurentMap_injective (fan : TauCeti.Toric.Fan embedding)
    (cone : PointedCone ℝ Ambient) : Function.Injective (fan.coneLaurentMap 𝕜 cone) := by
  change Function.Injective (MonoidAlgebra.mapDomain
    (dualSemigroup fan.lattice cone).subtype.toMultiplicative)
  exact MonoidAlgebra.mapDomain_injective (fun _ _ same => Subtype.ext same)

@[simp] theorem coneLaurentMap_single (fan : TauCeti.Toric.Fan embedding)
    (cone : PointedCone ℝ Ambient) (character : dualSemigroup fan.lattice cone) (coefficient : 𝕜) :
    fan.coneLaurentMap 𝕜 cone (MonoidAlgebra.single (ofAdd character) coefficient) =
      MonoidAlgebra.single (ofAdd (character : Lattice →+ ℤ)) coefficient := by
  simp [coneLaurentMap]

theorem laurent_eq_constant_of_regular_support (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (polynomial : fan.LaurentCharacterAlgebra 𝕜)
    (regular_support : ∀ character ∈ polynomial.coeff.support,
      ∀ cone ∈ fan.cones, toAdd character ∈ dualSemigroup fan.lattice cone) :
    polynomial = MonoidAlgebra.single 1 (polynomial.coeff 1) := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext character
  by_cases zero_character : character = 1
  · subst character
    simp
  · have coefficient_zero : polynomial.coeff character = 0 := by
      by_contra nonzero
      have member := Finsupp.mem_support_iff.mpr nonzero
      have zero := fan.character_eq_zero_of_all_dualSemigroups complete (toAdd character)
        (regular_support character member)
      apply zero_character
      exact zero
    simp [coefficient_zero, zero_character]

theorem character_regular_of_mem_coneLaurent_support (fan : TauCeti.Toric.Fan embedding)
    (cone : PointedCone ℝ Ambient) (polynomial : affineCoordinateRing 𝕜 fan.lattice cone)
    (character : Multiplicative (Lattice →+ ℤ))
    (member : character ∈ (fan.coneLaurentMap 𝕜 cone polynomial).coeff.support) :
    toAdd character ∈ dualSemigroup fan.lattice cone := by
  classical
  let inclusion : Multiplicative (dualSemigroup fan.lattice cone) ↪
      Multiplicative (Lattice →+ ℤ) :=
    ⟨(dualSemigroup fan.lattice cone).subtype.toMultiplicative,
      fun _ _ same => Subtype.ext same⟩
  change character ∈ (Finsupp.mapDomain inclusion polynomial.coeff).support at member
  rw [Finsupp.support_mapDomain_embedding, Finset.mem_map] at member
  obtain ⟨local_character, _, same⟩ := member
  rw [← same]
  exact local_character.property

theorem laurent_eq_constant_of_all_cone_images (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (polynomial : fan.LaurentCharacterAlgebra 𝕜)
    (local_images : ∀ cone ∈ fan.cones, ∃ local_polynomial : affineCoordinateRing 𝕜 fan.lattice cone,
      fan.coneLaurentMap 𝕜 cone local_polynomial = polynomial) :
    polynomial = MonoidAlgebra.single 1 (polynomial.coeff 1) := by
  apply fan.laurent_eq_constant_of_regular_support 𝕜 complete polynomial
  intro character member cone belongs
  obtain ⟨local_polynomial, same⟩ := local_images cone belongs
  apply fan.character_regular_of_mem_coneLaurent_support 𝕜 cone local_polynomial character
  rwa [same]

end TauCeti.Toric.Fan
