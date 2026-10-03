module

public import BondalThomsen.Fan.FanoIntegralRayTransport
public import BondalThomsen.Rarity.FiniteClassEncoding
public import BondalThomsen.Rarity.ToricFanoIntegralFanClasses

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module Set
open TauCeti.Toric.Fan BondalThomsen.ToricTransport BondalThomsen.ProjectiveBundle
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

variable {Lattice Ambient : Type} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem strictFano_integralFanFamilyClasses_finite
    {Index : Type*} {dimension : ℕ} (fans : Index → TauCeti.Toric.Fan embedding)
    (complete : ∀ index, (fans index).IsComplete)
    (regular : ∀ index, (fans index).IsRegular)
    (strict : ∀ index, (fans index).HasStrictAnticanonicalConeSupport)
    (reference : Basis (Fin dimension) ℤ Lattice) :
    (Set.range (fun index => integralFanClass (fans index))).Finite := by
  classical
  choose bases special using
    (fun index => (fans index).exists_specialConeBasis (complete index) (regular index) reference)
  let code := fun index => (fans index).normalizedRayCoordinates (bases index)
  have finiteCodes : (Set.range code).Finite := by
    apply ((smoothFanoCoordinateBox_finite dimension).finite_subsets).subset
    rintro coordinates ⟨index, rfl⟩
    exact (fans index).specialConeBasis_normalizedRayCoordinates_subset_box
      (complete index) (regular index) (strict index) (bases index) (special index)
  exact (finite_class_range_of_finite_code_range (fun index => integralFanClass (fans index))
    code finiteCodes (fun first second equality =>
      integralFanClass_eq_of_normalizedRayCoordinates_eq (fans first) (fans second)
        (complete first) (regular first) (strict first) (complete second) (regular second)
        (strict second) (bases first) (bases second) equality)).1

theorem actualFano_integralFanFamilyClasses_finite
    {Index : Type*} {dimension : ℕ} (fans : Index → TauCeti.Toric.Fan embedding)
    (complete : ∀ index, (fans index).IsComplete)
    (regular : ∀ index, (fans index).IsRegular)
    (ample : ∀ index,
      letI := (fans index).algebraicRealization_isIntegral 𝕜 (regular index)
        ((fans index).completeFan_nonemptyCones (complete index))
      SchemeLineBundleClassAmple (((fans index).toricCanonicalLineBundleClass 𝕜
        (complete index) (regular index))⁻¹))
    (reference : Basis (Fin dimension) ℤ Lattice) :
    (Set.range (fun index => integralFanClass (fans index))).Finite :=
  strictFano_integralFanFamilyClasses_finite fans complete regular
    (fun index => (fans index).strictAnticanonicalSupport_of_actualCanonicalInverse_isAmple 𝕜
      (complete index) (regular index) (ample index)) reference

theorem smoothProjectiveToricFanoIntegralFanClasses_finite (dimension : ℕ) :
    (smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension).Finite := by
  classical
  choose fans complete regular realized _smooth _projective ample using
    (fun fanClass : smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension => fanClass.property)
  have rangeEquality : Set.range (fun fanClass => integralFanClass (fans fanClass)) =
      smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension := by
    ext fanClass
    constructor
    · rintro ⟨presented, rfl⟩
      change integralFanClass (fans presented) ∈ smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension
      rw [realized presented]
      exact presented.property
    · intro membership
      exact ⟨⟨fanClass, membership⟩, realized ⟨fanClass, membership⟩⟩
  rw [← rangeEquality]
  exact actualFano_integralFanFamilyClasses_finite 𝕜 fans complete regular ample
    (parameterLatticeDimensionBasis dimension)

end BondalThomsen
