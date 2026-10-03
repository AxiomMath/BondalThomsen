module

public import BondalThomsen.DeepFan.StarDeep
public import BondalThomsen.Fan.RationalRayQuotient
public import BondalThomsen.Ports.Matroid.Representation
public import BondalThomsen.Matroid.RepresentedSimplification
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen
open scoped TensorProduct

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def starContractionRep (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    (fan.rayMatroid.contract {ray}).Rep ℚ (ℚ ⊗[ℤ] (fan.StarLattice ray)) where
  to_fun other := (1 : ℚ) ⊗ₜ[ℤ] ((Submodule.span ℤ {ray.val}).mkQ other.val)
  indep_iff' selected := by
    let := fan.lattice.free
    let := fan.lattice.finite
    obtain ⟨size, basis, removed, equality⟩ := ray.property.1.exists_basis
    let vectors := fun other : fan.Ray => (1 : ℚ) ⊗ₜ[ℤ] other.val
    let representation := Matroid.repOfRays (Field := ℚ) vectors
    have rational_span : Submodule.span ℚ (representation '' ({ray} : Set fan.Ray)) =
        Submodule.span ℚ {((1 : ℚ) ⊗ₜ[ℤ] ray.val)} := by
      apply congrArg (Submodule.span ℚ)
      rw [Set.image_singleton]
      rfl
    have contracted := (representation.contract ({ray} : Set fan.Ray)).indep_iff
      (independentSet := selected)
    change (fan.rayMatroid.contract {ray}).Indep selected ↔
      LinearIndepOn ℚ (fun other =>
        (Submodule.span ℚ (representation '' ({ray} : Set fan.Ray))).mkQ (vectors other))
        selected at contracted
    rw [rational_span] at contracted
    rw [contracted]
    let equivalence := rationalRayQuotientEquiv basis removed ray.val equality
    have compatible : (fun other : fan.Ray =>
        equivalence ((Submodule.span ℚ {((1 : ℚ) ⊗ₜ[ℤ] ray.val)}).mkQ (vectors other))) =
        (fun other : fan.Ray =>
          (1 : ℚ) ⊗ₜ[ℤ] ((Submodule.span ℤ {ray.val}).mkQ other.val)) := by
      funext other
      exact rationalRayQuotientEquiv_mkQ_tmul basis removed ray.val equality other.val
    constructor
    · intro independent
      have mapped := independent.map_injOn equivalence.toLinearMap
        (fun _ _ _ _ same => equivalence.injective same)
      change LinearIndepOn ℚ (fun other =>
        equivalence ((Submodule.span ℚ {((1 : ℚ) ⊗ₜ[ℤ] ray.val)}).mkQ (vectors other)))
        selected at mapped
      rwa [compatible] at mapped
    · intro independent
      rw [← compatible] at independent
      exact independent.of_comp equivalence.toLinearMap

noncomputable def starRayRep (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    (fan.star ray).rayMatroid.Rep ℚ (ℚ ⊗[ℤ] (fan.StarLattice ray)) :=
  Matroid.repOfRays (Field := ℚ) (fun other : (fan.star ray).Ray => (1 : ℚ) ⊗ₜ[ℤ] other.val)

theorem starContractionRep_nonzeroLines_eq [FiniteDimensional ℝ Ambient]
    (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (ray : fan.Ray) :
    (fan.starContractionRep ray).nonzeroLines = (fan.starRayRep ray).nonzeroLines := by
  let := (fan.star ray).lattice.free
  have tensor_injective := Module.Flat.tensorProduct_mk_injective ℤ
    (fan.StarLattice ray) ℚ
  ext line
  constructor
  · rintro ⟨source, nonzero, equality⟩
    have integral_nonzero : (Submodule.span ℤ {ray.val}).mkQ source.val ≠ 0 := by
      intro zero
      apply nonzero
      change (1 : ℚ) ⊗ₜ[ℤ] ((Submodule.span ℤ {ray.val}).mkQ source.val) = 0
      rw [zero, TensorProduct.tmul_zero]
    have properties := fan.projected_ray_isRay complete regular deep reference ray source
      integral_nonzero
    let other : (fan.star ray).Ray := ⟨_, properties⟩
    exact ⟨other, nonzero, equality⟩
  · rintro ⟨other, nonzero, equality⟩
    obtain ⟨source, source_eq⟩ := fan.starRay_eq_projected_ray complete regular ray other
    refine ⟨source, ?_, ?_⟩
    · change (1 : ℚ) ⊗ₜ[ℤ] ((Submodule.span ℤ {ray.val}).mkQ source.val) ≠ 0
      change (1 : ℚ) ⊗ₜ[ℤ] other.val ≠ 0 at nonzero
      rwa [source_eq] at nonzero
    · change Submodule.span ℚ {(1 : ℚ) ⊗ₜ[ℤ]
        ((Submodule.span ℤ {ray.val}).mkQ source.val)} = line
      change Submodule.span ℚ {(1 : ℚ) ⊗ₜ[ℤ] other.val} = line at equality
      rwa [source_eq] at equality

noncomputable def star_contraction_simplification_iso [FiniteDimensional ℝ Ambient]
    (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (ray : fan.Ray)
    {source_simple : Matroid fan.Ray} {star_simple : Matroid (fan.star ray).Ray}
    (source_simplification : source_simple.IsSimplification (fan.rayMatroid.contract {ray}))
    (star_simplification : star_simple.IsSimplification (fan.star ray).rayMatroid) :
    Matroid.Iso source_simple star_simple :=
  (fan.starContractionRep ray).simplificationIso (fan.starRayRep ray)
    source_simplification star_simplification
    (fan.starContractionRep_nonzeroLines_eq complete regular deep reference ray)

end TauCeti.Toric.Fan
