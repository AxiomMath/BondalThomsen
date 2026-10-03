module

public import BondalThomsen.Toric.Divisor.EffectiveSections
public import BondalThomsen.Toric.Divisor.PicardFaithfulness
public import BondalThomsen.Derived.LineBundleGenericComposition

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem invariantDivisorEffectiveSection_rationalValue (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (effective : ∀ ray, 0 ≤ divisor ray)
    (open_set : (fan.algebraicRealization 𝕜 regular).Opens) [Nonempty open_set] :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set
      (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι open_set
        (fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular divisor open_set
          (fan.invariantDivisorEffectiveSection 𝕜 complete regular divisor effective))) = 1 := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  unfold invariantDivisorEffectiveSection
  rw [fan.invariantDivisorSheafRestrictGlobal_rationalValue 𝕜,
    fan.laurentRationalMap_characterMonomial 𝕜, fan.rationalCharacterUnit_zero 𝕜, Units.val_one]

theorem invariantDivisor_effective_sections_le (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor effective_divisor : fan.InvariantRayDivisor)
    (effective : ∀ ray, 0 ≤ effective_divisor ray) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    ∀ open_set, (fan.invariantDivisorCartier 𝕜 complete regular divisor).sections open_set ≤
      (fan.invariantDivisorCartier 𝕜 complete regular (divisor + effective_divisor)).sections open_set := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  intro open_set rational_section member
  by_cases inhabited : Nonempty open_set
  · let := inhabited
    let effective_section := fan.invariantDivisorSheafRestrictGlobal 𝕜 complete regular
      effective_divisor open_set
      (fan.invariantDivisorEffectiveSection 𝕜 complete regular effective_divisor effective)
    have effective_member :=
      (fan.invariantDivisorCartier 𝕜 complete regular effective_divisor).sheafι_app_mem
        open_set effective_section
    have product_member :=
      TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.rationalFunctionsMulBilin_mem_sections
        member effective_member
    have product_eq : TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMulBilin
        (fan.algebraicRealization 𝕜 regular) open_set rational_section
        (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular effective_divisor).sheafι
          open_set effective_section) = rational_section := by
      apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv open_set).injective
      rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_mulBilin,
        fan.invariantDivisorEffectiveSection_rationalValue 𝕜 complete regular effective_divisor
          effective open_set, mul_one]
    rw [product_eq, ← fan.invariantDivisorCartier_add 𝕜 complete regular divisor effective_divisor]
      at product_member
    exact product_member
  · apply TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections.mpr
    intro point contains
    exact (inhabited ⟨⟨point, contains⟩⟩).elim

noncomputable def invariantDivisorEffectiveHom (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor effective_divisor : fan.InvariantRayDivisor)
    (effective : ∀ ray, 0 ≤ effective_divisor ray) :
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj ⟶
      (fan.invariantDivisorLineBundle 𝕜 complete regular (divisor + effective_divisor)).obj := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact (fan.invariantDivisorCartier 𝕜 complete regular (divisor + effective_divisor)).sheafLift
    (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι
    (fun open_set section_value => fan.invariantDivisor_effective_sections_le 𝕜 complete regular
      divisor effective_divisor effective open_set
      ((fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_mem open_set section_value))

theorem invariantDivisorEffectiveHom_ι (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor effective_divisor : fan.InvariantRayDivisor)
    (effective : ∀ ray, 0 ≤ effective_divisor ray) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.invariantDivisorEffectiveHom 𝕜) complete regular divisor effective_divisor effective ≫
      (fan.invariantDivisorCartier 𝕜 complete regular (divisor + effective_divisor)).sheafι =
        (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheafLift_ι _ _ _

theorem invariantDivisorEffectiveHom_mono (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor effective_divisor : fan.InvariantRayDivisor)
    (effective : ∀ ray, 0 ≤ effective_divisor ray) :
    Mono (fan.invariantDivisorEffectiveHom 𝕜 complete regular divisor effective_divisor effective) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  have : Mono (fan.invariantDivisorEffectiveHom 𝕜 complete regular divisor effective_divisor effective ≫
      (fan.invariantDivisorCartier 𝕜 complete regular (divisor + effective_divisor)).sheafι) := by
    rw [fan.invariantDivisorEffectiveHom_ι 𝕜]
    exact SheafOfModules.Submodule.instMonoι
      (fan.invariantDivisorCartier 𝕜 complete regular divisor).submodule
  exact mono_of_mono _ (fan.invariantDivisorCartier 𝕜 complete regular (divisor + effective_divisor)).sheafι

theorem invariantDivisorEffectiveHom_ne_zero (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor effective_divisor : fan.InvariantRayDivisor)
    (effective : ∀ ray, 0 ≤ effective_divisor ray) :
    fan.invariantDivisorEffectiveHom 𝕜 complete regular divisor effective_divisor effective ≠ 0 := by
  let := fan.invariantDivisorEffectiveHom_mono 𝕜 complete regular divisor effective_divisor effective
  intro equality
  have identity_zero : 𝟙 (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj = 0 := by
    apply (cancel_mono (fan.invariantDivisorEffectiveHom 𝕜 complete regular divisor effective_divisor effective)).mp
    simp only [Category.id_comp, zero_comp, equality]
  exact BondalThomsen.invertibleSheaf_identity_ne_zero_of_globalFunctions
    (fan.scalarGlobalFunctionsEquiv 𝕜 complete regular)
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) identity_zero

set_option maxHeartbeats 800000 in

theorem invariantDivisorEffective_sub_nonzeroHom (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor effective_divisor : fan.InvariantRayDivisor)
    (effective : ∀ ray, 0 ≤ effective_divisor ray) :
    ∃ morphism : (fan.invariantDivisorLineBundle 𝕜 complete regular (divisor - effective_divisor)).obj ⟶
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj, morphism ≠ 0 := by
  let statement : fan.InvariantRayDivisor → Prop := fun target => ∃ morphism :
      (fan.invariantDivisorLineBundle 𝕜 complete regular (divisor - effective_divisor)).obj ⟶
      (fan.invariantDivisorLineBundle 𝕜 complete regular target).obj, morphism ≠ 0
  have result : statement ((divisor - effective_divisor) + effective_divisor) :=
      ⟨fan.invariantDivisorEffectiveHom 𝕜 complete regular (divisor - effective_divisor)
          effective_divisor effective,
        fan.invariantDivisorEffectiveHom_ne_zero 𝕜 complete regular (divisor - effective_divisor)
          effective_divisor effective⟩
  have final : statement divisor := (sub_add_cancel divisor effective_divisor) ▸ result
  exact final

end TauCeti.Toric.Fan
