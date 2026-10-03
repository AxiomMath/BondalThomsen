module

public import BondalThomsen.Toric.Positivity.FiniteGlobalGeneration
public import BondalThomsen.Toric.Divisor.PicardGlobalGeneration
public import BondalThomsen.Toric.Divisor.SupportClasses
public import BondalThomsen.Toric.Positivity.VeryAmpleLineBundle

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

universe schemeUniverse

noncomputable def invertibleSheafTensorPower {scheme : Scheme.{schemeUniverse}}
    (bundle : InvertibleSheaf scheme) : ℕ → InvertibleSheaf scheme
  | 0 => InvertibleSheaf.trivial scheme
  | exponent + 1 => InvertibleSheaf.tensorProduct
      (invertibleSheafTensorPower bundle exponent) bundle

theorem invertibleSheafTensorPower_class {scheme : Scheme.{schemeUniverse}}
    (bundle : InvertibleSheaf scheme) (exponent : ℕ) :
    LineBundleClass.mk (invertibleSheafTensorPower bundle exponent) =
      LineBundleClass.mk bundle ^ exponent := by
  induction exponent with
  | zero => simp only [invertibleSheafTensorPower, LineBundleClass.mk_trivial, pow_zero]
  | succ exponent induction_hypothesis =>
      rw [invertibleSheafTensorPower, LineBundleClass.mk_tensorProduct,
        induction_hypothesis, pow_succ]

def InvertibleSheafSemiample {scheme : Scheme.{schemeUniverse}}
    (bundle : InvertibleSheaf scheme) : Prop :=
  ∃ exponent : ℕ, 0 < exponent ∧
    Nonempty (invertibleSheafTensorPower bundle exponent).obj.GeneratingSections

noncomputable def SchemeLineBundleClassSemiample {scheme : Scheme.{schemeUniverse}}
    (bundleClass : LineBundleClass scheme) : Prop :=
  ∃ exponent : ℕ, 0 < exponent ∧
    SchemeLineBundleClassGloballyGenerated (bundleClass ^ exponent)

theorem invertibleSheafSemiample_iff_class {scheme : Scheme.{schemeUniverse}}
    (bundle : InvertibleSheaf scheme) :
    InvertibleSheafSemiample bundle ↔
      SchemeLineBundleClassSemiample (LineBundleClass.mk bundle) := by
  unfold InvertibleSheafSemiample SchemeLineBundleClassSemiample
  apply exists_congr
  intro exponent
  rw [← invertibleSheafTensorPower_class bundle exponent,
    schemeLineBundleClassGloballyGenerated_mk_iff]

theorem invertibleSheafSemiample_iff_of_iso {scheme : Scheme.{schemeUniverse}}
    {first second : InvertibleSheaf scheme} (isomorphism : first.obj ≅ second.obj) :
    InvertibleSheafSemiample first ↔ InvertibleSheafSemiample second := by
  rw [invertibleSheafSemiample_iff_class, invertibleSheafSemiample_iff_class,
    (LineBundleClass.mk_eq_mk_iff).mpr ⟨isomorphism⟩]

theorem invertibleSheafSemiample_of_globallyGenerated {scheme : Scheme.{schemeUniverse}}
    (bundle : InvertibleSheaf scheme) (generated : Nonempty bundle.obj.GeneratingSections) :
    InvertibleSheafSemiample bundle := by
  rw [invertibleSheafSemiample_iff_class]
  refine ⟨1, Nat.zero_lt_one, ?_⟩
  rw [pow_one, schemeLineBundleClassGloballyGenerated_mk_iff]
  exact generated

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

omit [FiniteDimensional ℝ Ambient] in
theorem hasRaySupportInequalities_nsmul_iff (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) (multiple : ℕ) (positive : 0 < multiple) :
    fan.HasRaySupportInequalities (multiple • divisor) ↔
      fan.HasRaySupportInequalities divisor := by
  constructor
  · intro support dimension basis cone_basis ray
    have inequality := support dimension basis cone_basis ray
    rw [fan.coneDivisorCharacter_nsmul] at inequality
    change -(multiple • divisor ray) ≤
      multiple • fan.coneDivisorCharacter basis cone_basis divisor ray.val at inequality
    rw [← neg_nsmul] at inequality
    exact (nsmul_le_nsmul_iff_right (Nat.ne_of_gt positive)).mp inequality
  · intro support dimension basis cone_basis ray
    rw [fan.coneDivisorCharacter_nsmul]
    change -(multiple • divisor ray) ≤
      multiple • fan.coneDivisorCharacter basis cone_basis divisor ray.val
    rw [← neg_nsmul]
    exact nsmul_le_nsmul_right (support dimension basis cone_basis ray) multiple

theorem invariantDivisorTensorPowerGloballyGenerated_iff_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (multiple : ℕ) (positive : 0 < multiple) :
    Nonempty (BondalThomsen.invertibleSheafTensorPower
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) multiple).obj.GeneratingSections ↔
        fan.HasRaySupportInequalities divisor := by
  rw [← BondalThomsen.schemeLineBundleClassGloballyGenerated_mk_iff,
    BondalThomsen.invertibleSheafTensorPower_class,
    ← fan.invariantDivisorLineBundleClass_nsmul 𝕜 complete regular divisor multiple,
    BondalThomsen.schemeLineBundleClassGloballyGenerated_mk_iff]
  exact (fan.invariantDivisorGloballyGenerated_iff_support 𝕜 complete regular (multiple • divisor)).trans
    (fan.hasRaySupportInequalities_nsmul_iff divisor multiple positive)

noncomputable def invariantDivisorTensorPowerIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (multiple : ℕ) :
    (BondalThomsen.invertibleSheafTensorPower
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) multiple).obj ≅
        (fan.invariantDivisorLineBundle 𝕜 complete regular (multiple • divisor)).obj :=
  ((LineBundleClass.mk_eq_mk_iff).mp (by
    rw [BondalThomsen.invertibleSheafTensorPower_class,
      fan.invariantDivisorLineBundleClass_nsmul 𝕜 complete regular divisor multiple])).some

theorem invariantDivisorLineBundleSemiample_iff_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    BondalThomsen.InvertibleSheafSemiample (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) ↔
      fan.HasRaySupportInequalities divisor := by
  constructor
  · rintro ⟨multiple, positive, generated⟩
    exact (fan.invariantDivisorTensorPowerGloballyGenerated_iff_support 𝕜
      complete regular divisor multiple positive).mp generated
  · intro support
    exact BondalThomsen.invertibleSheafSemiample_of_globallyGenerated _
      ⟨fan.allDivisorMonomialSheafGeneratingSections 𝕜 complete regular divisor support⟩

theorem invertibleSheafSemiample_iff_globallyGenerated (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (bundle : InvertibleSheaf (fan.algebraicRealization 𝕜 regular)) :
    BondalThomsen.InvertibleSheafSemiample bundle ↔ Nonempty bundle.obj.GeneratingSections := by
  obtain ⟨divisor, ⟨isomorphism⟩⟩ :=
    fan.invertibleSheaf_exists_invariantDivisorRepresentative 𝕜 complete regular bundle
  exact (BondalThomsen.invertibleSheafSemiample_iff_of_iso isomorphism).trans
    ((fan.invariantDivisorLineBundleSemiample_iff_support 𝕜 complete regular divisor).trans
      (fan.invertibleSheafGloballyGenerated_iff_representative_support 𝕜
        complete regular bundle divisor isomorphism).symm)

end TauCeti.Toric.Fan
