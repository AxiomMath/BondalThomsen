module

public import BondalThomsen.Fan.MoriCone
public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable section

variable {baseField : Type} [Field baseField] {scheme : Scheme.{0}}
    [scheme.Over (Spec (CommRingCat.of baseField))]

def numericalPicardHom (numericalClass : numericalCurveSpace baseField scheme) :
    Additive (LineBundleClass scheme) →+ ℝ where
  toFun := numericalClass.val
  map_zero' := (numericalCurveSpace_isAdditive numericalClass).1
  map_add' := (numericalCurveSpace_isAdditive numericalClass).2

end

end BondalThomsen

namespace TauCeti.Toric.Fan

noncomputable section

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable {𝕜} in
local instance numericalConeBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

def numericalRayPicardClass (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (ray : fan.Ray) :
    Additive (LineBundleClass (fan.algebraicRealization 𝕜 regular)) :=
  fan.invariantDivisorPicardEquiv 𝕜 complete regular
    (fan.invariantRayDivisorClass (Finsupp.single ray 1))

def numericalRayCoordinates (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular) →ₗ[ℝ]
      (fan.Ray → ℝ) where
  toFun numericalClass ray := numericalClass.val (fan.numericalRayPicardClass 𝕜 complete regular ray)
  map_add' first second := by ext ray; rfl
  map_smul' scalar numericalClass := by ext ray; rfl

theorem numericalRayCoordinates_injective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    Function.Injective (fan.numericalRayCoordinates 𝕜 complete regular) := by
  intro first second coordinatesEqual
  let coefficientPicard :=
    (fan.invariantDivisorPicardEquiv 𝕜 complete regular).toAddMonoidHom.comp
      fan.invariantRayDivisorClass
  have coefficientEqual :
      (BondalThomsen.numericalPicardHom first).comp coefficientPicard =
        (BondalThomsen.numericalPicardHom second).comp coefficientPicard := by
    apply Finsupp.addHom_ext'
    intro ray
    apply AddMonoidHom.ext_int
    exact congrFun coordinatesEqual ray
  apply Subtype.ext
  funext bundleClass
  obtain ⟨divisor, divisorEquality⟩ :=
    fan.invariantDivisorPicard_coefficients_surjective 𝕜 complete regular bundleClass
  have evaluated := DFunLike.congr_fun coefficientEqual divisor
  change first.val (coefficientPicard divisor) = second.val (coefficientPicard divisor) at evaluated
  change coefficientPicard divisor = bundleClass at divisorEquality
  simpa only [divisorEquality] using evaluated

theorem numericalRayCoordinates_continuous (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    Continuous (fan.numericalRayCoordinates 𝕜 complete regular) := by
  apply continuous_pi
  intro ray
  exact (continuous_apply (fan.numericalRayPicardClass 𝕜 complete regular ray)).comp
    continuous_subtype_val

def numericalRealPicardFunctional (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (coefficients : fan.Ray → ℝ) :
    BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular) →ₗ[ℝ] ℝ := by
  classical
  letI := Fintype.ofFinite fan.Ray
  exact
    { toFun := fun numericalClass => ∑ ray, coefficients ray *
        numericalClass.val (fan.numericalRayPicardClass 𝕜 complete regular ray)
      map_add' := by
        intro first second
        simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro scalar numericalClass
        change (∑ ray, coefficients ray * (scalar *
          numericalClass.val (fan.numericalRayPicardClass 𝕜 complete regular ray))) =
          scalar * ∑ ray, coefficients ray *
            numericalClass.val (fan.numericalRayPicardClass 𝕜 complete regular ray)
        simp only [Finset.mul_sum, mul_left_comm] }

theorem numericalLinearFunctional_eq_realPicard (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (functional : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular) →ₗ[ℝ] ℝ) :
    ∃ coefficients : fan.Ray → ℝ,
      functional = fan.numericalRealPicardFunctional 𝕜 complete regular coefficients := by
  classical
  let := Fintype.ofFinite fan.Ray
  let coordinateEquiv := LinearEquiv.ofInjective
    (fan.numericalRayCoordinates 𝕜 complete regular)
    (fan.numericalRayCoordinates_injective 𝕜 complete regular)
  obtain ⟨extension, extensionEquality⟩ :=
    (functional.comp coordinateEquiv.symm.toLinearMap).exists_extend
  refine ⟨fun ray => extension (Pi.single ray 1), ?_⟩
  ext numericalClass
  have evaluated := DFunLike.congr_fun extensionEquality (coordinateEquiv numericalClass)
  have expansion : ∀ coordinates : fan.Ray → ℝ,
      extension coordinates = ∑ ray, extension (Pi.single ray 1) * coordinates ray := by
    intro coordinates
    calc
      extension coordinates = extension (∑ ray, Pi.single ray (coordinates ray)) :=
        congrArg extension (Finset.univ_sum_single coordinates).symm
      _ = ∑ ray, extension (Pi.single ray (coordinates ray)) := map_sum _ _ _
      _ = ∑ ray, extension (Pi.single ray 1) * coordinates ray := by
        apply Finset.sum_congr rfl
        intro ray member
        have singleEquality : Pi.single ray (coordinates ray) =
            coordinates ray • (Pi.single ray 1 : fan.Ray → ℝ) := by
          rw [← Pi.single_smul, smul_eq_mul, mul_one]
        rw [singleEquality, map_smul, smul_eq_mul, mul_comm]
  have evaluationEquality :
      extension (fan.numericalRayCoordinates 𝕜 complete regular numericalClass) =
        functional numericalClass := by
    calc
      extension (fan.numericalRayCoordinates 𝕜 complete regular numericalClass) =
          extension ((fan.numericalRayCoordinates 𝕜 complete regular).range.subtype
            (coordinateEquiv numericalClass)) := rfl
      _ = functional (coordinateEquiv.symm (coordinateEquiv numericalClass)) := evaluated
      _ = functional numericalClass := by rw [LinearEquiv.symm_apply_apply]
  rw [← evaluationEquality, expansion]
  rfl

theorem numericalClosedCone_separation (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (cone : ProperCone ℝ (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)))
    (numericalClass : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular))
    (outside : numericalClass ∉ cone) :
    ∃ coefficients : fan.Ray → ℝ,
      (∀ effectiveClass ∈ cone,
        0 ≤ fan.numericalRealPicardFunctional 𝕜 complete regular coefficients effectiveClass) ∧
      fan.numericalRealPicardFunctional 𝕜 complete regular coefficients numericalClass < 0 := by
  obtain ⟨functional, nonnegative, negative⟩ := cone.hyperplane_separation_point outside
  obtain ⟨coefficients, functionalEquality⟩ :=
    fan.numericalLinearFunctional_eq_realPicard 𝕜 complete regular functional.toLinearMap
  refine ⟨coefficients, ?_, ?_⟩
  · intro effectiveClass membership
    have evaluatedEquality := DFunLike.congr_fun functionalEquality effectiveClass
    change functional effectiveClass =
      fan.numericalRealPicardFunctional 𝕜 complete regular coefficients effectiveClass
      at evaluatedEquality
    rw [← evaluatedEquality]
    exact nonnegative effectiveClass membership
  · have evaluatedEquality := DFunLike.congr_fun functionalEquality numericalClass
    change functional numericalClass =
      fan.numericalRealPicardFunctional 𝕜 complete regular coefficients numericalClass
      at evaluatedEquality
    rw [← evaluatedEquality]
    exact negative

theorem numericalClosedCone_bipolar (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (cone : ProperCone ℝ (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)))
    (numericalClass : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)) :
    numericalClass ∈ cone ↔
      ∀ coefficients : fan.Ray → ℝ,
        (∀ effectiveClass ∈ cone,
          0 ≤ fan.numericalRealPicardFunctional 𝕜 complete regular coefficients effectiveClass) →
        0 ≤ fan.numericalRealPicardFunctional 𝕜 complete regular coefficients numericalClass := by
  constructor
  · intro membership coefficients nonnegative
    exact nonnegative numericalClass membership
  · intro allNonnegative
    by_contra outside
    obtain ⟨coefficients, nonnegative, negative⟩ :=
      fan.numericalClosedCone_separation 𝕜 complete regular cone numericalClass outside
    exact (not_lt_of_ge (allNonnegative coefficients nonnegative)) negative

def numericalMoriProperCone (fan : Fan embedding) (regular : fan.IsRegular) :
    ProperCone ℝ (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)) :=
  { BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular) with
    isClosed' := isClosed_closure }

theorem numericalMoriCone_bipolar (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (numericalClass : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)) :
    numericalClass ∈ BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular) ↔
      ∀ coefficients : fan.Ray → ℝ,
        (∀ effectiveClass ∈ BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular),
          0 ≤ fan.numericalRealPicardFunctional 𝕜 complete regular coefficients effectiveClass) →
        0 ≤ fan.numericalRealPicardFunctional 𝕜 complete regular coefficients numericalClass :=
  fan.numericalClosedCone_bipolar 𝕜 complete regular (fan.numericalMoriProperCone 𝕜 regular)
    numericalClass

end

end TauCeti.Toric.Fan
