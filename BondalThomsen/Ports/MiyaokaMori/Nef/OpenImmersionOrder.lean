module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LocalUniformizerOrder
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Length

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TopologicalSpace WithZero
open scoped Classical

universe u

noncomputable section

theorem Ring.ord_ringEquiv {sourceRing targetRing : Type*} [CommRing sourceRing] [CommRing targetRing]
    (equivalence : sourceRing ≃+* targetRing) (element : sourceRing) :
    Ring.ord targetRing (equivalence element) = Ring.ord sourceRing element := by
  unfold Ring.ord
  let _ : Algebra sourceRing targetRing := equivalence.toRingHom.toAlgebra
  have surjective : Function.Surjective (algebraMap sourceRing targetRing) := equivalence.surjective
  rw [← Module.length_eq_of_surjective (S := sourceRing) (R := targetRing)
    (M := targetRing ⧸ Ideal.span {equivalence element}) surjective]
  symm
  have image : (Ideal.span {element} : Ideal sourceRing).map equivalence.toRingHom =
      Ideal.span {equivalence element} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let quotientEquiv : (sourceRing ⧸ Ideal.span {element}) ≃+*
      (targetRing ⧸ Ideal.span {equivalence element}) :=
    Ideal.quotientEquiv _ _ equivalence image.symm
  let quotientLinearEquiv : (sourceRing ⧸ Ideal.span {element}) ≃ₗ[sourceRing]
      (targetRing ⧸ Ideal.span {equivalence element}) :=
    { quotientEquiv with
      map_smul' := fun scalar residue => by
        induction residue using Submodule.Quotient.induction_on with
        | H representative =>
          show quotientEquiv (scalar • Ideal.Quotient.mk _ representative) =
            scalar • quotientEquiv (Ideal.Quotient.mk _ representative)
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          rfl }
  exact quotientLinearEquiv.length_eq

theorem Ring.ordMonoidWithZeroHom_ringEquiv {sourceRing targetRing : Type*}
    [CommRing sourceRing] [CommRing targetRing] [Nontrivial sourceRing] [Nontrivial targetRing]
    (equivalence : sourceRing ≃+* targetRing) (element : sourceRing) :
    Ring.ordMonoidWithZeroHom targetRing (equivalence element) = Ring.ordMonoidWithZeroHom sourceRing element := by
  have membership : equivalence element ∈ nonZeroDivisors targetRing ↔ element ∈ nonZeroDivisors sourceRing := by
    rw [← MulEquivClass.map_nonZeroDivisors equivalence, Submonoid.mem_map]
    constructor
    · rintro ⟨preimage, member, equation⟩
      rwa [← equivalence.injective equation]
    · intro member
      exact ⟨element, member, rfl⟩
  by_cases nonzeroDivisor : element ∈ nonZeroDivisors sourceRing
  · rw [Ring.ordMonoidWithZeroHom_eq_ord nonzeroDivisor,
      Ring.ordMonoidWithZeroHom_eq_ord (membership.mpr nonzeroDivisor), Ring.ord_ringEquiv]
  · rw [Ring.ordMonoidWithZeroHom_eq_zero nonzeroDivisor,
      Ring.ordMonoidWithZeroHom_eq_zero (mt membership.mp nonzeroDivisor)]

theorem Ring.ordFrac_ringEquiv {sourceRing targetRing sourceField targetField : Type*}
    [CommRing sourceRing] [CommRing targetRing] [Field sourceField] [Field targetField]
    [IsDomain sourceRing] [IsDomain targetRing] [IsNoetherianRing sourceRing]
    [Ring.KrullDimLE 1 sourceRing] [IsNoetherianRing targetRing] [Ring.KrullDimLE 1 targetRing]
    [Algebra sourceRing sourceField] [IsFractionRing sourceRing sourceField]
    [Algebra targetRing targetField] [IsFractionRing targetRing targetField]
    (equivalence : sourceRing ≃+* targetRing) (fieldMap : sourceField →+* targetField)
    (compatible : ∀ element : sourceRing,
      fieldMap (algebraMap sourceRing sourceField element) = algebraMap targetRing targetField (equivalence element))
    (rational : sourceField) : Ring.ordFrac targetRing (fieldMap rational) = Ring.ordFrac sourceRing rational := by
  obtain ⟨numerator, denominator, denominatorRegular, rfl⟩ := IsFractionRing.div_surjective (A := sourceRing) rational
  have denominatorNonzero : denominator ≠ 0 := nonZeroDivisors.ne_zero denominatorRegular
  have imageDenominatorNonzero : equivalence denominator ≠ 0 :=
    (map_ne_zero_iff equivalence equivalence.injective).mpr denominatorNonzero
  rw [map_div₀, compatible, compatible, map_div₀, map_div₀]
  by_cases numeratorZero : numerator = 0
  · simp [numeratorZero]
  have imageNumeratorNonzero : equivalence numerator ≠ 0 :=
    (map_ne_zero_iff equivalence equivalence.injective).mpr numeratorZero
  rw [Ring.ordFrac_eq_ord targetRing (K := targetField) imageNumeratorNonzero,
    Ring.ordFrac_eq_ord targetRing (K := targetField) imageDenominatorNonzero,
    Ring.ordFrac_eq_ord sourceRing (K := sourceField) numeratorZero,
    Ring.ordFrac_eq_ord sourceRing (K := sourceField) denominatorNonzero,
    Ring.ordMonoidWithZeroHom_ringEquiv, Ring.ordMonoidWithZeroHom_ringEquiv]

namespace AlgebraicGeometry.OpenImmersionOrder

variable {source target : Scheme.{u}} (morphism : source ⟶ target)
  [IsOpenImmersion morphism] [IsIntegral source] [IsIntegral target]

def functionFieldMap : target.functionField →+* source.functionField :=
  ((target.presheaf.stalkSpecializes (specializes_of_eq (genericPoint_eq_of_isOpenImmersion morphism))) ≫
    morphism.stalkMap (genericPoint source)).hom

theorem functionFieldMap_algebraMap (point : source) (element : target.presheaf.stalk (morphism point)) :
    functionFieldMap morphism (algebraMap (target.presheaf.stalk (morphism point)) target.functionField element) =
      algebraMap (source.presheaf.stalk point) source.functionField (morphism.stalkMap point element) := by
  have specialization : genericPoint source ⤳ point := (genericPoint_spec source).specializes trivial
  have naturality := Scheme.Hom.stalkSpecializes_stalkMap_apply morphism (genericPoint source) point
    specialization element
  have composition := congrArg (fun homomorphism => homomorphism.hom element)
    (target.presheaf.stalkSpecializes_comp
      (specializes_of_eq (genericPoint_eq_of_isOpenImmersion morphism))
      ((genericPoint_spec target).specializes (Set.mem_univ (morphism point))))
  change morphism.stalkMap (genericPoint source)
    (target.presheaf.stalkSpecializes _ (target.presheaf.stalkSpecializes _ element)) =
      source.presheaf.stalkSpecializes specialization (morphism.stalkMap point element)
  rw [← naturality]
  exact congrArg _ composition

theorem ord_functionFieldMap [IsLocallyNoetherian source] [IsLocallyNoetherian target]
    (rational : target.functionField) (point : source) :
    source.ord (functionFieldMap morphism rational) point = target.ord rational (morphism point) := by
  have coheight : Order.coheight (morphism point) = Order.coheight point := coheight_eq_of_isOpenImmersion morphism
  by_cases sourceCoheight : Order.coheight point = 1
  · have targetCoheight : Order.coheight (morphism point) = 1 := coheight.trans sourceCoheight
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one sourceCoheight,
      Scheme.ord_eq_ordHom_of_coheight_eq_one targetCoheight]
    congr 2
    have : Ring.KrullDimLE 1 (source.presheaf.stalk point) := krullDimLE_of_coheight_le sourceCoheight.le
    have : Ring.KrullDimLE 1 (target.presheaf.stalk (morphism point)) := krullDimLE_of_coheight_le targetCoheight.le
    exact Ring.ordFrac_ringEquiv (asIso (morphism.stalkMap point)).commRingCatIsoToRingEquiv
      (functionFieldMap morphism) (functionFieldMap_algebraMap morphism point) rational
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one sourceCoheight,
      Scheme.ord_eq_zero_of_coheight_neq_one (by rwa [coheight])]

end AlgebraicGeometry.OpenImmersionOrder
