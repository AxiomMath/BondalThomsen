module

public import BondalThomsen.Toric.Positivity.AmpleStrictSupportConverse
public import BondalThomsen.LineBundle.AmpleLineBundleGlobalGeneration
public import BondalThomsen.Ports.MiyaokaMori.InvertibleSheafTensorPowerCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace BondalThomsen

variable {scheme : AlgebraicGeometry.Scheme.{0}} [IsIntegral scheme]

local instance cartierSheafInvertible (divisor : CartierDivisor scheme) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme divisor.sheaf :=
  CartierDivisor.isInvertible_sheaf divisor

def cartierSectionValue (divisor : CartierDivisor scheme)
    (open_set : scheme.Opens) [Nonempty open_set]
    (section_value : Γ(divisor.sheaf, open_set)) : scheme.functionField :=
  rationalFunctionsEquiv open_set
    (Scheme.Modules.Hom.app divisor.sheafι open_set section_value)

theorem cartierSectionValue_res (divisor : CartierDivisor scheme)
    {smaller larger : scheme.Opens} [Nonempty smaller] [Nonempty larger]
    (contained : smaller ≤ larger) (section_value : Γ(divisor.sheaf, larger)) :
    cartierSectionValue divisor smaller (divisor.sheaf.res contained section_value) =
      cartierSectionValue divisor larger section_value := by
  have naturality := (PresheafOfModules.naturality_apply divisor.sheafι.val
    (homOfLE contained).op section_value).symm
  calc
    _ = rationalFunctionsEquiv smaller
        ((rationalFunctions scheme).presheaf.map (homOfLE contained).op
          (Scheme.Modules.Hom.app divisor.sheafι larger section_value)) :=
      congrArg (rationalFunctionsEquiv smaller) naturality
    _ = _ := rationalFunctionsEquiv_map (homOfLE contained) _

theorem cartierGermToFunctionField_res {smaller larger : scheme.Opens}
    [Nonempty smaller] [Nonempty larger] (contained : smaller ≤ larger)
    (section_value : Γ(scheme, larger)) :
    scheme.germToFunctionField smaller
        (scheme.presheaf.map (homOfLE contained).op section_value) =
      scheme.germToFunctionField larger section_value := by
  exact scheme.presheaf.germ_res_apply (homOfLE contained)
    (genericPoint scheme) (genericPoint_mem smaller) section_value

theorem cartierTwistEquation (first second : CartierDivisor scheme)
    (open_set : scheme.Opens) [Nonempty open_set]
    (first_equation second_equation : scheme.functionFieldˣ)
    (first_equal : rationalUnitClass scheme open_set (Additive.ofMul first_equation) =
      first |_ open_set)
    (second_equal : rationalUnitClass scheme open_set (Additive.ofMul second_equation) =
      second |_ open_set) (exponent : ℕ) :
    rationalUnitClass scheme open_set
        (Additive.ofMul (second_equation * first_equation ^ exponent)) =
      (second + exponent • first) |_ open_set := by
  rw [ofMul_mul, ofMul_pow, map_add, map_nsmul,
    first_equal, second_equal]
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_add, map_nsmul]

def cartierEquationGenerator (divisor : CartierDivisor scheme)
    (open_set : scheme.Opens) [Nonempty open_set]
    (equation : scheme.functionFieldˣ)
    (equation_equal : rationalUnitClass scheme open_set (Additive.ofMul equation) =
      divisor |_ open_set) : Γ(divisor.sheaf, open_set) :=
  CartierDivisor.sectionMk ((rationalFunctionsEquiv open_set).symm (equation⁻¹ :
    scheme.functionFieldˣ))
    ((CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq le_rfl equation_equal).mpr
      ⟨1, by simp⟩)

theorem cartierEquationGenerator_value (divisor : CartierDivisor scheme)
    (open_set : scheme.Opens) [Nonempty open_set] (equation : scheme.functionFieldˣ)
    (equation_equal : rationalUnitClass scheme open_set (Additive.ofMul equation) =
      divisor |_ open_set) :
    cartierSectionValue divisor open_set
        (cartierEquationGenerator divisor open_set equation equation_equal) =
      (equation⁻¹ : scheme.functionFieldˣ) :=
  (rationalFunctionsEquiv open_set).apply_symm_apply _

theorem cartierSectionValue_smul (divisor : CartierDivisor scheme)
    (open_set : scheme.Opens) [Nonempty open_set] (scalar : Γ(scheme, open_set))
    (section_value : Γ(divisor.sheaf, open_set)) :
    cartierSectionValue divisor open_set (scalar • section_value) =
      scheme.germToFunctionField open_set scalar *
        cartierSectionValue divisor open_set section_value := by
  unfold cartierSectionValue
  rw [Scheme.Modules.Hom.app_smul, map_smul, Algebra.smul_def]
  rfl

theorem cartierSectionValue_injective (divisor : CartierDivisor scheme)
    (open_set : scheme.Opens) [Nonempty open_set] :
    Function.Injective (cartierSectionValue divisor open_set) :=
  (rationalFunctionsEquiv open_set).injective.comp (divisor.sheafι_app_injective open_set)

theorem cartierEquationGenerator_isFrame (divisor : CartierDivisor scheme)
    (open_set : scheme.Opens) [Nonempty open_set] (equation : scheme.functionFieldˣ)
    (equation_equal : rationalUnitClass scheme open_set (Additive.ofMul equation) =
      divisor |_ open_set) :
    Scheme.Modules.IsFrame divisor.sheaf open_set
      (cartierEquationGenerator divisor open_set equation equation_equal) := by
  intro smaller contained
  rcases isEmpty_or_nonempty smaller with empty | nonempty
  · have empty_equal : smaller = ⊥ := by
      apply Opens.ext
      ext point
      exact ⟨fun member => empty.elim ⟨point, member⟩, False.elim⟩
    subst smaller
    have := subsingleton_rationalFunctions (X := scheme) ⊥ rfl
    constructor
    · intro first_scalar second_scalar equal
      exact Subsingleton.elim _ _
    · intro section_value
      refine ⟨0, ?_⟩
      exact divisor.sheafι_app_injective ⊥ (Subsingleton.elim _ _)
  · have : Nonempty smaller := nonempty
    have generator_value : cartierSectionValue divisor smaller
        (divisor.sheaf.res contained
          (cartierEquationGenerator divisor open_set equation equation_equal)) =
        (equation⁻¹ : scheme.functionFieldˣ) := by
      rw [cartierSectionValue_res, cartierEquationGenerator_value]
    constructor
    · intro first_scalar second_scalar equal
      have values := congrArg (cartierSectionValue divisor smaller) equal
      rw [cartierSectionValue_smul, cartierSectionValue_smul, generator_value] at values
      apply scheme.germToFunctionField_injective smaller
      exact mul_right_cancel₀ (Units.ne_zero equation⁻¹) values
    · intro section_value
      obtain ⟨scalar, scalar_equal⟩ :=
        (CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq contained equation_equal).mp
          (divisor.sheafι_app_mem smaller section_value)
      refine ⟨scalar, (cartierSectionValue_injective divisor smaller) ?_⟩
      rw [cartierSectionValue_smul, generator_value, scalar_equal]
      change (equation : scheme.functionField) *
        cartierSectionValue divisor smaller section_value * ↑equation⁻¹ = _
      rw [mul_right_comm, Units.mul_inv, one_mul]

theorem cartierEquationFrame_coordinateValue (divisor : CartierDivisor scheme)
    (open_set : scheme.Opens) [Nonempty open_set] (equation : scheme.functionFieldˣ)
    (equation_equal : rationalUnitClass scheme open_set (Additive.ofMul equation) =
      divisor |_ open_set) (global_section : Γ(divisor.sheaf, ⊤)) :
    scheme.germToFunctionField open_set
        ((cartierEquationGenerator_isFrame divisor open_set equation equation_equal).coord
          le_rfl (divisor.sheaf.res le_top global_section)) =
      equation * cartierSectionValue divisor ⊤ global_section := by
  have equal := congrArg (cartierSectionValue divisor open_set)
    ((cartierEquationGenerator_isFrame divisor open_set equation equation_equal).coord_smul_frame
      le_rfl (divisor.sheaf.res le_top global_section))
  rw [Scheme.Modules.res_self, cartierSectionValue_smul,
    cartierEquationGenerator_value, cartierSectionValue_res] at equal
  have multiplied := congrArg (fun value : scheme.functionField => value * equation) equal
  rw [mul_assoc, Units.inv_mul, mul_one] at multiplied
  simpa only [mul_comm] using multiplied

theorem cartierAffineBasicOpen_clearDenominator
    (first second : CartierDivisor scheme) (open_set : scheme.Opens)
    [Nonempty open_set] (affine : IsAffineOpen open_set)
    (first_equation second_equation : scheme.functionFieldˣ)
    (first_equal : rationalUnitClass scheme open_set (Additive.ofMul first_equation) =
      first |_ open_set)
    (second_equal : rationalUnitClass scheme open_set (Additive.ofMul second_equation) =
      second |_ open_set)
    (global_section : Γ(first.sheaf, ⊤)) (coefficient : Γ(scheme, open_set))
    (coefficient_equal : scheme.germToFunctionField open_set coefficient =
      first_equation * cartierSectionValue first ⊤ global_section)
    [Nonempty (scheme.basicOpen coefficient)]
    (local_section : Γ(second.sheaf, scheme.basicOpen coefficient)) :
    ∃ exponent : ℕ, ∀ larger_exponent : ℕ, exponent ≤ larger_exponent →
      ∃ extended_section : Γ((second + larger_exponent • first).sheaf, open_set),
        cartierSectionValue (second + larger_exponent • first) open_set extended_section =
          cartierSectionValue second (scheme.basicOpen coefficient) local_section *
            cartierSectionValue first ⊤ global_section ^ larger_exponent := by
  obtain ⟨local_coefficient, local_equal⟩ :=
    (CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq
      (scheme.basicOpen_le coefficient) second_equal).mp
      (second.sheafι_app_mem _ local_section)
  obtain ⟨exponent, lifted_coefficient, lifted_equal⟩ :=
    exists_eq_pow_mul_of_isAffineOpen scheme open_set affine coefficient local_coefficient
  have lifted_value : scheme.germToFunctionField open_set lifted_coefficient =
      (first_equation * cartierSectionValue first ⊤ global_section) ^ exponent *
        (second_equation *
          cartierSectionValue second (scheme.basicOpen coefficient) local_section) := by
    have equal := congrArg (scheme.germToFunctionField (scheme.basicOpen coefficient))
      lifted_equal
    change scheme.germToFunctionField (scheme.basicOpen coefficient)
      (scheme.presheaf.map (homOfLE (scheme.basicOpen_le coefficient)).op lifted_coefficient) =
      scheme.germToFunctionField (scheme.basicOpen coefficient)
        ((scheme.presheaf.map (homOfLE (scheme.basicOpen_le coefficient)).op coefficient) ^
          exponent * local_coefficient) at equal
    rw [cartierGermToFunctionField_res, map_mul, map_pow,
      cartierGermToFunctionField_res, coefficient_equal, local_equal] at equal
    exact equal
  refine ⟨exponent, fun larger_exponent larger => ?_⟩
  let rational_value :=
    cartierSectionValue second (scheme.basicOpen coefficient) local_section *
      cartierSectionValue first ⊤ global_section ^ larger_exponent
  let rational_section := (rationalFunctionsEquiv open_set).symm rational_value
  have regular_value : scheme.germToFunctionField open_set
      (coefficient ^ (larger_exponent - exponent) * lifted_coefficient) =
        (second_equation * first_equation ^ larger_exponent) * rational_value := by
    rw [map_mul, map_pow, coefficient_equal, lifted_value, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel larger]
    dsimp only [rational_value]
    simp only [mul_pow]
    ring
  have membership : rational_section ∈ (second + larger_exponent • first).sections open_set := by
    apply (CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq le_rfl
      (cartierTwistEquation first second open_set first_equation second_equation
        first_equal second_equal larger_exponent)).mpr
    exact ⟨coefficient ^ (larger_exponent - exponent) * lifted_coefficient, by
      simpa only [rational_section, LinearEquiv.apply_symm_apply,
        Units.val_mul, Units.val_pow_eq_pow_val] using regular_value⟩
  refine ⟨CartierDivisor.sectionMk rational_section membership, ?_⟩
  exact (rationalFunctionsEquiv open_set).apply_symm_apply rational_value

theorem exists_affine_commonCartierEquations (first second : CartierDivisor scheme)
    (point : scheme) :
    ∃ (open_set : scheme.Opens) (contains : point ∈ open_set),
      IsAffineOpen open_set ∧
        ∃ first_equation second_equation : scheme.functionFieldˣ,
          letI : Nonempty open_set := ⟨⟨point, contains⟩⟩
          rationalUnitClass scheme open_set (Additive.ofMul first_equation) =
            first |_ open_set ∧
          rationalUnitClass scheme open_set (Additive.ofMul second_equation) =
            second |_ open_set := by
  obtain ⟨first_open, first_contained, first_contains, first_equation, first_equal⟩ :=
    first.exists_localEquation_le ⊤ (x := point) trivial
  obtain ⟨second_open, second_contained, second_contains, second_equation, second_equal⟩ :=
    second.exists_localEquation_le first_open first_contains
  obtain ⟨open_set, affine, contains, contained⟩ :=
    exists_isAffineOpen_mem_and_subset second_contains
  have : Nonempty first_open := ⟨⟨point, first_contains⟩⟩
  have : Nonempty second_open := ⟨⟨point, second_contains⟩⟩
  have : Nonempty open_set := ⟨⟨point, contains⟩⟩
  exact ⟨open_set, contains, affine, first_equation, second_equation,
    CartierDivisor.rationalUnitClass_eq_of_le (contained.trans second_contained) first_equal,
    CartierDivisor.rationalUnitClass_eq_of_le contained second_equal⟩

theorem cartierNonvanishingLocus_nonempty_of_value_ne_zero
    (divisor : CartierDivisor scheme) (global_section : Γ(divisor.sheaf, ⊤))
    (nonzero : cartierSectionValue divisor ⊤ global_section ≠ 0)
    (open_set : scheme.Opens) [Nonempty open_set] (equation : scheme.functionFieldˣ)
    (equation_equal : rationalUnitClass scheme open_set (Additive.ofMul equation) =
      divisor |_ open_set) :
    Nonempty (scheme.basicOpen
      ((cartierEquationGenerator_isFrame divisor open_set equation equation_equal).coord
        le_rfl (divisor.sheaf.res le_top global_section))) := by
  let coefficient :=
    (cartierEquationGenerator_isFrame divisor open_set equation equation_equal).coord
      le_rfl (divisor.sheaf.res le_top global_section)
  by_contra empty
  have open_empty : scheme.basicOpen coefficient = ⊥ := by
    apply Opens.ext
    ext point
    exact ⟨fun contains => empty ⟨⟨point, contains⟩⟩, False.elim⟩
  have zero := eq_zero_of_basicOpen_eq_bot coefficient open_empty
  have value := cartierEquationFrame_coordinateValue divisor open_set equation
    equation_equal global_section
  change scheme.germToFunctionField open_set coefficient = _ at value
  rw [zero, map_zero] at value
  exact (mul_ne_zero (Units.ne_zero equation) nonzero) value.symm

theorem cartierSection_extend_from_nonvanishingLocus
    [CompactSpace scheme] (first second : CartierDivisor scheme)
    (global_section : Γ(first.sheaf, ⊤))
    [Nonempty (first.sheaf.nonvanishingLocus global_section)]
    (nonzero : cartierSectionValue first ⊤ global_section ≠ 0)
    (local_section : Γ(second.sheaf, first.sheaf.nonvanishingLocus global_section)) :
    ∃ exponent : ℕ, ∀ larger_exponent : ℕ, exponent ≤ larger_exponent →
      ∃ extended_section : Γ((second + larger_exponent • first).sheaf, ⊤),
        cartierSectionValue (second + larger_exponent • first) ⊤ extended_section =
          cartierSectionValue second (first.sheaf.nonvanishingLocus global_section)
            local_section * cartierSectionValue first ⊤ global_section ^ larger_exponent := by
  classical
  choose opens contains affine first_equation second_equation first_equal second_equal using
    exists_affine_commonCartierEquations first second
  let (point : scheme) : Nonempty (opens point) := ⟨⟨point, contains point⟩⟩
  let frames := fun point => cartierEquationGenerator_isFrame first (opens point)
    (first_equation point) (first_equal point)
  let coefficient := fun point => (frames point).coord le_rfl
    (first.sheaf.res le_top global_section)
  have coordinate_values : ∀ point,
      scheme.germToFunctionField (opens point) (coefficient point) =
        first_equation point * cartierSectionValue first ⊤ global_section :=
    fun point => cartierEquationFrame_coordinateValue first (opens point)
      (first_equation point) (first_equal point) global_section
  have basic_contained : ∀ point,
      scheme.basicOpen (coefficient point) ≤ first.sheaf.nonvanishingLocus global_section := by
    intro point
    rw [← (frames point).inf_nonvanishingLocus_eq_basicOpen first.sheaf global_section]
    exact inf_le_right
  let (point : scheme) : Nonempty (scheme.basicOpen (coefficient point)) :=
    cartierNonvanishingLocus_nonempty_of_value_ne_zero first global_section nonzero
      (opens point) (first_equation point) (first_equal point)
  have local_lifts : ∀ point : scheme, ∃ exponent : ℕ,
      ∀ larger_exponent : ℕ, exponent ≤ larger_exponent →
        ∃ extended_section : Γ((second + larger_exponent • first).sheaf, opens point),
          cartierSectionValue (second + larger_exponent • first) (opens point)
              extended_section =
            cartierSectionValue second (first.sheaf.nonvanishingLocus global_section)
              local_section * cartierSectionValue first ⊤ global_section ^ larger_exponent := by
    intro point
    obtain ⟨exponent, lifts⟩ := cartierAffineBasicOpen_clearDenominator first second
      (opens point) (affine point) (first_equation point) (second_equation point)
      (first_equal point) (second_equal point) global_section (coefficient point)
      (coordinate_values point) (second.sheaf.res (basic_contained point) local_section)
    refine ⟨exponent, fun larger_exponent larger => ?_⟩
    obtain ⟨extended_section, equal⟩ := lifts larger_exponent larger
    exact ⟨extended_section, by rw [cartierSectionValue_res] at equal; exact equal⟩
  choose exponents local_lifts using local_lifts
  obtain ⟨finite_cover, subset, cover⟩ := isCompact_univ.elim_nhds_subcover
    (fun point => ((opens point : scheme.Opens) : Set scheme))
    (fun point _ => (opens point).isOpen.mem_nhds (contains point))
  refine ⟨finite_cover.sup exponents, fun larger_exponent larger => ?_⟩
  let rational_value :=
    cartierSectionValue second (first.sheaf.nonvanishingLocus global_section) local_section *
      cartierSectionValue first ⊤ global_section ^ larger_exponent
  let rational_section := (rationalFunctionsEquiv (⊤ : scheme.Opens)).symm rational_value
  have membership : rational_section ∈ (second + larger_exponent • first).sections ⊤ := by
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro point point_contains
    have covered := cover (Set.mem_univ point)
    rw [Set.mem_iUnion₂] at covered
    obtain ⟨chart_point, chart_mem, chart_contains⟩ := covered
    obtain ⟨extended_section, extended_equal⟩ := local_lifts chart_point larger_exponent
      ((Finset.le_sup (f := exponents) chart_mem).trans larger)
    let equation := second_equation chart_point * first_equation chart_point ^ larger_exponent
    have equation_equal := cartierTwistEquation first second (opens chart_point)
      (first_equation chart_point) (second_equation chart_point)
      (first_equal chart_point) (second_equal chart_point) larger_exponent
    have local_equation := CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
      equation_equal chart_contains
    refine ⟨equation, local_equation, ?_⟩
    have local_member := (second + larger_exponent • first).sheafι_app_mem
      (opens chart_point) extended_section
    have member := local_member point chart_contains equation local_equation
    change (equation : scheme.functionField) *
      cartierSectionValue (second + larger_exponent • first) (opens chart_point)
        extended_section ∈ _ at member
    rw [extended_equal] at member
    simpa only [rational_section, LinearEquiv.apply_symm_apply, rational_value] using member
  refine ⟨CartierDivisor.sectionMk rational_section membership, ?_⟩
  exact (rationalFunctionsEquiv (⊤ : scheme.Opens)).apply_symm_apply rational_value

theorem cartierSectionValue_ne_zero_of_nonvanishing
    (divisor : CartierDivisor scheme) (global_section : Γ(divisor.sheaf, ⊤))
    (point : scheme) (nonvanishing : point ∈ divisor.sheaf.nonvanishingLocus global_section) :
    cartierSectionValue divisor ⊤ global_section ≠ 0 := by
  obtain ⟨open_set, contains, affine, equation, second_equation, equation_equal, second_equal⟩ :=
    exists_affine_commonCartierEquations divisor divisor point
  have : Nonempty open_set := ⟨⟨point, contains⟩⟩
  let frame := cartierEquationGenerator_isFrame divisor open_set equation equation_equal
  let coefficient := frame.coord le_rfl (divisor.sheaf.res le_top global_section)
  have member : point ∈ scheme.basicOpen coefficient := by
    rw [← frame.inf_nonvanishingLocus_eq_basicOpen divisor.sheaf global_section]
    exact ⟨contains, nonvanishing⟩
  intro zero_value
  have value := cartierEquationFrame_coordinateValue divisor open_set equation
    equation_equal global_section
  change scheme.germToFunctionField open_set coefficient = _ at value
  rw [zero_value, mul_zero] at value
  have coefficient_zero : coefficient = 0 :=
    scheme.germToFunctionField_injective open_set (by simpa only [map_zero] using value)
  rw [coefficient_zero, scheme.basicOpen_zero] at member
  exact member

theorem cartierLocalEquation_nsmul (divisor : CartierDivisor scheme)
    (point : scheme) (equation : scheme.functionFieldˣ)
    (local_equation : divisor.IsLocalEquationAt point equation) (exponent : ℕ) :
    (exponent • divisor).IsLocalEquationAt point (equation ^ exponent) := by
  induction exponent with
  | zero => simpa only [zero_nsmul, pow_zero] using CartierDivisor.isLocalEquationAt_zero point
  | succ exponent induction_hypothesis =>
      simpa only [pow_succ, succ_nsmul] using induction_hypothesis.mul local_equation

def cartierSectionProductPower (first second : CartierDivisor scheme)
    (open_set : scheme.Opens) [Nonempty open_set]
    (first_section : Γ(first.sheaf, open_set)) (second_section : Γ(second.sheaf, open_set))
    (exponent : ℕ) : Γ((second + exponent • first).sheaf, open_set) := by
  let rational_value := cartierSectionValue second open_set second_section *
    cartierSectionValue first open_set first_section ^ exponent
  let rational_section := (rationalFunctionsEquiv open_set).symm rational_value
  have membership : rational_section ∈ (second + exponent • first).sections open_set := by
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro point contains
    obtain ⟨first_equation, first_local⟩ := first.exists_isLocalEquationAt point
    obtain ⟨second_equation, second_local⟩ := second.exists_isLocalEquationAt point
    let equation := second_equation * first_equation ^ exponent
    have local_equation := second_local.mul
      (cartierLocalEquation_nsmul first point first_equation first_local exponent)
    refine ⟨equation, local_equation, ?_⟩
    have first_member := first.sheafι_app_mem open_set first_section point contains
      first_equation first_local
    have second_member := second.sheafι_app_mem open_set second_section point contains
      second_equation second_local
    have member := Subring.mul_mem _ second_member (Subring.pow_mem _ first_member exponent)
    change ↑second_equation * cartierSectionValue second open_set second_section *
      (↑first_equation * cartierSectionValue first open_set first_section) ^ exponent ∈ _ at member
    have value_equal : (equation : scheme.functionField) * rational_value =
        ↑second_equation * cartierSectionValue second open_set second_section *
          (↑first_equation * cartierSectionValue first open_set first_section) ^ exponent := by
      dsimp only [equation, rational_value]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow]
      ring
    simpa only [rational_section, LinearEquiv.apply_symm_apply, value_equal] using member
  exact CartierDivisor.sectionMk rational_section membership

theorem cartierSectionProductPower_value (first second : CartierDivisor scheme)
    (open_set : scheme.Opens) [Nonempty open_set]
    (first_section : Γ(first.sheaf, open_set)) (second_section : Γ(second.sheaf, open_set))
    (exponent : ℕ) :
    cartierSectionValue (second + exponent • first) open_set
        (cartierSectionProductPower first second open_set first_section second_section exponent) =
      cartierSectionValue second open_set second_section *
        cartierSectionValue first open_set first_section ^ exponent :=
  (rationalFunctionsEquiv open_set).apply_symm_apply _

theorem cartierSection_extend_actual_restriction
    [CompactSpace scheme] (first second : CartierDivisor scheme)
    (global_section : Γ(first.sheaf, ⊤))
    [Nonempty (first.sheaf.nonvanishingLocus global_section)]
    (local_section : Γ(second.sheaf, first.sheaf.nonvanishingLocus global_section)) :
    ∃ exponent : ℕ, ∀ larger_exponent : ℕ, exponent ≤ larger_exponent →
      ∃ extended_section : Γ((second + larger_exponent • first).sheaf, ⊤),
        (second + larger_exponent • first).sheaf.res le_top extended_section =
          cartierSectionProductPower first second (first.sheaf.nonvanishingLocus global_section)
            (first.sheaf.res le_top global_section) local_section larger_exponent := by
  obtain ⟨point⟩ := ‹Nonempty (first.sheaf.nonvanishingLocus global_section)›
  obtain ⟨exponent, extensions⟩ := cartierSection_extend_from_nonvanishingLocus first second
    global_section (cartierSectionValue_ne_zero_of_nonvanishing first global_section
      point.val point.property) local_section
  refine ⟨exponent, fun larger_exponent larger => ?_⟩
  obtain ⟨extended_section, equal⟩ := extensions larger_exponent larger
  refine ⟨extended_section, (cartierSectionValue_injective _ _) ?_⟩
  rw [cartierSectionValue_res, equal, cartierSectionProductPower_value, cartierSectionValue_res]

end BondalThomsen

namespace TauCeti.Toric.Fan

local instance invariantCartierSheafInvertible
    {scheme : AlgebraicGeometry.Scheme.{0}} [IsIntegral scheme]
    (divisor : CartierDivisor scheme) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme divisor.sheaf :=
  CartierDivisor.isInvertible_sheaf divisor

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

def actualInvariantAmplePowerCartierIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (exponent : ℕ) :
    Scheme.Modules.tensorPow
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj exponent ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular (exponent • divisor)).obj :=
  (BondalThomsen.MiyaokaMori.invertibleSheafTensorPowerIso
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor) exponent).symm ≪≫
      fan.invariantDivisorTensorPowerIso 𝕜 complete regular divisor exponent

theorem exists_positiveInvariantPower_affineNonvanishing (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (ample : IsAmple (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj)
    (point : fan.algebraicRealization 𝕜 regular) :
    ∃ (exponent : ℕ) (_ : 0 < exponent)
      (section_value : Γ((fan.invariantDivisorLineBundle 𝕜 complete regular
        (exponent • divisor)).obj, ⊤)),
      point ∈ (fan.invariantDivisorLineBundle 𝕜 complete regular
        (exponent • divisor)).obj.nonvanishingLocus section_value ∧
      IsAffineOpen ((fan.invariantDivisorLineBundle 𝕜 complete regular
        (exponent • divisor)).obj.nonvanishingLocus section_value) := by
  obtain ⟨exponent, positive, section_value, contains, affine⟩ := ample.2 point
  let comparison := fan.actualInvariantAmplePowerCartierIso 𝕜 complete regular divisor exponent
  refine ⟨exponent, positive, Scheme.Modules.Hom.app comparison.hom ⊤ section_value, ?_, ?_⟩
  · exact (Scheme.Modules.mem_nonvanishingLocus_iso comparison section_value point).mpr contains
  · rw [Scheme.Modules.nonvanishingLocus_iso]
    exact affine

def actualInvariantCartierTwistIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor) (exponent : ℕ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.invariantDivisorCartier 𝕜 complete regular second +
      exponent • fan.invariantDivisorCartier 𝕜 complete regular first).sheaf ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular (second + exponent • first)).obj := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  apply eqToIso
  congr 1
  exact ((fan.invariantDivisorCartierHom 𝕜 complete regular).map_add second
    (exponent • first)).trans
      (congrArg (fun cartier => fan.invariantDivisorCartier 𝕜 complete regular second + cartier)
        ((fan.invariantDivisorCartierHom 𝕜 complete regular).map_nsmul exponent first)) |>.symm

def actualNegativeRayTwistCartierIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (ray : fan.Ray) (exponent : ℕ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (fan.invariantDivisorCartier 𝕜 complete regular (-Finsupp.single ray 1) +
      exponent • fan.invariantDivisorCartier 𝕜 complete regular divisor).sheaf ≅
        (fan.invariantDivisorLineBundle 𝕜 complete regular
          (fan.negativeRayTwistDivisor divisor ray exponent)).obj :=
  fan.actualInvariantCartierTwistIso 𝕜 complete regular divisor (-Finsupp.single ray 1)
    exponent ≪≫ eqToIso (congrArg
      (fun coefficients => (fan.invariantDivisorLineBundle 𝕜 complete regular coefficients).obj)
      (show -Finsupp.single ray 1 + exponent • divisor =
        fan.negativeRayTwistDivisor divisor ray exponent from by
          simp only [negativeRayTwistDivisor, sub_eq_add_neg, add_comm]))

end TauCeti.Toric.Fan
