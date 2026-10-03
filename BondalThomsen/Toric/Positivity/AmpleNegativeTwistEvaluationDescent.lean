module

public import BondalThomsen.Toric.Positivity.AmpleNegativeTwistGlobalGeneration

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace BondalThomsen

variable {scheme : AlgebraicGeometry.Scheme.{0}} [IsIntegral scheme]

local instance evaluationCartierSheafInvertible (divisor : CartierDivisor scheme) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme divisor.sheaf :=
  CartierDivisor.isInvertible_sheaf divisor

omit [IsIntegral scheme] in
theorem negativeTwistFrame_coordinate_isUnit {sheaf : scheme.Modules}
    {open_set : scheme.Opens} {original_section new_section : Γ(sheaf, open_set)}
    (original_frame : Scheme.Modules.IsFrame sheaf open_set original_section)
    (new_frame : Scheme.Modules.IsFrame sheaf open_set new_section) :
    IsUnit (original_frame.coord le_rfl new_section) := by
  obtain ⟨scalar, scalar_equal⟩ := (new_frame open_set le_rfl).surjective original_section
  rw [Scheme.Modules.res_self] at scalar_equal
  apply isUnit_iff_exists_inv.mpr
  refine ⟨scalar, (original_frame open_set le_rfl).injective ?_⟩
  have original_equal := original_frame.coord_smul_frame le_rfl new_section
  rw [Scheme.Modules.res_self] at original_equal
  rw [Scheme.Modules.res_self, one_smul, mul_comm, mul_smul, original_equal]
  exact scalar_equal

theorem cartierSectionProductPower_isFrame_of_equations
    (first second : CartierDivisor scheme) (open_set : scheme.Opens)
    [Nonempty open_set] (first_equation second_equation : scheme.functionFieldˣ)
    (first_equal : rationalUnitClass scheme open_set (Additive.ofMul first_equation) =
      first |_ open_set)
    (second_equal : rationalUnitClass scheme open_set (Additive.ofMul second_equation) =
      second |_ open_set)
    (first_section : Γ(first.sheaf, open_set)) (second_section : Γ(second.sheaf, open_set))
    (first_frame : Scheme.Modules.IsFrame first.sheaf open_set first_section)
    (second_frame : Scheme.Modules.IsFrame second.sheaf open_set second_section)
    (exponent : ℕ) :
    Scheme.Modules.IsFrame (second + exponent • first).sheaf open_set
      (cartierSectionProductPower first second open_set first_section second_section exponent) := by
  let first_generator := cartierEquationGenerator first open_set first_equation first_equal
  let second_generator := cartierEquationGenerator second open_set second_equation second_equal
  let first_generator_frame := cartierEquationGenerator_isFrame first open_set first_equation first_equal
  let second_generator_frame := cartierEquationGenerator_isFrame second open_set second_equation second_equal
  let first_coefficient := first_generator_frame.coord le_rfl first_section
  let second_coefficient := second_generator_frame.coord le_rfl second_section
  let product_equation := second_equation * first_equation ^ exponent
  have product_equal := cartierTwistEquation first second open_set first_equation second_equation
    first_equal second_equal exponent
  let product_generator := cartierEquationGenerator (second + exponent • first) open_set
    product_equation product_equal
  have representation : cartierSectionProductPower first second open_set first_section
      second_section exponent = (second_coefficient * first_coefficient ^ exponent) •
        product_generator := by
    apply cartierSectionValue_injective (second + exponent • first) open_set
    rw [cartierSectionProductPower_value, cartierSectionValue_smul]
    have first_representation := congrArg (cartierSectionValue first open_set)
      (first_generator_frame.coord_smul_frame le_rfl first_section)
    have second_representation := congrArg (cartierSectionValue second open_set)
      (second_generator_frame.coord_smul_frame le_rfl second_section)
    rw [Scheme.Modules.res_self, cartierSectionValue_smul, cartierEquationGenerator_value]
      at first_representation second_representation
    rw [← first_representation, ← second_representation, map_mul, map_pow]
    change _ = scheme.germToFunctionField open_set second_coefficient *
      scheme.germToFunctionField open_set first_coefficient ^ exponent *
        cartierSectionValue (second + exponent • first) open_set product_generator
    rw [cartierEquationGenerator_value]
    dsimp only [product_equation, first_coefficient, second_coefficient]
    simp only [mul_pow, mul_inv_rev, ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [representation]
  exact negativeTwistFrame_smul_unit (second + exponent • first).sheaf open_set product_generator
    (cartierEquationGenerator_isFrame _ _ product_equation product_equal) _
    ((negativeTwistFrame_coordinate_isUnit second_generator_frame second_frame).mul
      ((negativeTwistFrame_coordinate_isUnit first_generator_frame first_frame).pow exponent))

theorem cartierSectionProductPower_res (first second : CartierDivisor scheme)
    {smaller larger : scheme.Opens} [Nonempty smaller] [Nonempty larger]
    (contained : smaller ≤ larger) (first_section : Γ(first.sheaf, larger))
    (second_section : Γ(second.sheaf, larger)) (exponent : ℕ) :
    (second + exponent • first).sheaf.res contained
        (cartierSectionProductPower first second larger first_section second_section exponent) =
      cartierSectionProductPower first second smaller (first.sheaf.res contained first_section)
        (second.sheaf.res contained second_section) exponent := by
  apply cartierSectionValue_injective _ smaller
  rw [cartierSectionValue_res, cartierSectionProductPower_value,
    cartierSectionProductPower_value, cartierSectionValue_res, cartierSectionValue_res]

theorem cartierAffineNonvanishing_exists_eventual_globalFrame_at
    [CompactSpace scheme] (first second : CartierDivisor scheme)
    (global_section : Γ(first.sheaf, ⊤))
    (affine : IsAffineOpen (first.sheaf.nonvanishingLocus global_section))
    (point : scheme) (contains : point ∈ first.sheaf.nonvanishingLocus global_section) :
    ∃ (bound : ℕ) (neighborhood : scheme.Opens), point ∈ neighborhood ∧
      ∀ exponent : ℕ, bound ≤ exponent →
        ∃ extended_section : Γ((second + exponent • first).sheaf, ⊤),
          Scheme.Modules.IsFrame (second + exponent • first).sheaf neighborhood
            ((second + exponent • first).sheaf.res le_top extended_section) := by
  let nonvanishing := first.sheaf.nonvanishingLocus global_section
  have : Nonempty nonvanishing := ⟨⟨point, contains⟩⟩
  obtain ⟨local_section, second_open, second_contained, second_contains, second_frame⟩ :=
    cartierAffineOpen_exists_section_frame_at second nonvanishing affine point contains
  obtain ⟨first_open, first_contains, first_frame⟩ :=
    exists_frame_neighborhood_of_nonvanishing first.sheaf global_section point contains
  obtain ⟨equation_open, equation_contains, equation_affine, first_equation,
    second_equation, first_equal, second_equal⟩ :=
    exists_affine_commonCartierEquations first second point
  have : Nonempty equation_open := ⟨⟨point, equation_contains⟩⟩
  let neighborhood := second_open ⊓ first_open ⊓ equation_open
  have neighborhood_contains : point ∈ neighborhood :=
    ⟨⟨second_contains, first_contains⟩, equation_contains⟩
  have : Nonempty neighborhood := ⟨⟨point, neighborhood_contains⟩⟩
  have neighborhood_second : neighborhood ≤ second_open := inf_le_left.trans inf_le_left
  have neighborhood_first : neighborhood ≤ first_open := inf_le_left.trans inf_le_right
  have neighborhood_nonvanishing : neighborhood ≤ nonvanishing :=
    neighborhood_second.trans second_contained
  have restricted_first_frame : Scheme.Modules.IsFrame first.sheaf neighborhood
      (first.sheaf.res le_top global_section) := by
    have frame := first_frame.restrict neighborhood_first
    rw [Scheme.Modules.res_res] at frame
    exact frame
  have restricted_second_frame : Scheme.Modules.IsFrame second.sheaf neighborhood
      (second.sheaf.res neighborhood_nonvanishing local_section) := by
    have frame := second_frame.restrict neighborhood_second
    rw [Scheme.Modules.res_res] at frame
    exact frame
  obtain ⟨bound, extensions⟩ := cartierSection_extend_actual_restriction first second
    global_section local_section
  refine ⟨bound, neighborhood, neighborhood_contains, fun exponent larger => ?_⟩
  obtain ⟨extended_section, equal⟩ := extensions exponent larger
  refine ⟨extended_section, ?_⟩
  have local_equal := congrArg ((second + exponent • first).sheaf.res neighborhood_nonvanishing) equal
  rw [Scheme.Modules.res_res, cartierSectionProductPower_res,
    Scheme.Modules.res_res] at local_equal
  rw [local_equal]
  exact cartierSectionProductPower_isFrame_of_equations first second neighborhood
    first_equation second_equation
    (CartierDivisor.rationalUnitClass_eq_of_le inf_le_right first_equal)
    (CartierDivisor.rationalUnitClass_eq_of_le inf_le_right second_equal)
    _ _ restricted_first_frame restricted_second_frame exponent

def cartierTwistMultipleIso (first second : CartierDivisor scheme)
    (power repeats : ℕ) :
    (second + repeats • (power • first)).sheaf ≅
      (second + (power * repeats) • first).sheaf :=
  eqToIso (congrArg CartierDivisor.sheaf (by rw [smul_smul, Nat.mul_comm repeats power]))

theorem cartierAmplePower_exists_eventual_multipleFrame_at
    [CompactSpace scheme] (first second : CartierDivisor scheme)
    (point : scheme)
    (positive_power : ∃ (power : ℕ) (_ : 0 < power)
      (section_value : Γ((power • first).sheaf, ⊤)),
      point ∈ (power • first).sheaf.nonvanishingLocus section_value ∧
        IsAffineOpen ((power • first).sheaf.nonvanishingLocus section_value)) :
    ∃ (power bound : ℕ) (_ : 0 < power) (neighborhood : scheme.Opens),
      point ∈ neighborhood ∧ ∀ repeats : ℕ, bound ≤ repeats →
        ∃ section_value : Γ((second + (power * repeats) • first).sheaf, ⊤),
          Scheme.Modules.IsFrame (second + (power * repeats) • first).sheaf neighborhood
            ((second + (power * repeats) • first).sheaf.res le_top section_value) := by
  obtain ⟨power, positive, section_value, contains, affine⟩ := positive_power
  obtain ⟨bound, neighborhood, neighborhood_contains, extensions⟩ :=
    cartierAffineNonvanishing_exists_eventual_globalFrame_at (power • first) second
      section_value affine point contains
  refine ⟨power, bound, positive, neighborhood, neighborhood_contains, fun repeats larger => ?_⟩
  obtain ⟨extended_section, frame⟩ := extensions repeats larger
  let comparison := cartierTwistMultipleIso first second power repeats
  refine ⟨Scheme.Modules.Hom.app comparison.hom ⊤ extended_section, ?_⟩
  rw [ampleModuleHom_res]
  exact ampleFrame_iso_hom comparison neighborhood _ frame

def cartierTwistDegreeIso (first second : CartierDivisor scheme)
    (first_degree second_degree : ℕ) (equal : first_degree = second_degree) :
    (second + first_degree • first).sheaf ≅ (second + second_degree • first).sheaf :=
  eqToIso (congrArg (fun degree => (second + degree • first).sheaf) equal)

theorem cartierAffinePowerCover_exists_eventual_multiple_generatingSections
    [CompactSpace scheme] (first second : CartierDivisor scheme)
    (affine_powers : ∀ point : scheme,
      ∃ (power : ℕ) (_ : 0 < power) (section_value : Γ((power • first).sheaf, ⊤)),
        point ∈ (power • first).sheaf.nonvanishingLocus section_value ∧
          IsAffineOpen ((power • first).sheaf.nonvanishingLocus section_value)) :
    ∃ (period bound : ℕ) (_ : 0 < period) (_ : 0 < bound),
      ∀ multiple : ℕ, bound ≤ multiple →
        ∃ generators : (second + (period * multiple) • first).sheaf.GeneratingSections,
          generators.IsFiniteType := by
  classical
  choose powers bounds positive charts contains extensions using fun point =>
    cartierAmplePower_exists_eventual_multipleFrame_at first second point (affine_powers point)
  obtain ⟨selected, covers⟩ := CompactSpace.isCompact_univ.elim_finite_subcover
    (fun point : scheme => (charts point : Set scheme))
    (fun point => (charts point).isOpen)
    (fun point _ => Set.mem_iUnion.mpr ⟨point, contains point⟩)
  let period := ∏ point ∈ selected, powers point
  let bound := (∑ point ∈ selected, bounds point) + 1
  have period_positive : 0 < period := Finset.prod_pos fun point member => positive point
  refine ⟨period, bound, period_positive, Nat.succ_pos _, fun multiple larger => ?_⟩
  let repeats := fun point : scheme => (∏ other ∈ selected.erase point, powers other) * multiple
  have repeats_large : ∀ point ∈ selected, bounds point ≤ repeats point := by
    intro point member
    have product_positive : 0 < ∏ other ∈ selected.erase point, powers other :=
      Finset.prod_pos fun other other_member => positive other
    calc
      bounds point ≤ ∑ other ∈ selected, bounds other :=
        Finset.single_le_sum (fun other member => Nat.zero_le _) member
      _ ≤ bound := Nat.le_succ _
      _ ≤ multiple := larger
      _ ≤ repeats point := by
        simpa only [repeats, Nat.succ_eq_add_one, zero_add, one_mul] using
          Nat.mul_le_mul_right multiple product_positive
  have degree_equal : ∀ point ∈ selected, powers point * repeats point = period * multiple := by
    intro point member
    dsimp only [repeats, period]
    rw [← mul_assoc, Finset.mul_prod_erase selected powers member]
  have local_sections : ∀ point ∈ selected,
      ∃ section_value : Γ((second + (period * multiple) • first).sheaf, ⊤),
        Scheme.Modules.IsFrame (second + (period * multiple) • first).sheaf (charts point)
          ((second + (period * multiple) • first).sheaf.res le_top section_value) := by
    intro point member
    obtain ⟨section_value, frame⟩ := extensions point (repeats point) (repeats_large point member)
    let comparison := cartierTwistDegreeIso first second (powers point * repeats point)
      (period * multiple) (degree_equal point member)
    refine ⟨Scheme.Modules.Hom.app comparison.hom ⊤ section_value, ?_⟩
    rw [ampleModuleHom_res]
    exact ampleFrame_iso_hom comparison (charts point) _ frame
  choose sections frames using local_sections
  let Index := {point // point ∈ selected}
  let : Fintype Index := inferInstance
  let finite_charts : Index → scheme.Opens := fun point => charts point.val
  have finite_covers : IsOpenCover finite_charts := by
    apply IsOpenCover.mk
    apply top_unique
    intro point point_contains
    obtain ⟨selected_point, member, chart_contains⟩ := Set.mem_iUnion₂.mp
      (covers (Set.mem_univ point))
    exact Opens.mem_iSup.mpr ⟨⟨selected_point, member⟩, chart_contains⟩
  let section_maps := fun point : Index => ampleGlobalSectionHom
    (second + (period * multiple) • first).sheaf (sections point.val point.property)
  have local_iso : ∀ point : Index, IsIso ((section_maps point).over (finite_charts point)) :=
    fun point => moduleGlobalSectionHom_over_isIso_of_frame _ _ _ (frames point.val point.property)
  exact ⟨finiteFrameCoverGeneratingSections finite_charts finite_covers section_maps local_iso,
    inferInstance⟩

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance toricEvaluationCartierSheafInvertible
    {scheme : AlgebraicGeometry.Scheme.{0}} [IsIntegral scheme]
    (divisor : CartierDivisor scheme) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme divisor.sheaf :=
  CartierDivisor.isInvertible_sheaf divisor

def invariantCartierPowerIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (power : ℕ) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    (power • fan.invariantDivisorCartier 𝕜 complete regular divisor).sheaf ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular (power • divisor)).obj := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact eqToIso (congrArg CartierDivisor.sheaf
    ((fan.invariantDivisorCartierHom 𝕜 complete regular).map_nsmul power divisor).symm)

theorem invariantCartier_affinePositivePower_at_of_isAmple
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (ample : IsAmple (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj)
    (point : fan.algebraicRealization 𝕜 regular) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    ∃ (power : ℕ) (_ : 0 < power)
      (section_value : Γ((power • fan.invariantDivisorCartier 𝕜 complete regular divisor).sheaf, ⊤)),
      point ∈ (power • fan.invariantDivisorCartier 𝕜 complete regular divisor).sheaf.nonvanishingLocus
        section_value ∧
      IsAffineOpen ((power • fan.invariantDivisorCartier 𝕜 complete regular divisor).sheaf.nonvanishingLocus
        section_value) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  obtain ⟨power, positive, section_value, contains, affine⟩ :=
    fan.exists_positiveInvariantPower_affineNonvanishing 𝕜 complete regular divisor ample point
  let comparison := fan.invariantCartierPowerIso 𝕜 complete regular divisor power
  refine ⟨power, positive, Scheme.Modules.Hom.app comparison.inv ⊤ section_value, ?_, ?_⟩
  · exact (Scheme.Modules.mem_nonvanishingLocus_iso comparison.symm section_value point).mpr contains
  · exact (Scheme.Modules.nonvanishingLocus_iso comparison.symm section_value).symm ▸ affine

theorem negativeRayTwist_exists_eventual_multiple_generatingSections_of_isAmple
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (ray : fan.Ray)
    (ample : IsAmple (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj) :
    ∃ (period bound : ℕ) (_ : 0 < period) (_ : 0 < bound),
      ∀ multiple : ℕ, bound ≤ multiple →
        ∃ generators : (fan.invariantDivisorLineBundle 𝕜 complete regular
          (fan.negativeRayTwistDivisor divisor ray (period * multiple))).obj.GeneratingSections,
          generators.IsFiniteType := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let : CompactSpace (fan.algebraicRealization 𝕜 regular) := ample.1
  let first := fan.invariantDivisorCartier 𝕜 complete regular divisor
  let second := fan.invariantDivisorCartier 𝕜 complete regular (-Finsupp.single ray 1)
  obtain ⟨period, bound, positive_period, positive_bound, generators⟩ :=
    BondalThomsen.cartierAffinePowerCover_exists_eventual_multiple_generatingSections first second
      (fan.invariantCartier_affinePositivePower_at_of_isAmple 𝕜 complete regular divisor ample)
  refine ⟨period, bound, positive_period, positive_bound, fun multiple larger => ?_⟩
  obtain ⟨generated, finite⟩ := generators multiple larger
  let := finite
  let comparison := fan.actualNegativeRayTwistCartierIso 𝕜 complete regular divisor ray
    (period * multiple)
  exact ⟨generated.ofEpi comparison.hom, inferInstance⟩

theorem invariantDivisor_basisStrictSupport_of_isAmple
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor)
    (ample : IsAmple (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) :
    fan.BasisDivisorStrictSupport basis cone_basis divisor := by
  intro ray outside
  have weak := fan.divisor_hasRaySupportInequalities_of_isAmple 𝕜 complete regular divisor ample
    dimension basis cone_basis ray
  apply lt_of_le_of_ne weak
  intro equal
  obtain ⟨period, bound, positive_period, positive_bound, generators⟩ :=
    fan.negativeRayTwist_exists_eventual_multiple_generatingSections_of_isAmple 𝕜
      complete regular divisor ray ample
  obtain ⟨generated, finite⟩ := generators bound le_rfl
  exact fan.negativeRayTwist_not_globallyGenerated_of_supportEquality 𝕜 complete regular divisor
    basis cone_basis ray outside equal.symm (period * bound) ⟨generated⟩

end TauCeti.Toric.Fan
