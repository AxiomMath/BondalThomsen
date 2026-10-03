module

public import BondalThomsen.Toric.Positivity.AmpleNegativeTwistGeneration
public import BondalThomsen.LineBundle.AmpleLineBundleArbitraryAffinePullback

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

noncomputable section

namespace BondalThomsen

variable {scheme : AlgebraicGeometry.Scheme.{0}} [IsIntegral scheme]

local instance affineCartierSheafInvertible (divisor : CartierDivisor scheme) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme divisor.sheaf :=
  CartierDivisor.isInvertible_sheaf divisor

theorem cartierAffineOpen_sectionExtension
    (divisor : CartierDivisor scheme) (open_set : scheme.Opens)
    [Nonempty open_set] (affine : IsAffineOpen open_set) (coefficient : Γ(scheme, open_set))
    [Nonempty (scheme.basicOpen coefficient)]
    (local_section : Γ(divisor.sheaf, scheme.basicOpen coefficient)) :
    ∃ exponent : ℕ, ∃ extended_section : Γ(divisor.sheaf, open_set),
      divisor.sheaf.res (scheme.basicOpen_le coefficient) extended_section =
        (scheme.presheaf.map (homOfLE (scheme.basicOpen_le coefficient)).op coefficient) ^
          exponent • local_section := by
  classical
  let points : Type := {point : scheme // point ∈ open_set}
  have chart_exists : ∀ point : points,
      ∃ (chart : scheme.Opens) (contains : point.val ∈ chart),
        chart ≤ open_set ∧ IsAffineOpen chart ∧ ∃ equation : scheme.functionFieldˣ,
          letI : Nonempty chart := ⟨⟨point.val, contains⟩⟩
          rationalUnitClass scheme chart (Additive.ofMul equation) = divisor |_ chart := by
    intro point
    obtain ⟨equation_open, equation_contained, equation_contains, equation, equation_equal⟩ :=
      divisor.exists_localEquation_le open_set point.property
    obtain ⟨chart, chart_affine, contains, chart_contained⟩ :=
      exists_isAffineOpen_mem_and_subset equation_contains
    have : Nonempty equation_open := ⟨⟨point.val, equation_contains⟩⟩
    have : Nonempty chart := ⟨⟨point.val, contains⟩⟩
    exact ⟨chart, contains, chart_contained.trans equation_contained, chart_affine, equation,
      CartierDivisor.rationalUnitClass_eq_of_le chart_contained equation_equal⟩
  choose charts contains chart_contained chart_affine equations equation_equal using chart_exists
  let (point : points) : Nonempty (charts point) := ⟨⟨point.val, contains point⟩⟩
  let coefficients : ∀ point : points, Γ(scheme, charts point) := fun point =>
    scheme.presheaf.map (homOfLE (chart_contained point)).op coefficient
  have basic_contained : ∀ point : points,
      scheme.basicOpen (coefficients point) ≤ scheme.basicOpen coefficient := by
    intro point
    rw [scheme.basicOpen_res]
    exact inf_le_right
  let (point : points) : Nonempty (scheme.basicOpen (coefficients point)) := by
    refine ⟨⟨genericPoint scheme, ?_⟩⟩
    change genericPoint scheme ∈ scheme.basicOpen
      (scheme.presheaf.map (homOfLE (chart_contained point)).op coefficient)
    rw [scheme.basicOpen_res]
    exact ⟨genericPoint_mem (charts point), genericPoint_mem (scheme.basicOpen coefficient)⟩
  have local_lifts : ∀ point : points, ∃ exponent : ℕ, ∃ lifted : Γ(scheme, charts point),
      scheme.germToFunctionField (charts point) lifted =
        (equations point : scheme.functionField) *
          (scheme.germToFunctionField open_set coefficient ^ exponent *
            cartierSectionValue divisor (scheme.basicOpen coefficient) local_section) := by
    intro point
    obtain ⟨local_coefficient, local_equal⟩ :=
      (CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq
        (scheme.basicOpen_le (coefficients point)) (equation_equal point)).mp
          (divisor.sheafι_app_mem _ (divisor.sheaf.res (basic_contained point) local_section))
    obtain ⟨exponent, lifted, equal⟩ := exists_eq_pow_mul_of_isAffineOpen scheme
      (charts point) (chart_affine point) (coefficients point) local_coefficient
    have values := congrArg (scheme.germToFunctionField (scheme.basicOpen (coefficients point))) equal
    change scheme.germToFunctionField (scheme.basicOpen (coefficients point))
      (scheme.presheaf.map (homOfLE (scheme.basicOpen_le (coefficients point))).op lifted) =
      scheme.germToFunctionField (scheme.basicOpen (coefficients point))
        ((scheme.presheaf.map (homOfLE (scheme.basicOpen_le (coefficients point))).op
          (coefficients point)) ^ exponent * local_coefficient) at values
    rw [cartierGermToFunctionField_res, map_mul, map_pow,
      cartierGermToFunctionField_res, local_equal] at values
    change scheme.germToFunctionField (charts point) lifted =
      scheme.germToFunctionField (charts point) (coefficients point) ^ exponent *
        (equations point * cartierSectionValue divisor (scheme.basicOpen (coefficients point))
          (divisor.sheaf.res (basic_contained point) local_section)) at values
    rw [cartierSectionValue_res, cartierGermToFunctionField_res] at values
    exact ⟨exponent, lifted, by rw [values]; ring⟩
  choose exponents lifted lifted_equal using local_lifts
  have compact_points : CompactSpace points := isCompact_iff_compactSpace.mp affine.isCompact
  let := compact_points
  obtain ⟨finite_cover, subset, covers⟩ := isCompact_univ.elim_nhds_subcover
    (fun point : points => {other : points | other.val ∈ charts point})
    (fun point _ => ((charts point).isOpen.preimage continuous_subtype_val).mem_nhds
      (contains point))
  let exponent := finite_cover.sup exponents
  let rational_value := scheme.germToFunctionField open_set coefficient ^ exponent *
    cartierSectionValue divisor (scheme.basicOpen coefficient) local_section
  let rational_section := (rationalFunctionsEquiv open_set).symm rational_value
  have membership : rational_section ∈ divisor.sections open_set := by
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro point point_contains
    obtain ⟨chart_point, chart_mem, chart_contains⟩ :=
      Set.mem_iUnion₂.mp (covers (Set.mem_univ (⟨point, point_contains⟩ : points)))
    let local_coefficient := coefficients chart_point ^ (exponent - exponents chart_point) *
      lifted chart_point
    have regular_value : scheme.germToFunctionField (charts chart_point) local_coefficient =
        equations chart_point * rational_value := by
      dsimp only [local_coefficient, coefficients]
      rw [map_mul, map_pow, cartierGermToFunctionField_res, lifted_equal]
      dsimp only [rational_value]
      have powers : scheme.germToFunctionField open_set coefficient ^
          (exponent - exponents chart_point) *
            scheme.germToFunctionField open_set coefficient ^ exponents chart_point =
          scheme.germToFunctionField open_set coefficient ^ exponent := by
        rw [← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := exponents) chart_mem)]
      calc
        _ = (equations chart_point : scheme.functionField) *
          (scheme.germToFunctionField open_set coefficient ^ (exponent - exponents chart_point) *
            scheme.germToFunctionField open_set coefficient ^ exponents chart_point) *
              cartierSectionValue divisor (scheme.basicOpen coefficient) local_section := by ring
        _ = _ := by rw [powers, mul_assoc]
    have equation_local := CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
      (equation_equal chart_point) chart_contains
    refine ⟨equations chart_point, equation_local, ?_⟩
    rw [show rationalFunctionsEquiv open_set rational_section = rational_value from
      (rationalFunctionsEquiv open_set).apply_symm_apply _]
    rw [← regular_value,
      ← AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField scheme chart_contains]
    exact RingHom.mem_range_self _ _
  refine ⟨exponent, CartierDivisor.sectionMk rational_section membership,
    (cartierSectionValue_injective divisor (scheme.basicOpen coefficient)) ?_⟩
  rw [cartierSectionValue_res, cartierSectionValue_smul, map_pow, cartierGermToFunctionField_res]
  exact (rationalFunctionsEquiv open_set).apply_symm_apply rational_value

omit [IsIntegral scheme] in
theorem negativeTwistFrame_smul_unit (sheaf : scheme.Modules) (open_set : scheme.Opens)
    (section_value : Γ(sheaf, open_set)) (frame : Scheme.Modules.IsFrame sheaf open_set section_value)
    (scalar : Γ(scheme, open_set)) (unit : IsUnit scalar) :
    Scheme.Modules.IsFrame sheaf open_set (scalar • section_value) := by
  intro smaller contained
  have scalar_unit := unit.map (scheme.presheaf.map (homOfLE contained).op).hom
  obtain ⟨invertible_scalar, scalar_equal⟩ := scalar_unit
  have representation : (fun coefficient : Γ(scheme, smaller) =>
      coefficient • sheaf.res contained (scalar • section_value)) =
        (fun coefficient : Γ(scheme, smaller) => coefficient • sheaf.res contained section_value) ∘
          (fun coefficient : Γ(scheme, smaller) => coefficient * invertible_scalar) := by
    funext coefficient
    change coefficient • (sheaf.presheaf.map (homOfLE contained).op (scalar • section_value)) = _
    rw [Scheme.Modules.map_smul, ← scalar_equal]
    change coefficient • (↑invertible_scalar • sheaf.res contained section_value) =
      (coefficient * ↑invertible_scalar) • sheaf.res contained section_value
    exact (mul_smul coefficient (↑invertible_scalar) _).symm
  rw [representation]
  exact (frame smaller contained).comp (Units.mulRight_bijective invertible_scalar)

theorem cartierAffineOpen_exists_section_frame_at
    (divisor : CartierDivisor scheme) (open_set : scheme.Opens)
    (affine : IsAffineOpen open_set) (point : scheme) (point_contains : point ∈ open_set) :
    ∃ (section_value : Γ(divisor.sheaf, open_set)) (neighborhood : scheme.Opens)
      (contained : neighborhood ≤ open_set),
      point ∈ neighborhood ∧
        Scheme.Modules.IsFrame divisor.sheaf neighborhood (divisor.sheaf.res contained section_value) := by
  have : Nonempty open_set := ⟨⟨point, point_contains⟩⟩
  obtain ⟨equation_open, equation_contained, equation_contains, equation, equation_equal⟩ :=
    divisor.exists_localEquation_le open_set point_contains
  have : Nonempty equation_open := ⟨⟨point, equation_contains⟩⟩
  obtain ⟨coefficient, basic_contained, basic_contains⟩ :=
    affine.exists_basicOpen_le (⟨point, equation_contains⟩ : equation_open) point_contains
  have : Nonempty (scheme.basicOpen coefficient) := ⟨⟨point, basic_contains⟩⟩
  let frame_section := divisor.sheaf.res basic_contained
    (cartierEquationGenerator divisor equation_open equation equation_equal)
  have frame := (cartierEquationGenerator_isFrame divisor equation_open equation equation_equal).restrict
    basic_contained
  obtain ⟨exponent, section_value, equal⟩ := cartierAffineOpen_sectionExtension divisor open_set
    affine coefficient frame_section
  refine ⟨section_value, scheme.basicOpen coefficient, scheme.basicOpen_le coefficient,
    basic_contains, ?_⟩
  rw [equal]
  exact negativeTwistFrame_smul_unit divisor.sheaf (scheme.basicOpen coefficient) frame_section
    frame _ ((scheme.toRingedSpace.isUnit_res_basicOpen coefficient).pow exponent)

end BondalThomsen
