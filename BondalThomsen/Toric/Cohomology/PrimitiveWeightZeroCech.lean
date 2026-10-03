module

public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Fan.PrimitiveCollectionBoundary
public import BondalThomsen.Cohomology.FiniteAffineCechHigherComparison
public import BondalThomsen.Toric.Scheme.Separated
public import BondalThomsen.Toric.Scheme.Noetherian

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti.Toric Multiplicative
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def primitiveCechChartOpen (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (index : Fin (Nat.card fan.cones)) : (fan.algebraicRealization 𝕜 regular).Opens :=
  (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index)).opensRange

noncomputable def primitiveCechCone (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    (degree : ℕ) → (Fin (degree + 1) → Fin (Nat.card fan.cones)) → fan.cones
  | 0, tuple => fan.divisorLocalCone 𝕜 complete regular (tuple 0)
  | degree + 1, tuple => fan.divisorLocalCone 𝕜 complete regular (tuple 0) ⊓
      fan.primitiveCechCone complete regular degree (tuple ∘ Fin.succ)

theorem primitiveCechCone_le_chart (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) (index : Fin (degree + 1)) :
    fan.primitiveCechCone 𝕜 complete regular degree tuple ≤
      fan.divisorLocalCone 𝕜 complete regular (tuple index) := by
  induction degree with
  | zero =>
    have index_zero : index = 0 := by omega
    subst index
    exact le_rfl
  | succ degree induction =>
    refine Fin.cases ?_ (fun smaller => ?_) index
    · exact inf_le_left
    · exact inf_le_right.trans (induction (tuple ∘ Fin.succ) smaller)

theorem primitiveCechCone_opensRange (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    (fan.affineToricChartι 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular degree tuple)).opensRange =
      ⨅ index, fan.primitiveCechChartOpen 𝕜 complete regular (tuple index) := by
  induction degree with
  | zero =>
    apply le_antisymm
    · refine le_iInf fun index => ?_
      have index_zero : index = 0 := by omega
      subst index
      exact le_rfl
    · exact iInf_le _ 0
  | succ degree induction =>
    rw [primitiveCechCone, fan.chart_opensRange_intersection 𝕜, induction]
    apply le_antisymm
    · refine le_iInf fun index => ?_
      refine Fin.cases ?_ (fun smaller => ?_) index
      · exact inf_le_left
      · exact inf_le_right.trans (iInf_le _ smaller)
    · exact le_inf (iInf_le _ 0) (le_iInf fun smaller => iInf_le _ smaller.succ)

theorem primitiveCechIntersection_eq_chart (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection
      (fan.primitiveCechChartOpen 𝕜 complete regular) degree tuple =
      (fan.affineToricChartι 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular degree tuple)).opensRange := by
  rw [BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection,
    BondalThomsen.FiniteAffineCechHigherComparison.productOpens_eq_iInf,
    fan.primitiveCechCone_opensRange 𝕜]
  rfl

theorem primitiveCechChartOpen_covers (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    IsOpenCover (fan.primitiveCechChartOpen 𝕜 complete regular) :=
  (fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).covers

omit [FiniteDimensional ℝ Ambient] in
theorem translatedCharacter_mem_dualSemigroup_iff_rays (fan : Fan embedding)
    (cone : fan.cones) (divisor : fan.InvariantRayDivisor)
    (chartCharacter character : Lattice →+ ℤ)
    (presentation : ∀ ray : fan.Ray, embedding ray.val ∈ cone.val →
      chartCharacter ray.val = -divisor ray) :
    character - chartCharacter ∈ dualSemigroup fan.lattice cone.val ↔
      ∀ ray : fan.Ray, embedding ray.val ∈ cone.val → -divisor ray ≤ character ray.val := by
  constructor
  · intro member ray contains
    have evaluation := (mem_dualSemigroup fan.lattice (character - chartCharacter)).mp member contains
    rw [fan.lattice.realCharacter_apply, AddMonoidHom.sub_apply, presentation ray contains] at evaluation
    have integerBound : (0 : ℤ) ≤ character ray.val - -divisor ray := by
      exact_mod_cast evaluation
    exact sub_nonneg.mp integerBound
  · intro inequalities
    let toric := fan.isToricCone cone.property
    apply (mem_dualSemigroup_iff_primitiveGenerator fan.lattice toric _).mpr
    intro coneRay
    let actual : fan.Ray := ⟨primitiveGenerator fan.lattice toric coneRay,
      primitiveGenerator_isPrimitive fan.lattice toric coneRay, by
        have singleton := coneRay.eq_hull_singleton (toric.salient.anti coneRay.1.isFaceOf.le)
          (primitiveGenerator_mem fan.lattice toric coneRay)
          (by simpa only [map_zero] using
            (fan.lattice.injective.ne (primitiveGenerator_ne_zero fan.lattice toric coneRay)))
        rw [← singleton]
        exact fan.mem_of_isFaceOf cone.property coneRay.1.isFaceOf⟩
    have contains : embedding actual.val ∈ cone.val :=
      coneRay.1.isFaceOf.le (primitiveGenerator_mem fan.lattice toric coneRay)
    change 0 ≤ character actual.val - chartCharacter actual.val
    rw [presentation actual contains]
    exact sub_nonneg.mpr (inequalities actual contains)

theorem primitiveCechCone_character_presents (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (ray : fan.Ray) (contains : embedding ray.val ∈
      (fan.primitiveCechCone 𝕜 complete regular degree tuple).val) :
    fan.divisorLocalCharacter 𝕜 complete regular divisor (tuple 0) ray.val = -divisor ray := by
  apply fan.coneDivisorCharacter_ray
  exact (fan.primitiveCechCone_le_chart 𝕜 complete regular degree tuple 0) contains

theorem primitiveCechCone_localEquation (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let cone := fan.primitiveCechCone 𝕜 complete regular degree tuple
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    (fan.invariantDivisorCartier 𝕜 complete regular divisor) |_
        (fan.affineToricChartι 𝕜 regular cone).opensRange =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
        (fan.affineToricChartι 𝕜 regular cone).opensRange
        (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular (fan.completeFan_nonemptyCones complete)
          (-fan.divisorLocalCharacter 𝕜 complete regular divisor (tuple 0)))) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let cone := fan.primitiveCechCone 𝕜 complete regular degree tuple
  let := fan.chartOpen_nonempty 𝕜 regular cone
  let := fan.chartOpen_nonempty 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular (tuple 0))
  have containment : (fan.affineToricChartι 𝕜 regular cone).opensRange ≤
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular (tuple 0))).opensRange := by
    rw [fan.primitiveCechCone_opensRange 𝕜]
    exact iInf_le _ 0
  have equation := congrArg
    (fun localSection => localSection |_ (fan.affineToricChartι 𝕜 regular cone).opensRange)
    (fan.invariantDivisorCartier_localEquation 𝕜 complete regular divisor (tuple 0))
  rw [TopCat.Presheaf.restrict_restrict containment le_top,
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_restrict
      (fan.algebraicRealization 𝕜 regular) containment] at equation
  exact equation

theorem primitiveCechCone_laurentSections_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    let cone := fan.primitiveCechCone 𝕜 complete regular degree tuple
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    (fan.laurentRationalSection 𝕜) regular (fan.completeFan_nonemptyCones complete)
        (fan.affineToricChartι 𝕜 regular cone).opensRange polynomial ∈
      (fan.invariantDivisorCartier 𝕜 complete regular divisor).sections
        (fan.affineToricChartι 𝕜 regular cone).opensRange ↔
      polynomial ∈ fan.divisorLaurentSectionSpace 𝕜 cone.val divisor := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let cone := fan.primitiveCechCone 𝕜 complete regular degree tuple
  let := fan.chartOpen_nonempty 𝕜 regular cone
  change fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete)
      (fan.affineToricChartι 𝕜 regular cone).opensRange polynomial ∈
    (fan.invariantDivisorCartier 𝕜 complete regular divisor).sections
      (fan.affineToricChartι 𝕜 regular cone).opensRange ↔
    polynomial ∈ fan.divisorLaurentSectionSpace 𝕜 cone.val divisor
  rw [fan.laurentRationalSection_mem_cartierSections_iff 𝕜 regular
    (fan.completeFan_nonemptyCones complete) cone
    (fan.divisorLocalCharacter 𝕜 complete regular divisor (tuple 0)) _
    (fan.primitiveCechCone_localEquation 𝕜 complete regular divisor degree tuple),
    fan.mem_range_coneCharacterSectionMap_iff 𝕜, fan.mem_divisorLaurentSectionSpace_iff 𝕜]
  apply forall_congr'
  intro exponent
  apply forall_congr'
  intro _contains
  exact fan.translatedCharacter_mem_dualSemigroup_iff_rays cone divisor _ _
    (fan.primitiveCechCone_character_presents 𝕜 complete regular divisor degree tuple)

omit [FiniteDimensional ℝ Ambient] in
theorem laurentRationalSection_restrict_between (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    (larger smaller : (fan.algebraicRealization 𝕜 regular).Opens)
    [Nonempty larger] [Nonempty smaller] (containment : smaller ≤ larger)
    (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions (fan.algebraicRealization 𝕜 regular)).presheaf.map
        (homOfLE containment).op (fan.laurentRationalSection 𝕜 regular nonempty larger polynomial) =
      fan.laurentRationalSection 𝕜 regular nonempty smaller polynomial := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv smaller).injective
  rw [TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map,
    fan.rationalFunctionsEquiv_laurentRationalSection 𝕜,
    fan.rationalFunctionsEquiv_laurentRationalSection 𝕜]

noncomputable def primitiveCechLaurentToSheafSections (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.divisorLaurentSectionSpace 𝕜 (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor →+
      Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
        (fan.affineToricChartι 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular degree tuple)).opensRange) := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let cone := fan.primitiveCechCone 𝕜 complete regular degree tuple
  letI := fan.chartOpen_nonempty 𝕜 regular cone
  exact {
    toFun := fun polynomial => TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sectionMk
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete)
        (fan.affineToricChartι 𝕜 regular cone).opensRange polynomial.val)
      ((fan.primitiveCechCone_laurentSections_iff 𝕜 complete regular divisor degree tuple polynomial.val).mpr
        polynomial.property)
    map_zero' := by apply Subtype.ext; exact map_zero _
    map_add' := fun first second => by apply Subtype.ext; exact map_add _ _ _ }

theorem primitiveCechLaurentToSheafSections_injective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    Function.Injective (fan.primitiveCechLaurentToSheafSections 𝕜 complete regular divisor degree tuple) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let cone := fan.primitiveCechCone 𝕜 complete regular degree tuple
  let chart := (fan.affineToricChartι 𝕜 regular cone).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular cone
  intro first second same
  apply Subtype.ext
  apply fan.laurentRationalMap_injective 𝕜 regular (fan.completeFan_nonemptyCones complete)
  have rational_same := congrArg (fun section_value =>
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
      (Scheme.Modules.Hom.app (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι chart
        section_value)) same
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) chart first.val) =
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) chart second.val)
    at rational_same
  simpa only [rationalFunctionsEquiv_laurentRationalSection] using rational_same

theorem primitiveCechLaurentToSheafSections_surjective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    Function.Surjective (fan.primitiveCechLaurentToSheafSections 𝕜 complete regular divisor degree tuple) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let cone := fan.primitiveCechCone 𝕜 complete regular degree tuple
  let chart := (fan.affineToricChartι 𝕜 regular cone).opensRange
  let := fan.chartOpen_nonempty 𝕜 regular cone
  let character := fan.divisorLocalCharacter 𝕜 complete regular divisor (tuple 0)
  intro section_value
  have member := (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_mem chart section_value
  obtain ⟨regular_coefficient, coefficient_equation⟩ :=
    (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq
      le_rfl (fan.primitiveCechCone_localEquation 𝕜 complete regular divisor degree tuple).symm).mp member
  let coefficient := (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).symm regular_coefficient
  let polynomial := fan.coneCharacterSectionMap 𝕜 cone.val character coefficient
  have polynomial_member : polynomial ∈ fan.divisorLaurentSectionSpace 𝕜 cone.val divisor := by
    apply (fan.primitiveCechCone_laurentSections_iff 𝕜 complete regular divisor degree tuple polynomial).mp
    exact (fan.laurentRationalSection_mem_cartierSections_iff 𝕜 regular
      (fan.completeFan_nonemptyCones complete) cone character _
      (fan.primitiveCechCone_localEquation 𝕜 complete regular divisor degree tuple) polynomial).mpr
      ⟨coefficient, rfl⟩
  refine ⟨⟨polynomial, polynomial_member⟩, ?_⟩
  apply (fan.invariantDivisorCartier 𝕜 complete regular divisor).sheafι_app_injective chart
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart).injective
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv chart
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete) chart polynomial) = _
  rw [fan.rationalFunctionsEquiv_laurentRationalSection 𝕜,
    fan.laurentRationalMap_coneCharacterSectionMap 𝕜 regular _ cone]
  have coefficient_germ : fan.chartCoordinateGerm 𝕜 regular (fan.completeFan_nonemptyCones complete)
      cone coefficient = (fan.algebraicRealization 𝕜 regular).germToFunctionField chart regular_coefficient :=
    (fan.chartCoordinateGerm_sections 𝕜 regular _ cone coefficient).trans
      (congrArg ((fan.algebraicRealization 𝕜 regular).germToFunctionField chart)
        ((fan.chartCoordinateSectionsEquiv 𝕜 regular cone).apply_symm_apply regular_coefficient))
  rw [coefficient_germ, coefficient_equation, rationalCharacterUnit_neg]
  simp only [Units.val_inv_eq_inv_val]
  rw [mul_right_comm, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

noncomputable def primitiveCechSheafSectionsEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.divisorLaurentSectionSpace 𝕜 (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor ≃+
      Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
        (fan.affineToricChartι 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular degree tuple)).opensRange) :=
  AddEquiv.ofBijective (fan.primitiveCechLaurentToSheafSections 𝕜 complete regular divisor degree tuple)
    ⟨fan.primitiveCechLaurentToSheafSections_injective 𝕜 complete regular divisor degree tuple,
      fan.primitiveCechLaurentToSheafSections_surjective 𝕜 complete regular divisor degree tuple⟩

omit [FiniteDimensional ℝ Ambient] in
theorem divisorLaurentSectionSpace_antitone (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) {larger smaller : PointedCone ℝ Ambient}
    (containment : smaller ≤ larger) :
    fan.divisorLaurentSectionSpace 𝕜 larger divisor ≤ fan.divisorLaurentSectionSpace 𝕜 smaller divisor := by
  intro polynomial member
  rw [fan.mem_divisorLaurentSectionSpace_iff 𝕜] at member ⊢
  exact fun exponent supported ray contains => member exponent supported ray (containment contains)

theorem primitiveCechLaurentToSheafSections_restrict (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (largerDegree smallerDegree : ℕ)
    (largerTuple : Fin (largerDegree + 1) → Fin (Nat.card fan.cones))
    (smallerTuple : Fin (smallerDegree + 1) → Fin (Nat.card fan.cones))
    (containment : fan.primitiveCechCone 𝕜 complete regular smallerDegree smallerTuple ≤
      fan.primitiveCechCone 𝕜 complete regular largerDegree largerTuple)
    (openContainment :
      (fan.affineToricChartι 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular smallerDegree smallerTuple)).opensRange ≤
      (fan.affineToricChartι 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular largerDegree largerTuple)).opensRange)
    (polynomial : fan.divisorLaurentSectionSpace 𝕜
      (fan.primitiveCechCone 𝕜 complete regular largerDegree largerTuple).val divisor) :
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.map (homOfLE openContainment).op
        (fan.primitiveCechLaurentToSheafSections 𝕜 complete regular divisor largerDegree largerTuple polynomial) =
      fan.primitiveCechLaurentToSheafSections 𝕜 complete regular divisor smallerDegree smallerTuple
        ⟨polynomial.val, fan.divisorLaurentSectionSpace_antitone 𝕜 divisor containment polynomial.property⟩ := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let := fan.chartOpen_nonempty 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular largerDegree largerTuple)
  let := fan.chartOpen_nonempty 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular smallerDegree smallerTuple)
  apply Subtype.ext
  change (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions (fan.algebraicRealization 𝕜 regular)).presheaf.map
      (homOfLE openContainment).op
      (fan.laurentRationalSection 𝕜 regular (fan.completeFan_nonemptyCones complete)
        (fan.affineToricChartι 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular largerDegree largerTuple)).opensRange
        polynomial.val) = _
  exact fan.laurentRationalSection_restrict_between 𝕜 regular (fan.completeFan_nonemptyCones complete)
    _ _ openContainment polynomial.val

omit [FiniteDimensional ℝ Ambient] in
theorem primitiveCechCone_opensRange_mono (fan : Fan embedding)
    (regular : fan.IsRegular) {smaller larger : fan.cones} (containment : smaller ≤ larger) :
    (fan.affineToricChartι 𝕜 regular smaller).opensRange ≤
      (fan.affineToricChartι 𝕜 regular larger).opensRange := by
  have intersection := fan.chart_opensRange_intersection 𝕜 regular smaller larger
  rw [inf_eq_left.mpr containment] at intersection
  exact intersection.le.trans inf_le_right

noncomputable def divisorLaurentWeightZeroProjection (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (divisor : fan.InvariantRayDivisor) :
    fan.divisorLaurentSectionSpace 𝕜 cone divisor →ₗ[𝕜]
      (fan.divisorLaurentSectionSpace 𝕜) cone divisor := by
  classical
  refine {
    toFun := fun polynomial => ⟨MonoidAlgebra.single (ofAdd 0) (polynomial.val.coeff (ofAdd 0)), ?_⟩
    map_add' := fun first second => ?_
    map_smul' := fun scalar polynomial => ?_ }
  · rw [fan.mem_divisorLaurentSectionSpace_iff 𝕜]
    intro exponent supported ray contains
    have exponent_zero : exponent = ofAdd 0 := Finset.mem_singleton.mp
      (Finsupp.support_single_subset supported)
    have nonzero : polynomial.val.coeff (ofAdd 0) ≠ 0 := by
      intro coefficient_zero
      change exponent ∈ (Finsupp.single (ofAdd 0) (polynomial.val.coeff (ofAdd 0))).support at supported
      rw [coefficient_zero] at supported
      simp at supported
    subst exponent
    exact (fan.mem_divisorLaurentSectionSpace_iff 𝕜 cone divisor polynomial.val).mp polynomial.property
      (ofAdd 0) (Finsupp.mem_support_iff.mpr nonzero) ray contains
  · apply Subtype.ext
    simp only [Submodule.coe_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.single_add]
  · apply Subtype.ext
    simp only [Submodule.coe_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      MonoidAlgebra.smul_single, RingHom.id_apply]

noncomputable def primitiveCechWeightZeroProjection (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
      (fan.affineToricChartι 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular degree tuple)).opensRange) →+
    Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
      (fan.affineToricChartι 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular degree tuple)).opensRange) :=
  (fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree tuple).toAddMonoidHom.comp
    ((fan.divisorLaurentWeightZeroProjection 𝕜
      (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor).toAddMonoidHom.comp
        (fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree tuple).symm.toAddMonoidHom)

theorem primitiveCechWeightZeroProjection_apply_laurent (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (polynomial : fan.divisorLaurentSectionSpace 𝕜
      (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor) :
    fan.primitiveCechWeightZeroProjection 𝕜 complete regular divisor degree tuple
        (fan.primitiveCechLaurentToSheafSections 𝕜 complete regular divisor degree tuple polynomial) =
      fan.primitiveCechLaurentToSheafSections 𝕜 complete regular divisor degree tuple
        (fan.divisorLaurentWeightZeroProjection 𝕜
          (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor polynomial) := by
  change (fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree tuple)
      (fan.divisorLaurentWeightZeroProjection 𝕜 _ divisor
        ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree tuple).symm
          ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree tuple) polynomial))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

theorem primitiveCechWeightZeroProjection_restrict (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (largerDegree smallerDegree : ℕ)
    (largerTuple : Fin (largerDegree + 1) → Fin (Nat.card fan.cones))
    (smallerTuple : Fin (smallerDegree + 1) → Fin (Nat.card fan.cones))
    (containment : fan.primitiveCechCone 𝕜 complete regular smallerDegree smallerTuple ≤
      fan.primitiveCechCone 𝕜 complete regular largerDegree largerTuple)
    (section_value : Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
      (fan.affineToricChartι 𝕜 regular (fan.primitiveCechCone 𝕜 complete regular largerDegree largerTuple)).opensRange)) :
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.map
        (homOfLE (fan.primitiveCechCone_opensRange_mono 𝕜 regular containment)).op
        (fan.primitiveCechWeightZeroProjection 𝕜 complete regular divisor largerDegree largerTuple section_value) =
      fan.primitiveCechWeightZeroProjection 𝕜 complete regular divisor smallerDegree smallerTuple
        ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.map
          (homOfLE (fan.primitiveCechCone_opensRange_mono 𝕜 regular containment)).op section_value) := by
  obtain ⟨polynomial, rfl⟩ := fan.primitiveCechLaurentToSheafSections_surjective 𝕜
    complete regular divisor largerDegree largerTuple section_value
  rw [fan.primitiveCechWeightZeroProjection_apply_laurent 𝕜,
    fan.primitiveCechLaurentToSheafSections_restrict 𝕜 complete regular divisor
      largerDegree smallerDegree largerTuple smallerTuple containment,
    fan.primitiveCechLaurentToSheafSections_restrict 𝕜 complete regular divisor
      largerDegree smallerDegree largerTuple smallerTuple containment,
    fan.primitiveCechWeightZeroProjection_apply_laurent 𝕜]
  rfl

theorem le_primitiveCechCone_iff (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (cone : fan.cones)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    cone ≤ fan.primitiveCechCone 𝕜 complete regular degree tuple ↔
      ∀ index, cone ≤ fan.divisorLocalCone 𝕜 complete regular (tuple index) := by
  constructor
  · exact fun containment index => containment.trans
      (fan.primitiveCechCone_le_chart 𝕜 complete regular degree tuple index)
  · intro containments
    induction degree with
    | zero => exact containments 0
    | succ degree induction =>
      exact le_inf (containments 0)
        (induction (tuple ∘ Fin.succ) (fun index => containments index.succ))

theorem primitiveCechCone_le_face (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (degree : ℕ)
    (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones)) (deleted : Fin (degree + 2)) :
    fan.primitiveCechCone 𝕜 complete regular (degree + 1) tuple ≤
      fan.primitiveCechCone 𝕜 complete regular degree (tuple ∘ deleted.succAbove) := by
  apply (fan.le_primitiveCechCone_iff 𝕜 complete regular _ degree _).mpr
  exact fun index => fan.primitiveCechCone_le_chart 𝕜 complete regular (degree + 1) tuple
    (deleted.succAbove index)

theorem primitiveCechWeightZeroProjection_face (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones))
    (deleted : Fin (degree + 2))
    (section_value : Γ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj,
      (fan.affineToricChartι 𝕜 regular
        (fan.primitiveCechCone 𝕜 complete regular degree (tuple ∘ deleted.succAbove))).opensRange)) :
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.map
        (homOfLE (fan.primitiveCechCone_opensRange_mono 𝕜 regular
          (fan.primitiveCechCone_le_face 𝕜 complete regular degree tuple deleted))).op
        (fan.primitiveCechWeightZeroProjection 𝕜 complete regular divisor degree
          (tuple ∘ deleted.succAbove) section_value) =
      fan.primitiveCechWeightZeroProjection 𝕜 complete regular divisor (degree + 1) tuple
        ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.map
          (homOfLE (fan.primitiveCechCone_opensRange_mono 𝕜 regular
            (fan.primitiveCechCone_le_face 𝕜 complete regular degree tuple deleted))).op section_value) :=
  fan.primitiveCechWeightZeroProjection_restrict 𝕜 complete regular divisor degree (degree + 1)
    (tuple ∘ deleted.succAbove) tuple
    (fan.primitiveCechCone_le_face 𝕜 complete regular degree tuple deleted) section_value

end TauCeti.Toric.Fan
