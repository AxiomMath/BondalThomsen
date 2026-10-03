module

public import BondalThomsen.Toric.Scheme.DeepProperness
public import Mathlib.RingTheory.HahnSeries.HahnEmbedding

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

theorem finite_nonnegative_perturbation {Index : Type*} (indices : Finset Index)
    (first second : Index → ℝ)
    (nonnegative : ∀ index ∈ indices, 0 ≤ first index)
    (positive_on_zero : ∀ index ∈ indices, first index = 0 → 0 < second index) :
    ∃ multiplier : ℝ, 0 < multiplier ∧
      ∀ index ∈ indices, 0 < multiplier * first index + second index := by
  classical
  induction indices using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert index indices absent induction =>
    obtain ⟨multiplier, multiplier_positive, bounds⟩ := induction
      (fun other member => nonnegative other (Finset.mem_insert_of_mem member))
      (fun other member => positive_on_zero other (Finset.mem_insert_of_mem member))
    by_cases first_zero : first index = 0
    · refine ⟨multiplier, multiplier_positive, ?_⟩
      intro other member
      rcases Finset.mem_insert.mp member with rfl | member
      · simpa [first_zero] using positive_on_zero other (Finset.mem_insert_self _ _) first_zero
      · exact bounds other member
    · have first_positive : 0 < first index :=
        lt_of_le_of_ne (nonnegative index (Finset.mem_insert_self _ _)) (Ne.symm first_zero)
      let larger := max multiplier ((|second index| + 1) / first index)
      have multiplier_le : multiplier ≤ larger := le_max_left _ _
      have current_bound : |second index| + 1 ≤ larger * first index :=
        (div_le_iff₀ first_positive).mp (le_max_right _ _)
      refine ⟨larger, lt_of_lt_of_le multiplier_positive multiplier_le, ?_⟩
      intro other member
      rcases Finset.mem_insert.mp member with rfl | member
      · have absolute_bound := neg_abs_le (second other)
        linarith
      · have comparison := mul_le_mul_of_nonneg_right multiplier_le
          (nonnegative other (Finset.mem_insert_of_mem member))
        linarith [bounds other member]

theorem hahnSeries_finite_positive_functional {Group Index : Type*}
    [AddCommGroup Group] [LinearOrder Index] [Zero Index]
    (series : Group →+ HahnSeries Index ℝ) (elements : Finset Group)
    (positive : ∀ element ∈ elements, 0 < toLex (series element)) :
    ∃ functional : Group →+ ℝ, ∀ element ∈ elements, 0 < functional element := by
  classical
  induction elements using Finset.strongInductionOn
  next elements induction =>
    by_cases nonempty : elements.Nonempty
    · obtain ⟨first, first_member, minimal⟩ := elements.exists_min_image
        (fun element => (series element).order) nonempty
      let index := (series first).order
      let coefficient := (HahnSeries.coeff.addMonoidHom index).comp series
      have coefficient_nonnegative : ∀ element ∈ elements, 0 ≤ coefficient element := by
        intro element member
        have order_le : index ≤ (series element).order := minimal element member
        rcases eq_or_lt_of_le order_le with equal | strict
        · have leading_positive : 0 < (series element).leadingCoeff :=
            HahnSeries.leadingCoeff_pos_iff.mpr (positive element member)
          change 0 ≤ (series element).coeff index
          rw [equal, ← HahnSeries.leadingCoeff_eq]
          exact leading_positive.le
        · change 0 ≤ (series element).coeff index
          rw [HahnSeries.coeff_eq_zero_of_lt_order strict]
      have first_positive : 0 < coefficient first := by
        change 0 < (series first).coeff (series first).order
        rw [← HahnSeries.leadingCoeff_eq]
        exact HahnSeries.leadingCoeff_pos_iff.mpr (positive first first_member)
      let remaining := elements.filter (fun element => coefficient element = 0)
      have smaller : remaining ⊂ elements := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro equal
        have member : first ∈ remaining := equal.symm ▸ first_member
        exact ne_of_gt first_positive (Finset.mem_filter.mp member).2
      obtain ⟨functional, functional_positive⟩ := induction remaining smaller
        (fun element member => positive element (Finset.mem_filter.mp member).1)
      obtain ⟨multiplier, _, bounds⟩ := finite_nonnegative_perturbation elements
        coefficient functional coefficient_nonnegative
        (fun element member zero => functional_positive element (Finset.mem_filter.mpr ⟨member, zero⟩))
      refine ⟨multiplier • coefficient + functional, ?_⟩
      intro element member
      simpa only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul]
        using bounds element member
    · exact ⟨0, by simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]⟩

theorem orderedGroup_finite_positive_functional (Group : Type*)
    [AddCommGroup Group] [LinearOrder Group] [IsOrderedAddMonoid Group]
    (elements : Finset Group) (positive : ∀ element ∈ elements, 0 < element) :
    ∃ functional : Group →+ ℝ, ∀ element ∈ elements, 0 < functional element := by
  classical
  by_cases nonempty : elements.Nonempty
  · obtain ⟨embedding, injective, _⟩ := hahnEmbedding_isOrderedAddMonoid Group
    have strictly_monotone : StrictMono embedding :=
      (OrderHomClass.monotone embedding).strictMono_of_injective injective
    let series : Group →+ HahnSeries (FiniteArchimedeanClass Group) ℝ :=
      { toFun := fun element => ofLex (embedding element)
        map_zero' := by simp
        map_add' := by intros; simp }
    obtain ⟨first, member⟩ := nonempty
    have first_positive : 0 < toLex (series first) := by
      simpa [series] using strictly_monotone (positive first member)
    have first_nonzero : series first ≠ 0 := by
      intro zero
      simp [zero] at first_positive
    let : Zero (FiniteArchimedeanClass Group) :=
      ⟨(series first).orderTop.untop (HahnSeries.orderTop_ne_top.mpr first_nonzero)⟩
    exact hahnSeries_finite_positive_functional series elements
      (fun element member => by
        simpa [series] using strictly_monotone (positive element member))
  · exact ⟨0, by simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]⟩

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem character_eq_sum_basisCoordinates {Index : Type*} [Fintype Index]
    (basis : Basis Index ℤ Lattice) (character : Lattice →+ ℤ) :
    character = ∑ index, character (basis index) • (basis.coord index).toAddMonoidHom := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  classical
  simp [AddMonoidHom.toIntLinearMap, Basis.coord_apply, Finsupp.single_apply]

theorem realCharacter_sum_basisCoordinates {Index : Type*} [Fintype Index]
    (fan : Fan embedding) (basis : Basis Index ℤ Lattice)
    (functional : (Lattice →+ ℤ) →+ ℝ) (character : Lattice →+ ℤ) :
    fan.lattice.realCharacter character
      (∑ index, functional (basis.coord index).toAddMonoidHom • embedding (basis index)) =
        functional character := by
  classical
  conv_rhs => rw [character_eq_sum_basisCoordinates basis character]
  simp only [map_sum, map_smul, fan.lattice.realCharacter_apply, AddMonoidHom.map_zsmul,
    zsmul_eq_mul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem complete_orderedCharacter_integralCone {Group : Type*}
    [AddCommGroup Group] [LinearOrder Group] [IsOrderedAddMonoid Group]
    (fan : Fan embedding) (complete : fan.IsComplete)
    (order : (Lattice →+ ℤ) →+ Group) :
    ∃ cone : fan.cones, ∀ character : dualSemigroup fan.lattice cone.val,
      0 ≤ order character.val := by
  classical
  by_contra absent
  have witnesses : ∀ cone : fan.cones, ∃ character : dualSemigroup fan.lattice cone.val,
      order character.val < 0 := by
    intro cone
    by_contra all_nonnegative
    apply absent
    exact ⟨cone, fun character => le_of_not_gt (fun negative => all_nonnegative ⟨character, negative⟩)⟩
  choose witness witness_negative using witnesses
  let := Fintype.ofFinite fan.cones
  let values := Finset.univ.image (fun cone : fan.cones => -order (witness cone).val)
  obtain ⟨functional, positive⟩ := BondalThomsen.orderedGroup_finite_positive_functional Group values
    (fun value member => by
      obtain ⟨cone, _, equal⟩ := Finset.mem_image.mp member
      rw [← equal]
      exact neg_pos.mpr (witness_negative cone))
  let := fan.lattice.free
  let := fan.lattice.finite
  let basis := Module.finBasis ℤ Lattice
  let real_order := functional.comp order
  let point := ∑ index, real_order (basis.coord index).toAddMonoidHom • embedding (basis index)
  obtain ⟨cone, member, contains⟩ := fan.isComplete_iff.mp complete point
  let actual_cone : fan.cones := ⟨cone, member⟩
  have bound := (witness actual_cone).property contains
  change 0 ≤ fan.lattice.realCharacter (witness actual_cone).val point at bound
  rw [realCharacter_sum_basisCoordinates fan basis real_order] at bound
  have strictly_positive := positive (-order (witness actual_cone).val)
    (Finset.mem_image.mpr ⟨actual_cone, Finset.mem_univ _, rfl⟩)
  simp only [map_neg] at strictly_positive
  change 0 ≤ functional (order (witness actual_cone).val) at bound
  linarith

section ArbitraryValuationTorus

variable {ValuationRing FractionField : Type} [CommRing ValuationRing] [IsDomain ValuationRing]
    [_root_.ValuationRing ValuationRing] [Field FractionField]
    [Algebra ValuationRing FractionField] [IsFractionRing ValuationRing FractionField]

noncomputable def valuationTorusCharacterValues
    (characters : Multiplicative (Lattice →+ ℤ) →* FractionField) :
    Multiplicative (Lattice →+ ℤ) →* (_root_.ValuationRing.ValueGroup ValuationRing FractionField)ˣ :=
  ((_root_.ValuationRing.valuation ValuationRing FractionField).toMonoidWithZeroHom.toMonoidHom.comp
    characters).toHomUnits

noncomputable def valuationTorusCharacterOrder
    (characters : Multiplicative (Lattice →+ ℤ) →* FractionField) :
    (Lattice →+ ℤ) →+ Additive (_root_.ValuationRing.ValueGroup ValuationRing FractionField)ˣ where
  toFun character := -Additive.ofMul (valuationTorusCharacterValues characters (ofAdd character))
  map_zero' := by simp
  map_add' first second := by
    change -Additive.ofMul (valuationTorusCharacterValues characters (ofAdd first * ofAdd second)) = _
    rw [map_mul]
    exact neg_add _ _

theorem valuationTorusCharacterOrder_nonnegative_iff
    (characters : Multiplicative (Lattice →+ ℤ) →* FractionField) (character : Lattice →+ ℤ) :
    0 ≤ valuationTorusCharacterOrder (ValuationRing := ValuationRing) characters character ↔
      IsLocalization.IsInteger ValuationRing (characters (ofAdd character)) := by
  change 0 ≤ -Additive.ofMul (valuationTorusCharacterValues characters (ofAdd character)) ↔ _
  rw [neg_nonneg]
  change valuationTorusCharacterValues characters (ofAdd character) ≤ 1 ↔ _
  rw [← Units.val_le_val]
  change _root_.ValuationRing.valuation ValuationRing FractionField (characters (ofAdd character)) ≤ 1 ↔ _
  exact (_root_.ValuationRing.mem_integer_iff ValuationRing FractionField _)

theorem complete_valuationTorusCharacters_integral_on_chart (fan : Fan embedding)
    (complete : fan.IsComplete)
    (characters : Multiplicative (Lattice →+ ℤ) →* FractionField) :
    ∃ cone : fan.cones, ∀ character : dualSemigroup fan.lattice cone.val,
      IsLocalization.IsInteger ValuationRing (characters (ofAdd character.val)) := by
  obtain ⟨cone, nonnegative⟩ := fan.complete_orderedCharacter_integralCone complete
    (valuationTorusCharacterOrder (ValuationRing := ValuationRing) characters)
  exact ⟨cone, fun character => (valuationTorusCharacterOrder_nonnegative_iff characters character.val).mp
    (nonnegative character)⟩

section ComplexValuationAlgebras

variable [Algebra 𝕜 ValuationRing] [Algebra 𝕜 FractionField]
    [IsScalarTower 𝕜 ValuationRing FractionField]

theorem complete_valuationTorusPoint_chartRingLift (fan : Fan embedding)
    (complete : fan.IsComplete)
    (generic : MonoidAlgebra 𝕜 (Multiplicative (Lattice →+ ℤ)) →ₐ[𝕜] FractionField) :
    ∃ cone : fan.cones, ∃ lift : affineCoordinateRing 𝕜 fan.lattice cone.val →ₐ[𝕜] ValuationRing,
      (IsScalarTower.toAlgHom 𝕜 ValuationRing FractionField).comp lift =
        generic.comp ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice).toAlgHom.comp
          (faceAffineCoordinateRingMap 𝕜 fan.lattice
            (fan.isToricCone cone.property).salient.bot_isFaceOf)) := by
  let characters := generic.toMonoidHom.comp (MonoidAlgebra.of 𝕜 (Multiplicative (Lattice →+ ℤ)))
  obtain ⟨cone, integral⟩ := fan.complete_valuationTorusCharacters_integral_on_chart
    (ValuationRing := ValuationRing) complete characters
  refine ⟨cone, MonoidAlgebra.lift 𝕜 ValuationRing _
    (fan.valuationChartCharacterLift characters cone integral), ?_⟩
  apply MonoidAlgebra.algHom_ext
  · intro exponent
    simp only [AlgHom.comp_apply, MonoidAlgebra.lift_single, one_smul,
      IsScalarTower.toAlgHom_apply, fan.valuationChartCharacterLift_algebraMap]
    change characters (ofAdd (toAdd exponent).val) =
      generic ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice)
        ((faceAffineCoordinateRingMap 𝕜 fan.lattice
          (fan.isToricCone cone.property).salient.bot_isFaceOf)
            (MonoidAlgebra.single (ofAdd (toAdd exponent)) 1)))
    rw [faceAffineCoordinateRingMap_single, denseTorusCoordinateRingEquiv_single]
    rfl
  · ext

theorem complete_regular_valuationTorusPoint_lift (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (generic : MonoidAlgebra 𝕜 (Multiplicative (Lattice →+ ℤ)) →ₐ[𝕜] FractionField) :
    ∃ cone : fan.cones, ∃ chart_lift : Spec (CommRingCat.of ValuationRing) ⟶ fan.affineToricChart 𝕜 cone,
      Spec.map (CommRingCat.ofHom (algebraMap ValuationRing FractionField)) ≫ chart_lift ≫
          fan.affineToricChartι 𝕜 regular cone =
        Spec.map (CommRingCat.ofHom
          (generic.comp (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).toAlgHom).toRingHom) ≫
            fan.denseTorusι 𝕜 regular (Nonempty.intro cone) ∧
      chart_lift ≫ fan.affineToricChartι 𝕜 regular cone ≫ fan.structureMap 𝕜 regular =
        Spec.map (CommRingCat.ofHom (algebraMap 𝕜 ValuationRing)) := by
  obtain ⟨cone, ring_lift, ring_factorization⟩ :=
    fan.complete_valuationTorusPoint_chartRingLift 𝕜 (ValuationRing := ValuationRing) complete generic
  refine ⟨cone, Spec.map (CommRingCat.ofHom ring_lift.toRingHom), ?_, ?_⟩
  · rw [fan.denseTorusι_face 𝕜 regular cone, faceAffineToricSchemeMap_def]
    simp only [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    exact congrArg (fun map => CommRingCat.ofHom map.toRingHom) ring_factorization
  · rw [fan.chartι_comp_structureMap 𝕜 regular cone, ← Spec.map_comp]
    congr 1
    ext scalar
    exact ring_lift.commutes scalar

theorem complete_regular_valuationTorusMorphism_lift (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    (generic : Spec (CommRingCat.of FractionField) ⟶ fan.denseTorus 𝕜)
    (over_base : generic ≫ fan.denseTorusι 𝕜 regular nonempty ≫ fan.structureMap 𝕜 regular =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 FractionField))) :
    ∃ lift : Spec (CommRingCat.of ValuationRing) ⟶ fan.algebraicRealization 𝕜 regular,
      Spec.map (CommRingCat.ofHom (algebraMap ValuationRing FractionField)) ≫ lift =
        generic ≫ fan.denseTorusι 𝕜 regular nonempty ∧
      lift ≫ fan.structureMap 𝕜 regular = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 ValuationRing)) := by
  let generic_ring : affineCoordinateRing 𝕜 fan.lattice (⊥ : PointedCone ℝ Ambient) →+* FractionField :=
    (Spec.preimage generic).hom
  have generic_scalars : ∀ scalar : 𝕜,
      generic_ring (algebraMap 𝕜 _ scalar) = algebraMap 𝕜 FractionField scalar := by
    change generic ≫ fan.affineToricChartι 𝕜 regular (fan.botCone nonempty) ≫
      fan.structureMap 𝕜 regular = _ at over_base
    rw [fan.chartι_comp_structureMap 𝕜 regular (fan.botCone nonempty),
      ← Spec.map_preimage generic, ← Spec.map_comp] at over_base
    have ring_eq := Spec.map_injective over_base
    exact fun scalar => ConcreteCategory.congr_hom ring_eq scalar
  let generic_algebra : affineCoordinateRing 𝕜 fan.lattice (⊥ : PointedCone ℝ Ambient) →ₐ[𝕜] FractionField :=
    { generic_ring with commutes' := generic_scalars }
  obtain ⟨cone, chart_lift, extension_eq, base_eq⟩ := fan.complete_regular_valuationTorusPoint_lift 𝕜
    (ValuationRing := ValuationRing) complete regular
      (generic_algebra.comp (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm.toAlgHom)
  have generic_eq : Spec.map (CommRingCat.ofHom
      (((generic_algebra.comp (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm.toAlgHom).comp
        (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).toAlgHom).toRingHom)) = generic := by
    rw [← Spec.map_preimage generic]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro element
    exact congrArg generic_ring ((denseTorusCoordinateRingEquiv 𝕜 fan.lattice).symm_apply_apply element)
  rw [generic_eq, fan.denseTorusι_eq 𝕜 regular (Nonempty.intro cone) nonempty] at extension_eq
  exact ⟨chart_lift ≫ fan.affineToricChartι 𝕜 regular cone, extension_eq, base_eq⟩

end ComplexValuationAlgebras

end ArbitraryValuationTorus

theorem complete_regular_valuationTorusSquare_hasLift (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    (square : ValuativeCommSq (fan.structureMap 𝕜 regular))
    (torus_generic : Spec (CommRingCat.of square.K) ⟶ fan.denseTorus 𝕜)
    (factorization : torus_generic ≫ fan.denseTorusι 𝕜 regular nonempty = square.i₁) :
    square.commSq.HasLift := by
  let base_ring : 𝕜 →+* square.R := (Spec.preimage square.i₂).hom
  let : Algebra 𝕜 square.R := base_ring.toAlgebra
  let : Algebra 𝕜 square.K := Algebra.compHom square.K base_ring
  let : IsScalarTower 𝕜 square.R square.K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have base_eq : Spec.map (CommRingCat.ofHom (algebraMap 𝕜 square.R)) = square.i₂ :=
    Spec.map_preimage square.i₂
  have over_base : torus_generic ≫ fan.denseTorusι 𝕜 regular nonempty ≫ fan.structureMap 𝕜 regular =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 square.K)) := by
    rw [← Category.assoc, factorization, square.commSq.w, ← base_eq, ← Spec.map_comp]
    rfl
  obtain ⟨lift, generic_eq, base_extension⟩ := fan.complete_regular_valuationTorusMorphism_lift 𝕜
    (ValuationRing := square.R) complete regular nonempty torus_generic over_base
  exact CommSq.HasLift.mk' ⟨lift, generic_eq.trans factorization, base_extension.trans base_eq⟩

end TauCeti.Toric.Fan
