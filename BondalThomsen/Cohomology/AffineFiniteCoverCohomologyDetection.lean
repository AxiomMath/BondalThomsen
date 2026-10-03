module

public import BondalThomsen.Cohomology.AffineCofinalCoverVanishing
public import BondalThomsen.Derived.SheafExtCohomologyDimensionShift
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.AffineQuasicoherentCohomologyVanishing
open BondalThomsen.AffineCechDerivedComparison

namespace BondalThomsen.AffineFiniteCoverCohomologyDetection

universe schemeUniverse indexUniverse

noncomputable section

variable {ring : CommRingCat.{schemeUniverse}}

def restrictSections (coefficient : (Spec ring).Modules)
    {smaller larger : (Spec ring).Opens} (inclusion : smaller ≤ larger) :
    Γ(coefficient, larger) →ₗ[ring] Γ(coefficient, smaller) :=
  sectionRestriction coefficient (homOfLE inclusion)

theorem restrictSections_smul (coefficient : (Spec ring).Modules)
    {smaller larger : (Spec ring).Opens} (inclusion : smaller ≤ larger)
    (scalar : ring) (element : Γ(coefficient, larger)) :
    restrictSections coefficient inclusion (scalar • element) =
      scalar • restrictSections coefficient inclusion element :=
  (restrictSections coefficient inclusion).map_smul scalar element

theorem restrictSections_sub (coefficient : (Spec ring).Modules)
    {smaller larger : (Spec ring).Opens} (inclusion : smaller ≤ larger)
    (first second : Γ(coefficient, larger)) :
    restrictSections coefficient inclusion (first - second) =
      restrictSections coefficient inclusion first -
        restrictSections coefficient inclusion second :=
  (restrictSections coefficient inclusion).map_sub first second

@[simp]
theorem restrictSections_comp (coefficient : (Spec ring).Modules)
    {small middle large : (Spec ring).Opens}
    (first : small ≤ middle) (second : middle ≤ large)
    (element : Γ(coefficient, large)) :
    restrictSections coefficient first (restrictSections coefficient second element) =
      restrictSections coefficient (first.trans second) element := by
  change ((sectionRestriction coefficient (homOfLE first)).comp
    (sectionRestriction coefficient (homOfLE second))) element = _
  rw [sectionRestriction_comp]
  rfl

instance principalRestriction_isLocalized (coefficient : (Spec ring).Modules)
    [coefficient.IsQuasicoherent] (base denominator : ring) :
    IsLocalizedModule.Away denominator
      (restrictSections coefficient (PrimeSpectrum.basicOpen_mul_le_left base denominator)) := by
  let restriction := restrictSections coefficient
    (PrimeSpectrum.basicOpen_mul_le_left base denominator)
  have restriction_global : restriction.comp
      (basicSectionRestriction coefficient base) =
      basicSectionRestriction coefficient (base * denominator) :=
    sectionRestriction_comp_top coefficient
      (homOfLE (PrimeSpectrum.basicOpen_mul_le_left base denominator))
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen denominator
      (PrimeSpectrum.basicOpen_mul_le_right base denominator)
  · intro element
    obtain ⟨exponent, numerator, cleared⟩ := IsLocalizedModule.Away.surj
      (basicSectionRestriction coefficient (base * denominator))
      (base * denominator) element
    obtain ⟨inverse, inverse_equation⟩ := IsUnit.exists_right_inv
      ((Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen base
        (M := coefficient) le_rfl).pow exponent)
    rw [← map_pow] at inverse_equation
    refine ⟨exponent, inverse (basicSectionRestriction coefficient base numerator), ?_⟩
    apply (coefficient.isSMulRegular_of_le_basicOpen
      (PrimeSpectrum.basicOpen_mul_le_left base denominator)).pow exponent
    change base ^ exponent • (denominator ^ exponent • element) =
      base ^ exponent • restriction (inverse (basicSectionRestriction coefficient base numerator))
    rw [← map_smul]
    have cancels : base ^ exponent •
        inverse (basicSectionRestriction coefficient base numerator) =
        basicSectionRestriction coefficient base numerator := by
      exact congrArg (fun endomorphism =>
        endomorphism (basicSectionRestriction coefficient base numerator)) inverse_equation
    rw [cancels]
    change base ^ exponent • (denominator ^ exponent • element) = _
    rw [← mul_smul, ← mul_pow, cleared, ← restriction_global]
    rfl
  · intro element vanishes
    obtain ⟨exponent, numerator, cleared⟩ := IsLocalizedModule.Away.surj
      (basicSectionRestriction coefficient base) base element
    have numerator_zero : basicSectionRestriction coefficient (base * denominator) numerator = 0 := by
      rw [← restriction_global, LinearMap.comp_apply, ← cleared, map_smul, vanishes,
        smul_zero]
    obtain ⟨extra_exponent, killed⟩ := IsLocalizedModule.Away.exists_of_eq
      (base * denominator) (f := basicSectionRestriction coefficient (base * denominator))
      (show basicSectionRestriction coefficient (base * denominator) numerator =
        basicSectionRestriction coefficient (base * denominator) 0 by
          simpa only [map_zero] using numerator_zero)
    refine ⟨extra_exponent, ?_⟩
    apply (coefficient.isSMulRegular_of_le_basicOpen (show
      PrimeSpectrum.basicOpen base ≤ PrimeSpectrum.basicOpen base from le_rfl)).pow
        (extra_exponent + exponent)
    have mapped := congrArg (basicSectionRestriction coefficient base) killed
    rw [map_smul, map_smul, map_zero, smul_zero, ← cleared, mul_pow,
      mul_smul] at mapped
    change base ^ (extra_exponent + exponent) • (denominator ^ extra_exponent • element) =
      base ^ (extra_exponent + exponent) • (0 : Γ(coefficient, PrimeSpectrum.basicOpen base))
    rw [pow_add, mul_smul, smul_zero]
    rw [smul_comm (denominator ^ extra_exponent) (base ^ exponent),
      smul_comm (base ^ extra_exponent) (base ^ exponent)] at mapped
    rw [smul_comm (base ^ exponent) (base ^ extra_exponent)] at mapped
    exact mapped

instance principalIntersectionRestriction_isLocalized
    (coefficient : (Spec ring).Modules) [coefficient.IsQuasicoherent]
    (base denominator : ring) :
    IsLocalizedModule.Away denominator
      (restrictSections coefficient (show
        PrimeSpectrum.basicOpen base ⊓ PrimeSpectrum.basicOpen denominator ≤
          PrimeSpectrum.basicOpen base from inf_le_left)) := by
  let transport := ((modulesSpecToSheaf.obj coefficient).obj.mapIso
    (eqToIso (PrimeSpectrum.basicOpen_mul base denominator)).op).symm.toLinearEquiv
  have comparison : transport.toLinearMap.comp
      (restrictSections coefficient (PrimeSpectrum.basicOpen_mul_le_left base denominator)) =
      restrictSections coefficient (show
        PrimeSpectrum.basicOpen base ⊓ PrimeSpectrum.basicOpen denominator ≤
          PrimeSpectrum.basicOpen base from inf_le_left) := by
    ext element
    change coefficient.presheaf.map _ (coefficient.presheaf.map _ element) = _
    rw [← Functor.map_comp_apply]
    rfl
  rw [← comparison]
  letI localized_principal_restriction :=
    principalRestriction_isLocalized coefficient base denominator
  exact (IsLocalizedModule.comp_iff_of_bijective_left
    (Submonoid.powers denominator) transport.toLinearMap transport.bijective).mpr inferInstance

theorem intersectionRestriction_isLocalized_of_principal
    (coefficient : (Spec ring).Modules) [coefficient.IsQuasicoherent]
    (base_open : (Spec ring).Opens)
    (principal : ∃ generator : ring, base_open = PrimeSpectrum.basicOpen generator)
    (denominator : ring) :
    IsLocalizedModule.Away denominator
      (restrictSections coefficient (show
        base_open ⊓ PrimeSpectrum.basicOpen denominator ≤ base_open from inf_le_left)) := by
  obtain ⟨generator, rfl⟩ := principal
  exact principalIntersectionRestriction_isLocalized coefficient generator denominator

def PrincipalCechCocycle {index : Type indexUniverse}
    (coefficient : (Spec ring).Modules) (generators : index → ring)
    (values : ∀ first second,
      Γ(coefficient, PrimeSpectrum.basicOpen (generators first) ⊓
        PrimeSpectrum.basicOpen (generators second))) : Prop :=
  ∀ first second third,
    restrictSections coefficient (show
      (PrimeSpectrum.basicOpen (generators first) ⊓
        PrimeSpectrum.basicOpen (generators second)) ⊓
          PrimeSpectrum.basicOpen (generators third) ≤
        PrimeSpectrum.basicOpen (generators first) ⊓
          PrimeSpectrum.basicOpen (generators second) from inf_le_left)
      (values first second) +
    restrictSections coefficient (show
      (PrimeSpectrum.basicOpen (generators first) ⊓
        PrimeSpectrum.basicOpen (generators second)) ⊓
          PrimeSpectrum.basicOpen (generators third) ≤
        PrimeSpectrum.basicOpen (generators second) ⊓
          PrimeSpectrum.basicOpen (generators third) from
            inf_le_inf (inf_le_right) le_rfl) (values second third) =
    restrictSections coefficient (show
      (PrimeSpectrum.basicOpen (generators first) ⊓
        PrimeSpectrum.basicOpen (generators second)) ⊓
          PrimeSpectrum.basicOpen (generators third) ≤
        PrimeSpectrum.basicOpen (generators first) ⊓
          PrimeSpectrum.basicOpen (generators third) from
            inf_le_inf (inf_le_left) le_rfl) (values first third)

set_option maxHeartbeats 800000 in

theorem finitePrincipalCech_coboundary
    {index : Type indexUniverse} [Fintype index]
    (coefficient : (Spec ring).Modules) [coefficient.IsQuasicoherent]
    (generators : index → ring)
    (covers : (⨆ cover_index, PrimeSpectrum.basicOpen (generators cover_index)) = ⊤)
    (values : ∀ first second,
      Γ(coefficient, PrimeSpectrum.basicOpen (generators first) ⊓
        PrimeSpectrum.basicOpen (generators second)))
    (cocycle : PrincipalCechCocycle coefficient generators values) :
    ∃ sections : ∀ cover_index, Γ(coefficient, PrimeSpectrum.basicOpen (generators cover_index)),
      ∀ first second,
        restrictSections coefficient inf_le_left (sections first) -
          restrictSections coefficient inf_le_right (sections second) = values first second := by
  classical
  let opens := fun cover_index => PrimeSpectrum.basicOpen (generators cover_index)
  have local_clearing (pivot cover_index : index) :
      ∃ (exponent : ℕ) (lift : Γ(coefficient, opens cover_index)),
        generators pivot ^ exponent • values cover_index pivot =
          restrictSections coefficient inf_le_left lift := by
    exact IsLocalizedModule.Away.surj
      (restrictSections coefficient (show opens cover_index ⊓ opens pivot ≤
        opens cover_index from inf_le_left)) (generators pivot) (values cover_index pivot)
  choose exponents lifts lifts_clear using local_clearing
  let common_exponent := Finset.univ.sup (fun pair : index × index =>
    exponents pair.1 pair.2)
  have exponent_bound (pivot cover_index : index) :
      exponents pivot cover_index ≤ common_exponent :=
    Finset.le_sup (f := fun pair : index × index => exponents pair.1 pair.2)
      (Finset.mem_univ (pivot, cover_index))
  let common_lifts := fun pivot cover_index =>
    generators pivot ^ (common_exponent - exponents pivot cover_index) • lifts pivot cover_index
  have common_lifts_clear (pivot cover_index : index) :
      restrictSections coefficient (show opens cover_index ⊓ opens pivot ≤
        opens cover_index from inf_le_left) (common_lifts pivot cover_index) =
          generators pivot ^ common_exponent • values cover_index pivot := by
    dsimp only [common_lifts]
    rw [map_smul, ← lifts_clear, ← mul_smul, ← pow_add,
      Nat.sub_add_cancel (exponent_bound pivot cover_index)]
  let residual := fun pivot first second =>
    restrictSections coefficient (show opens first ⊓ opens second ≤ opens first from inf_le_left)
        (common_lifts pivot first) -
      restrictSections coefficient (show opens first ⊓ opens second ≤ opens second from inf_le_right)
        (common_lifts pivot second) -
      generators pivot ^ common_exponent • values first second
  have residual_local_zero (pivot first second : index) :
      restrictSections coefficient (show (opens first ⊓ opens second) ⊓ opens pivot ≤
        opens first ⊓ opens second from inf_le_left) (residual pivot first second) = 0 := by
    dsimp only [residual]
    simp only [restrictSections_sub, restrictSections_smul, restrictSections_comp]
    have first_clear := congrArg (restrictSections coefficient (show
      (opens first ⊓ opens second) ⊓ opens pivot ≤ opens first ⊓ opens pivot from
        inf_le_inf inf_le_left le_rfl)) (common_lifts_clear pivot first)
    have second_clear := congrArg (restrictSections coefficient (show
      (opens first ⊓ opens second) ⊓ opens pivot ≤ opens second ⊓ opens pivot from
        inf_le_inf inf_le_right le_rfl)) (common_lifts_clear pivot second)
    simp only [restrictSections_comp, restrictSections_smul] at first_clear second_clear
    rw [first_clear, second_clear]
    have relation := cocycle first second pivot
    change restrictSections coefficient _ (values first second) +
      restrictSections coefficient _ (values second pivot) =
      restrictSections coefficient _ (values first pivot) at relation
    rw [← relation, smul_add]
    abel
  have residual_clearing (pivot first second : index) :
      ∃ exponent : ℕ, generators pivot ^ exponent • residual pivot first second = 0 := by
    letI localized_intersection := intersectionRestriction_isLocalized_of_principal
      coefficient (opens first ⊓ opens second)
      ⟨generators first * generators second, (PrimeSpectrum.basicOpen_mul _ _).symm⟩
      (generators pivot)
    obtain ⟨exponent, killed⟩ := IsLocalizedModule.Away.exists_of_eq (generators pivot)
      (f := restrictSections coefficient (show (opens first ⊓ opens second) ⊓ opens pivot ≤
        opens first ⊓ opens second from inf_le_left))
      (show restrictSections coefficient _ (residual pivot first second) =
        restrictSections coefficient _ 0 from by
          rw [residual_local_zero, map_zero])
    exact ⟨exponent, by simpa only [smul_zero] using killed⟩
  choose extra_exponents extra_kill using residual_clearing
  let common_extra := Finset.univ.sup (fun triple : index × index × index =>
    extra_exponents triple.1 triple.2.1 triple.2.2)
  have extra_bound (pivot first second : index) :
      extra_exponents pivot first second ≤ common_extra :=
    Finset.le_sup (f := fun triple : index × index × index =>
      extra_exponents triple.1 triple.2.1 triple.2.2)
      (Finset.mem_univ (pivot, first, second))
  have common_kill (pivot first second : index) :
      generators pivot ^ common_extra • residual pivot first second = 0 := by
    rw [show common_extra = (common_extra - extra_exponents pivot first second) +
      extra_exponents pivot first second from (Nat.sub_add_cancel (extra_bound pivot first second)).symm,
      pow_add, mul_smul, extra_kill, smul_zero]
  let corrected := fun pivot cover_index =>
    generators pivot ^ common_extra • common_lifts pivot cover_index
  have corrected_difference (pivot first second : index) :
      restrictSections coefficient (show opens first ⊓ opens second ≤ opens first from inf_le_left)
          (corrected pivot first) -
        restrictSections coefficient (show opens first ⊓ opens second ≤ opens second from inf_le_right)
          (corrected pivot second) =
        generators pivot ^ (common_extra + common_exponent) • values first second := by
    have killed := common_kill pivot first second
    dsimp only [residual] at killed
    rw [smul_sub, smul_sub, ← mul_smul, ← pow_add, sub_eq_zero] at killed
    calc
      _ = generators pivot ^ common_extra •
          restrictSections coefficient inf_le_left (common_lifts pivot first) -
        generators pivot ^ common_extra •
          restrictSections coefficient inf_le_right (common_lifts pivot second) := by
        exact congrArg₂ (fun first_value second_value => first_value - second_value)
          (restrictSections_smul coefficient inf_le_left
            (generators pivot ^ common_extra) (common_lifts pivot first))
          (restrictSections_smul coefficient inf_le_right
            (generators pivot ^ common_extra) (common_lifts pivot second))
      _ = _ := killed
  have span_top : Ideal.span (Set.range generators) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp covers
  have powered_span_top : Ideal.span
      (Set.range (fun cover_index => generators cover_index ^ (common_extra + common_exponent))) = ⊤ := by
    have image_range :
        (fun element : ring => element ^ (common_extra + common_exponent)) ''
          Set.range generators =
        Set.range (fun cover_index => generators cover_index ^
          (common_extra + common_exponent)) := by
      ext element
      constructor
      · rintro ⟨_, ⟨cover_index, rfl⟩, rfl⟩
        exact ⟨cover_index, rfl⟩
      · rintro ⟨cover_index, rfl⟩
        exact ⟨generators cover_index, ⟨cover_index, rfl⟩, rfl⟩
    rw [← image_range]
    exact Ideal.span_pow_eq_top (Set.range generators) span_top (common_extra + common_exponent)
  obtain ⟨weights, weights_sum⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : ring) ∈ Ideal.span
      (Set.range (fun cover_index => generators cover_index ^ (common_extra + common_exponent))) from by
        rw [powered_span_top]; trivial)
  refine ⟨fun cover_index => ∑ pivot, weights pivot • corrected pivot cover_index, ?_⟩
  intro first second
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  trans ∑ pivot, (weights pivot * generators pivot ^
    (common_extra + common_exponent)) • values first second
  · apply Finset.sum_congr rfl
    intro pivot membership
    calc
      _ = weights pivot •
          (restrictSections coefficient inf_le_left (corrected pivot first) -
            restrictSections coefficient inf_le_right (corrected pivot second)) := by
        exact (congrArg₂ (fun first_value second_value => first_value - second_value)
          (restrictSections_smul coefficient inf_le_left (weights pivot) (corrected pivot first))
          (restrictSections_smul coefficient inf_le_right (weights pivot) (corrected pivot second))).trans
            (smul_sub _ _ _).symm
      _ = _ := (congrArg (fun element => weights pivot • element)
        (corrected_difference pivot first second)).trans (smul_smul _ _ _)
  · rw [← Finset.sum_smul, weights_sum, one_smul]

def mapSections {first second : (Spec ring).Modules} (morphism : first ⟶ second)
    (open_set : (Spec ring).Opens) : Γ(first, open_set) →ₗ[ring] Γ(second, open_set) :=
  ((modulesSpecToSheaf.map morphism).hom.app (op open_set)).hom

theorem mapSections_restrict {first second : (Spec ring).Modules}
    (morphism : first ⟶ second) {smaller larger : (Spec ring).Opens}
    (inclusion : smaller ≤ larger) (element : Γ(first, larger)) :
    mapSections morphism smaller (restrictSections first inclusion element) =
      restrictSections second inclusion (mapSections morphism larger element) := by
  exact (modulesSpecToSheaf.map morphism).hom.naturality_apply
    (homOfLE inclusion).op element

theorem sectionwise_kernel {sequence : ShortComplex (Spec ring).Modules}
    (exact_sequence : sequence.ShortExact) (open_set : (Spec ring).Opens)
    (element : Γ(sequence.X₂, open_set))
    (vanishes : mapSections sequence.g open_set element = 0) :
    ∃ preimage : Γ(sequence.X₁, open_set), mapSections sequence.f open_set preimage = element := by
  let sections_functor := SheafOfModules.toSheaf (Spec ring).ringCatSheaf ⋙
    sheafToPresheaf _ _ ⋙
    (evaluation _ AddCommGrpCat).obj (op open_set)
  letI section_functor_additive : sections_functor.Additive := by
    dsimp only [sections_functor]
    infer_instance
  letI section_functor_limits : PreservesFiniteLimits sections_functor := by
    dsimp only [sections_functor]
    infer_instance
  have exact_sections := exact_sequence.exact.map_of_mono_of_preservesKernel
    sections_functor
    exact_sequence.mono_f inferInstance
  exact (ShortComplex.ab_exact_iff _).mp exact_sections element vanishes

theorem sectionwise_kernel_injective {sequence : ShortComplex (Spec ring).Modules}
    (exact_sequence : sequence.ShortExact) (open_set : (Spec ring).Opens) :
    Function.Injective (mapSections sequence.f open_set) := by
  letI mono_kernel_map := exact_sequence.mono_f
  exact (AddCommGrpCat.mono_iff_injective
    ((SheafOfModules.toSheaf (Spec ring).ringCatSheaf ⋙ sheafToPresheaf _ _ ⋙
      (evaluation _ AddCommGrpCat).obj (op open_set)).map sequence.f)).mp
      inferInstance

theorem sectionwise_composite_zero {sequence : ShortComplex (Spec ring).Modules}
    (open_set : (Spec ring).Opens) (element : Γ(sequence.X₁, open_set)) :
    mapSections sequence.g open_set (mapSections sequence.f open_set element) = 0 := by
  exact congrArg (fun morphism => morphism.app open_set element) sequence.zero

set_option maxHeartbeats 800000 in

theorem global_lift_of_finite_principal_lifts
    {sequence : ShortComplex (Spec ring).Modules}
    (exact_sequence : sequence.ShortExact) [sequence.X₁.IsQuasicoherent]
    {index : Type schemeUniverse} [Fintype index] (generators : index → ring)
    (covers : (⨆ cover_index, PrimeSpectrum.basicOpen (generators cover_index)) = ⊤)
    (target_section : Γ(sequence.X₃, ⊤))
    (local_lifts : ∀ cover_index, Γ(sequence.X₂, PrimeSpectrum.basicOpen (generators cover_index)))
    (lifts_target : ∀ cover_index,
      mapSections sequence.g (PrimeSpectrum.basicOpen (generators cover_index)) (local_lifts cover_index) =
        restrictSections sequence.X₃ le_top target_section) :
    ∃ global_lift : Γ(sequence.X₂, ⊤), mapSections sequence.g ⊤ global_lift = target_section := by
  let opens := fun cover_index => PrimeSpectrum.basicOpen (generators cover_index)
  let differences := fun first second =>
    restrictSections sequence.X₂ (show opens first ⊓ opens second ≤ opens first from inf_le_left)
        (local_lifts first) -
      restrictSections sequence.X₂ (show opens first ⊓ opens second ≤ opens second from inf_le_right)
        (local_lifts second)
  have differences_kernel (first second : index) :
      mapSections sequence.g (opens first ⊓ opens second) (differences first second) = 0 := by
    dsimp only [differences]
    rw [map_sub, mapSections_restrict, mapSections_restrict, lifts_target, lifts_target,
      restrictSections_comp, restrictSections_comp, sub_self]
  choose cocycle_values cocycle_values_map using
    (fun first second => sectionwise_kernel exact_sequence (opens first ⊓ opens second)
      (differences first second) (differences_kernel first second))
  have cocycle : PrincipalCechCocycle sequence.X₁ generators cocycle_values := by
    intro first second third
    apply sectionwise_kernel_injective exact_sequence
      ((opens first ⊓ opens second) ⊓ opens third)
    rw [map_add, mapSections_restrict, mapSections_restrict, mapSections_restrict,
      cocycle_values_map, cocycle_values_map, cocycle_values_map]
    dsimp only [differences]
    simp only [restrictSections_sub]
    repeat erw [restrictSections_comp]
    abel
  obtain ⟨corrections, corrections_difference⟩ :=
    finitePrincipalCech_coboundary sequence.X₁ generators covers cocycle_values cocycle
  let corrected_lifts := fun cover_index => local_lifts cover_index -
    mapSections sequence.f (opens cover_index) (corrections cover_index)
  have compatible : TopCat.Presheaf.IsCompatible
      (modulesSpecToSheaf.obj sequence.X₂).obj opens corrected_lifts := by
    intro first second
    change restrictSections sequence.X₂ inf_le_left (corrected_lifts first) =
      restrictSections sequence.X₂ inf_le_right (corrected_lifts second)
    have comparison := congrArg (mapSections sequence.f (opens first ⊓ opens second))
      (corrections_difference first second)
    rw [map_sub, mapSections_restrict, mapSections_restrict, cocycle_values_map] at comparison
    dsimp only [corrected_lifts]
    rw [restrictSections_sub, restrictSections_sub,
      ← mapSections_restrict, ← mapSections_restrict]
    dsimp only [differences] at comparison
    have first_naturality := mapSections_restrict sequence.f
      (show opens first ⊓ opens second ≤ opens first from inf_le_left) (corrections first)
    have second_naturality := mapSections_restrict sequence.f
      (show opens first ⊓ opens second ≤ opens second from inf_le_right) (corrections second)
    erw [← first_naturality, ← second_naturality] at comparison
    exact sub_eq_sub_iff_sub_eq_sub.mp comparison.symm
  obtain ⟨global_lift, lift_restrictions, _⟩ :=
    (modulesSpecToSheaf.obj sequence.X₂).existsUnique_gluing' opens ⊤
      (fun cover_index => homOfLE (show opens cover_index ≤ (⊤ : (Spec ring).Opens) from le_top))
      (by rw [covers])
      corrected_lifts compatible
  refine ⟨global_lift, ?_⟩
  apply (modulesSpecToSheaf.obj sequence.X₃).eq_of_locally_eq' opens ⊤
    (fun cover_index => homOfLE (show opens cover_index ≤ (⊤ : (Spec ring).Opens) from le_top))
    (by rw [covers])
  intro cover_index
  change restrictSections sequence.X₃ le_top (mapSections sequence.g ⊤ global_lift) =
    restrictSections sequence.X₃ le_top target_section
  rw [← mapSections_restrict]
  have local_restriction : restrictSections sequence.X₂
      (show opens cover_index ≤ (⊤ : (Spec ring).Opens) from le_top) global_lift =
        corrected_lifts cover_index := lift_restrictions cover_index
  rw [local_restriction]
  dsimp only [corrected_lifts]
  rw [map_sub, sectionwise_composite_zero, sub_zero, lifts_target]

def sectionBoundary {sequence : ShortComplex (Spec ring).Modules}
    (exact_sequence : sequence.ShortExact) (open_set : (Spec ring).Opens) :
    Γ(sequence.X₃, open_set) →+ cohomologyOn sequence.X₁ 1 open_set :=
  ((TauCeti.SheafOfModules.shortExact_map_toSheaf exact_sequence).extClass.postcomp
    ((TauCeti.CategoryTheory.freeYonedaSheafFunctor
      (Opens.grothendieckTopology (Spec ring))).obj open_set) rfl).comp
    (cohomologyOnZeroEquiv sequence.X₃ open_set).symm.toAddMonoidHom

theorem sectionBoundary_restrict {sequence : ShortComplex (Spec ring).Modules}
    (exact_sequence : sequence.ShortExact) {smaller larger : (Spec ring).Opens}
    (inclusion : smaller ≤ larger) (element : Γ(sequence.X₃, larger)) :
    cohomologyOnRes sequence.X₁ 1 inclusion
      (sectionBoundary exact_sequence larger element) =
        sectionBoundary exact_sequence smaller (restrictSections sequence.X₃ inclusion element) := by
  have zero_restriction := cohomologyOnZeroEquiv_restriction sequence.X₃ inclusion
    ((cohomologyOnZeroEquiv sequence.X₃ larger).symm element)
  rw [AddEquiv.apply_symm_apply] at zero_restriction
  have inverse_restriction :
      cohomologyOnRes sequence.X₃ 0 inclusion
        ((cohomologyOnZeroEquiv sequence.X₃ larger).symm element) =
      (cohomologyOnZeroEquiv sequence.X₃ smaller).symm
        (restrictSections sequence.X₃ inclusion element) := by
    apply (cohomologyOnZeroEquiv sequence.X₃ smaller).injective
    exact zero_restriction.trans (AddEquiv.apply_symm_apply _ _).symm
  change (Abelian.Ext.mk₀ ((TauCeti.CategoryTheory.freeYonedaSheafFunctor
    (Opens.grothendieckTopology (Spec ring))).map (homOfLE inclusion))).comp
      (((cohomologyOnZeroEquiv sequence.X₃ larger).symm element).comp
        (TauCeti.SheafOfModules.shortExact_map_toSheaf exact_sequence).extClass rfl)
      (zero_add 1) = _
  rw [← Abelian.Ext.comp_assoc _ _ _ (zero_add 0) rfl (by omega)]
  change (cohomologyOnRes sequence.X₃ 0 inclusion
      ((cohomologyOnZeroEquiv sequence.X₃ larger).symm element)).comp
    (TauCeti.SheafOfModules.shortExact_map_toSheaf exact_sequence).extClass rfl = _
  rw [inverse_restriction]
  rfl

theorem sectionBoundary_eq_zero_iff_lift
    {sequence : ShortComplex (Spec ring).Modules}
    (exact_sequence : sequence.ShortExact) (open_set : (Spec ring).Opens)
    (element : Γ(sequence.X₃, open_set)) :
    sectionBoundary exact_sequence open_set element = 0 ↔
      ∃ lift : Γ(sequence.X₂, open_set), mapSections sequence.g open_set lift = element := by
  let abelian_exact := TauCeti.SheafOfModules.shortExact_map_toSheaf exact_sequence
  let generator := (TauCeti.CategoryTheory.freeYonedaSheafFunctor
    (Opens.grothendieckTopology (Spec ring))).obj open_set
  constructor
  · intro vanishes
    obtain ⟨previous, previous_image⟩ := Abelian.Ext.covariant_sequence_exact₃
      generator abelian_exact ((cohomologyOnZeroEquiv sequence.X₃ open_set).symm element)
      rfl vanishes
    obtain ⟨lift_map, rfl⟩ := Abelian.Ext.addEquiv₀.symm.surjective previous
    refine ⟨TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv
      (Opens.grothendieckTopology (Spec ring)) open_set
      ((SheafOfModules.toSheaf (Spec ring).ringCatSheaf).obj sequence.X₂) lift_map, ?_⟩
    have image_sections := congrArg (cohomologyOnZeroEquiv sequence.X₃ open_set) previous_image
    change cohomologyOnZeroEquiv sequence.X₃ open_set
      ((Abelian.Ext.mk₀ lift_map).comp
        (Abelian.Ext.mk₀ ((SheafOfModules.toSheaf (Spec ring).ringCatSheaf).map sequence.g))
          (add_zero 0)) = _ at image_sections
    rw [Abelian.Ext.mk₀_comp_mk₀] at image_sections
    simp only [cohomologyOnZeroEquiv, AddEquiv.trans_apply,
      ← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply] at image_sections
    erw [AddEquiv.apply_symm_apply] at image_sections
    exact (TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv_naturality_right
      (Opens.grothendieckTopology (Spec ring)) lift_map
      ((SheafOfModules.toSheaf (Spec ring).ringCatSheaf).map sequence.g)).symm.trans
        image_sections
  · rintro ⟨lift, lift_image⟩
    let lift_map := (TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv
      (Opens.grothendieckTopology (Spec ring)) open_set
      ((SheafOfModules.toSheaf (Spec ring).ringCatSheaf).obj sequence.X₂)).symm lift
    have lift_map_image : lift_map ≫
        (SheafOfModules.toSheaf (Spec ring).ringCatSheaf).map sequence.g =
      Abelian.Ext.addEquiv₀ ((cohomologyOnZeroEquiv sequence.X₃ open_set).symm element) := by
      apply (TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv
        (Opens.grothendieckTopology (Spec ring)) open_set
        ((SheafOfModules.toSheaf (Spec ring).ringCatSheaf).obj sequence.X₃)).injective
      rw [TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv_naturality_right]
      simp only [lift_map, AddEquiv.apply_symm_apply]
      change mapSections sequence.g open_set lift =
        cohomologyOnZeroEquiv sequence.X₃ open_set
          ((cohomologyOnZeroEquiv sequence.X₃ open_set).symm element)
      rw [AddEquiv.apply_symm_apply, lift_image]
    change ((cohomologyOnZeroEquiv sequence.X₃ open_set).symm element).comp
      abelian_exact.extClass rfl = 0
    rw [← Abelian.Ext.mk₀_addEquiv₀_apply
      ((cohomologyOnZeroEquiv sequence.X₃ open_set).symm element), ← lift_map_image,
      ← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero]
    erw [abelian_exact.comp_extClass]
    exact Abelian.Ext.comp_zero (Abelian.Ext.mk₀ lift_map) _ 1 1 rfl

theorem sectionBoundary_finite_principal_detection
    {sequence : ShortComplex (Spec ring).Modules}
    (exact_sequence : sequence.ShortExact) [sequence.X₁.IsQuasicoherent]
    {index : Type schemeUniverse} [Fintype index] (generators : index → ring)
    (covers : (⨆ cover_index, PrimeSpectrum.basicOpen (generators cover_index)) = ⊤)
    (element : Γ(sequence.X₃, ⊤))
    (locally_zero : ∀ cover_index,
      cohomologyOnRes sequence.X₁ 1 le_top (sectionBoundary exact_sequence ⊤ element) =
        (0 : cohomologyOn sequence.X₁ 1 (PrimeSpectrum.basicOpen (generators cover_index)))) :
    sectionBoundary exact_sequence ⊤ element = 0 := by
  have local_lifts_exist (cover_index : index) :
      ∃ lift : Γ(sequence.X₂, PrimeSpectrum.basicOpen (generators cover_index)),
        mapSections sequence.g _ lift = restrictSections sequence.X₃ le_top element := by
    apply (sectionBoundary_eq_zero_iff_lift exact_sequence _ _).mp
    rw [← sectionBoundary_restrict]
    exact locally_zero cover_index
  choose lifts lifts_image using local_lifts_exist
  exact (sectionBoundary_eq_zero_iff_lift exact_sequence ⊤ element).mpr
    (global_lift_of_finite_principal_lifts exact_sequence generators covers element lifts lifts_image)

theorem sectionBoundary_surjective_of_isFlasque
    {sequence : ShortComplex (Spec ring).Modules}
    (exact_sequence : sequence.ShortExact) [sequence.X₂.presheaf.IsFlasque]
    (open_set : (Spec ring).Opens) :
    Function.Surjective (sectionBoundary exact_sequence open_set) := by
  intro element
  let abelian_exact := TauCeti.SheafOfModules.shortExact_map_toSheaf exact_sequence
  let generator := (TauCeti.CategoryTheory.freeYonedaSheafFunctor
    (Opens.grothendieckTopology (Spec ring))).obj open_set
  have next_zero : element.comp
      (Abelian.Ext.mk₀ ((SheafOfModules.toSheaf (Spec ring).ringCatSheaf).map sequence.f))
      (add_zero 1) = 0 := by
    exact Subsingleton.elim (α := cohomologyOn sequence.X₂ 1 open_set) _ _
  obtain ⟨previous, previous_image⟩ := Abelian.Ext.covariant_sequence_exact₁
    generator abelian_exact element next_zero rfl
  refine ⟨cohomologyOnZeroEquiv sequence.X₃ open_set previous, ?_⟩
  change ((cohomologyOnZeroEquiv sequence.X₃ open_set).symm
    (cohomologyOnZeroEquiv sequence.X₃ open_set previous)).comp abelian_exact.extClass rfl = _
  rw [AddEquiv.symm_apply_apply]
  exact previous_image

theorem cohomologyOnOne_finite_principal_detection
    (coefficient : (Spec ring).Modules) [coefficient.IsQuasicoherent]
    {index : Type schemeUniverse} [Fintype index] (generators : index → ring)
    (covers : (⨆ cover_index, PrimeSpectrum.basicOpen (generators cover_index)) = ⊤)
    (element : cohomologyOn coefficient 1 ⊤)
    (locally_zero : ∀ cover_index,
      cohomologyOnRes coefficient 1 le_top element =
        (0 : cohomologyOn coefficient 1 (PrimeSpectrum.basicOpen (generators cover_index)))) :
    element = 0 := by
  let sequence := BondalThomsen.SheafExtCohomologyDimensionShift.injectiveCokernelSequence coefficient
  let exact_sequence :=
    BondalThomsen.SheafExtCohomologyDimensionShift.injectiveCokernelSequence_shortExact coefficient
  letI finite_detection_quasicoherent_kernel : sequence.X₁.IsQuasicoherent := by
    change coefficient.IsQuasicoherent
    infer_instance
  letI finite_detection_injective_middle : Injective sequence.X₂ := by
    dsimp only [sequence]
    infer_instance
  letI finite_detection_flasque_middle : sequence.X₂.presheaf.IsFlasque :=
    BondalThomsen.SheafPositiveExtCohomology.injectiveSheaf_isFlasque sequence.X₂
  obtain ⟨quotient_section, section_image⟩ :=
    sectionBoundary_surjective_of_isFlasque exact_sequence ⊤ element
  have boundary_zero := sectionBoundary_finite_principal_detection
    exact_sequence generators covers quotient_section (by
      intro cover_index
      rw [section_image]
      exact locally_zero cover_index)
  exact section_image.symm.trans boundary_zero

theorem affine_cohomologyOnOne_eq_zero
    (coefficient : (Spec ring).Modules) [coefficient.IsQuasicoherent]
    (element : cohomologyOn coefficient 1 ⊤) : element = 0 := by
  obtain ⟨generators, covers, locally_zero⟩ :=
    BondalThomsen.AffineCofinalCoverVanishing.abelianCohomology_finite_principal_local_zero
      ((SheafOfModules.toSheaf (Spec ring).ringCatSheaf).obj coefficient)
      1 (by decide) ⊤ isCompact_univ element
  refine cohomologyOnOne_finite_principal_detection coefficient
    (fun generator : ↥generators => generator.val) ?_ element ?_
  · simpa only [iSup_subtype] using covers
  · intro generator
    exact (locally_zero generator.val generator.property).choose_spec

theorem affine_cohomologyOne_eq_zero
    (coefficient : (Spec ring).Modules) [coefficient.IsQuasicoherent]
    (element : Cohomology coefficient 1) : element = 0 := by
  have vanishes := congrArg (cohomologyOnTopIso coefficient 1).hom
    (affine_cohomologyOnOne_eq_zero coefficient
      ((cohomologyOnTopIso coefficient 1).inv element))
  simpa only [Iso.inv_hom_id_apply, map_zero] using vanishes

instance affine_quasicoherent_cohomologyOne_subsingleton
    (coefficient : (Spec ring).Modules) [coefficient.IsQuasicoherent] :
    Subsingleton (Cohomology coefficient 1) :=
  ⟨fun first second => (affine_cohomologyOne_eq_zero coefficient first).trans
    (affine_cohomologyOne_eq_zero coefficient second).symm⟩

end

end BondalThomsen.AffineFiniteCoverCohomologyDetection
