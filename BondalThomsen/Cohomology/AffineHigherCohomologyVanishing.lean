module

public import BondalThomsen.Cohomology.AffineFiniteCoverCohomologyDetection
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.AffineQuasicoherentCohomologyVanishing
open BondalThomsen.AffineFiniteCoverCohomologyDetection

namespace BondalThomsen.AffineHigherCohomologyVanishing

universe moduleUniverse

noncomputable section

theorem injective_extension_of_finite_relations
    {ring : Type moduleUniverse} [CommRing ring] [IsNoetherianRing ring]
    {target : Type moduleUniverse} [AddCommGroup target] [Module ring target]
    [Module.Injective ring target] (ideal : Ideal ring)
    {relations : Type moduleUniverse} [AddCommGroup relations] [Module ring relations]
    [Module.Finite ring relations] (first : relations →ₗ[ring] ring)
    (second : relations →ₗ[ring] target)
    (annihilated : ∃ exponent : ℕ, ideal ^ exponent • first.ker = ⊥) :
    ∃ (exponent : ℕ) (extension : ring →ₗ[ring] target),
      ∀ element ∈ ideal ^ exponent • (⊤ : Submodule ring relations),
        extension (first element) = second element := by
  obtain ⟨annihilator_exponent, kills⟩ := annihilated
  obtain ⟨artin_rees_exponent, artin_rees⟩ :=
    ideal.exists_pow_inf_eq_pow_smul first.ker
  let exponent := artin_rees_exponent + annihilator_exponent
  let domain : Submodule ring relations := ideal ^ exponent • ⊤
  have disjoint_relations : Disjoint domain first.ker := by
    rw [disjoint_iff]
    change ideal ^ exponent • ⊤ ⊓ first.ker = ⊥
    rw [artin_rees exponent (Nat.le_add_right _ _)]
    have bounded : ideal ^ (exponent - artin_rees_exponent) •
        (ideal ^ artin_rees_exponent • (⊤ : Submodule ring relations) ⊓ first.ker) ≤ ⊥ := by
      dsimp only [exponent]
      rw [Nat.add_sub_cancel_left]
      exact le_trans (Submodule.smul_mono le_rfl
        (show ideal ^ artin_rees_exponent • (⊤ : Submodule ring relations) ⊓ first.ker ≤
          first.ker from inf_le_right)) kills.le
    exact le_antisymm bounded bot_le
  have first_injective : Function.Injective (first.domRestrict domain) := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro element zero_image
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp disjoint_relations) element.val
      element.property (show element.val ∈ first.ker from zero_image)
  obtain ⟨extension, extension_equation⟩ :=
    Module.Injective.out (first.domRestrict domain) first_injective (second.domRestrict domain)
  exact ⟨exponent, extension, fun element membership =>
    extension_equation ⟨element, membership⟩⟩

theorem finitelyGenerated_uniform_annihilator_power
    {ring : Type moduleUniverse} [CommRing ring]
    {module : Type moduleUniverse} [AddCommGroup module] [Module ring module]
    (submodule : Submodule ring module) (finite : submodule.FG) (denominator : ring)
    (pointwise : ∀ element ∈ submodule, ∃ exponent : ℕ, denominator ^ exponent • element = 0) :
    ∃ exponent : ℕ, denominator ^ exponent ∈ submodule.annihilator := by
  classical
  obtain ⟨generators, generates⟩ := finite
  have local_annihilator (generator : ↥generators) :
      ∃ exponent : ℕ, denominator ^ exponent • generator.val = 0 :=
    pointwise generator.val (generates ▸ Submodule.subset_span generator.property)
  choose exponents kills using local_annihilator
  let exponent := Finset.univ.sup exponents
  refine ⟨exponent, Submodule.mem_annihilator.mpr ?_⟩
  rw [← generates]
  intro element membership
  refine Submodule.span_induction (fun generator generator_membership => ?_)
    (by simp) (fun first second first_mem second_mem first_zero second_zero => by
      rw [smul_add, first_zero, second_zero, add_zero])
    (fun scalar element element_mem element_zero => by
      rw [smul_comm (denominator ^ exponent) scalar element, element_zero, smul_zero]) membership
  let generator : ↥generators := ⟨generator, generator_membership⟩
  have bounded : exponents generator ≤ exponent := Finset.le_sup (Finset.mem_univ generator)
  rw [← Nat.sub_add_cancel bounded, pow_add, mul_smul, kills generator, smul_zero]

set_option maxHeartbeats 800000 in

theorem finitePrincipal_section_power_extends
    {ring : CommRingCat.{moduleUniverse}} (coefficient : (Spec ring).Modules)
    [coefficient.IsQuasicoherent]
    {index : Type moduleUniverse} [Fintype index] (generators : index → ring)
    (open_set : (Spec ring).Opens)
    (covers : (⨆ cover_index, PrimeSpectrum.basicOpen (generators cover_index)) = open_set)
    (denominator : ring) (contained : PrimeSpectrum.basicOpen denominator ≤ open_set)
    (element : Γ(coefficient, open_set)) :
    ∃ (exponent : ℕ) (global_section : Γ(coefficient, ⊤)),
      restrictSections coefficient le_top global_section = denominator ^ exponent • element := by
  classical
  obtain ⟨initial_exponent, numerator, cleared⟩ :=
    IsLocalizedModule.Away.surj (basicSectionRestriction coefficient denominator) denominator
      (restrictSections coefficient contained element)
  have principal_contained (cover_index : index) :
      PrimeSpectrum.basicOpen (generators cover_index) ≤ open_set :=
    covers ▸ le_iSup (fun cover_index => PrimeSpectrum.basicOpen (generators cover_index)) cover_index
  let residual (cover_index : index) :=
    basicSectionRestriction coefficient (generators cover_index) numerator -
      denominator ^ initial_exponent •
        restrictSections coefficient (principal_contained cover_index) element
  have residual_locally_zero (cover_index : index) :
      restrictSections coefficient (show
        PrimeSpectrum.basicOpen (generators cover_index) ⊓ PrimeSpectrum.basicOpen denominator ≤
          PrimeSpectrum.basicOpen (generators cover_index) from inf_le_left)
        (residual cover_index) = 0 := by
    dsimp only [residual, basicSectionRestriction]
    rw [restrictSections_sub, restrictSections_smul]
    change restrictSections coefficient inf_le_left
        (restrictSections coefficient le_top numerator) - _ = 0
    rw [restrictSections_comp, restrictSections_comp]
    have restricted := congrArg
      (restrictSections coefficient (show
        PrimeSpectrum.basicOpen (generators cover_index) ⊓ PrimeSpectrum.basicOpen denominator ≤
          PrimeSpectrum.basicOpen denominator from inf_le_right)) cleared
    change restrictSections coefficient inf_le_right
        (denominator ^ initial_exponent • restrictSections coefficient contained element) =
      restrictSections coefficient inf_le_right (restrictSections coefficient le_top numerator)
      at restricted
    rw [restrictSections_smul, restrictSections_comp, restrictSections_comp] at restricted
    exact sub_eq_zero.mpr restricted.symm
  have residual_annihilated (cover_index : index) :
      ∃ exponent : ℕ, denominator ^ exponent • residual cover_index = 0 := by
    let relative_localization_for_extension :=
      principalIntersectionRestriction_isLocalized coefficient (generators cover_index) denominator
    obtain ⟨exponent, kills⟩ := IsLocalizedModule.Away.exists_of_eq denominator
      ((residual_locally_zero cover_index).trans (map_zero _).symm)
    exact ⟨exponent, by simpa only [smul_zero] using kills⟩
  choose exponents kills using residual_annihilated
  let exponent := Finset.univ.sup exponents
  refine ⟨exponent + initial_exponent, denominator ^ exponent • numerator, ?_⟩
  apply (modulesSpecToSheaf.obj coefficient).eq_of_locally_eq'
    (fun cover_index => PrimeSpectrum.basicOpen (generators cover_index)) open_set
    (fun cover_index => homOfLE (principal_contained cover_index)) (by rw [covers])
  intro cover_index
  change restrictSections coefficient (principal_contained cover_index)
      (restrictSections coefficient le_top (denominator ^ exponent • numerator)) =
    restrictSections coefficient (principal_contained cover_index)
      (denominator ^ (exponent + initial_exponent) • element)
  rw [restrictSections_smul, restrictSections_smul, restrictSections_smul,
    restrictSections_comp, pow_add, mul_smul]
  have bounded : exponents cover_index ≤ exponent := Finset.le_sup (Finset.mem_univ cover_index)
  have uniform_zero : denominator ^ exponent • residual cover_index = 0 := by
    rw [← Nat.sub_add_cancel bounded, pow_add, mul_smul, kills cover_index, smul_zero]
  have residual_difference : residual cover_index =
      restrictSections coefficient le_top numerator -
        denominator ^ initial_exponent •
          restrictSections coefficient (principal_contained cover_index) element := rfl
  rw [residual_difference, smul_sub] at uniform_zero
  exact sub_eq_zero.mp uniform_zero

set_option maxHeartbeats 800000 in

theorem injectiveGlobalSections_restriction_surjective
    {ring : CommRingCat.{moduleUniverse}} [IsNoetherianRing ring]
    (coefficient : (Spec ring).Modules) [coefficient.IsQuasicoherent]
    [Module.Injective ring Γ(coefficient, ⊤)] (open_set : (Spec ring).Opens) :
    Function.Surjective (restrictSections coefficient (show open_set ≤ ⊤ from le_top)) := by
  classical
  let noetherian_spectrum_for_extension : NoetherianSpace (PrimeSpectrum ring) := inferInstance
  obtain ⟨generators, contained, covers⟩ :=
    BondalThomsen.AffineCofinalCoverVanishing.exists_finite_principal_cover open_set
      (NoetherianSpace.isCompact _) (fun _ => True) (by
        intro point membership
        obtain ⟨principal, ⟨generator, rfl⟩, generator_membership, inclusion⟩ :=
          (Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) membership
        exact ⟨generator, generator_membership, inclusion, trivial⟩)
  let cover_generators : ↥generators → ring := fun generator => generator.val
  have subtype_covers : (⨆ generator : ↥generators,
      PrimeSpectrum.basicOpen (cover_generators generator)) = open_set := by
    simpa only [cover_generators, iSup_subtype] using covers
  intro element
  have local_extensions (generator : ↥generators) :
      ∃ (exponent : ℕ) (global_section : Γ(coefficient, ⊤)),
        restrictSections coefficient le_top global_section =
          generator.val ^ exponent • element :=
    finitePrincipal_section_power_extends coefficient cover_generators open_set subtype_covers
      generator.val (contained generator.val generator.property).1 element
  choose exponents numerators numerator_images using local_extensions
  let powered_generator (generator : ↥generators) := generator.val ^ (exponents generator + 1)
  let powered_numerator (generator : ↥generators) := generator.val • numerators generator
  have powered_images (generator : ↥generators) :
      restrictSections coefficient le_top (powered_numerator generator) =
        powered_generator generator • element := by
    dsimp only [powered_numerator]
    rw [restrictSections_smul, numerator_images]
    simp only [powered_generator, pow_succ', mul_smul]
  let relations : Submodule ring (ring × Γ(coefficient, ⊤)) :=
    Submodule.span ring (Set.range (fun generator : ↥generators =>
      (powered_generator generator, powered_numerator generator)))
  let finite_section_relations : Module.Finite ring relations :=
    Module.Finite.of_fg (Submodule.fg_def.mpr
      ⟨_, Set.finite_range _, rfl⟩)
  let first : relations →ₗ[ring] ring :=
    (LinearMap.fst ring ring Γ(coefficient, ⊤)).comp relations.subtype
  let second : relations →ₗ[ring] Γ(coefficient, ⊤) :=
    (LinearMap.snd ring ring Γ(coefficient, ⊤)).comp relations.subtype
  have relation_images (relation : relations) :
      restrictSections coefficient le_top (second relation) = first relation • element := by
    have relation_kernel : relations ≤
        ((restrictSections coefficient (show open_set ≤ ⊤ from le_top)).comp
          (LinearMap.snd ring ring Γ(coefficient, ⊤)) -
        (LinearMap.toSpanSingleton ring Γ(coefficient, open_set) element).comp
          (LinearMap.fst ring ring Γ(coefficient, ⊤))).ker := by
      apply Submodule.span_le.mpr
      rintro pair ⟨generator, rfl⟩
      exact sub_eq_zero.mpr (powered_images generator)
    exact sub_eq_zero.mp (relation_kernel relation.property)
  let kernel_image := first.ker.map second
  have kernel_image_finite : kernel_image.FG :=
    (IsNoetherian.noetherian first.ker).map second
  have kernel_image_zero (section_value : Γ(coefficient, ⊤))
      (membership : section_value ∈ kernel_image) :
      restrictSections coefficient (show open_set ≤ ⊤ from le_top) section_value = 0 := by
    obtain ⟨relation, in_kernel, rfl⟩ := Submodule.mem_map.mp membership
    rw [relation_images, show first relation = 0 from in_kernel, zero_smul]
  let ideal : Ideal ring := Ideal.span (Set.range powered_generator)
  have radical_annihilator : ideal ≤ kernel_image.annihilator.radical := by
    apply Ideal.span_le.mpr
    rintro scalar ⟨generator, rfl⟩
    obtain ⟨power, kills⟩ := finitelyGenerated_uniform_annihilator_power
      kernel_image kernel_image_finite (powered_generator generator) (by
        intro section_value membership
        have localized_zero : basicSectionRestriction coefficient (powered_generator generator)
            section_value = 0 := by
          have inclusion : PrimeSpectrum.basicOpen (powered_generator generator) ≤ open_set := by
            simpa only [powered_generator, PrimeSpectrum.basicOpen_pow
              generator.val (exponents generator + 1) (by omega)] using
              (contained generator.val generator.property).1
          have restriction_zero := congrArg (restrictSections coefficient inclusion)
            (kernel_image_zero section_value membership)
          rw [restrictSections_comp, map_zero] at restriction_zero
          exact restriction_zero
        obtain ⟨power, kills⟩ := IsLocalizedModule.Away.exists_of_eq
          (powered_generator generator) (localized_zero.trans (map_zero _).symm)
        exact ⟨power, by simpa only [smul_zero] using kills⟩)
    exact Ideal.mem_radical_iff.mpr ⟨power, kills⟩
  obtain ⟨kernel_exponent, kernel_kills⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg radical_annihilator ideal.fg_of_isNoetherianRing
  have kernel_annihilated : ideal ^ kernel_exponent • first.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro relation membership
    have relation_in_kernel : relation ∈ first.ker := Submodule.smul_le_right membership
    have second_zero : second relation = 0 := by
      have image_membership : second relation ∈ ideal ^ kernel_exponent • kernel_image := by
        rw [← Submodule.map_smul'']
        exact Submodule.mem_map_of_mem membership
      have killed : ideal ^ kernel_exponent • kernel_image = ⊥ :=
        le_antisymm ((Submodule.smul_mono kernel_kills le_rfl).trans
          kernel_image.annihilator_smul.le) bot_le
      exact (Submodule.mem_bot ring).mp (killed ▸ image_membership)
    change relation = 0
    apply Subtype.ext
    exact Prod.ext (show first relation = 0 from relation_in_kernel) second_zero
  obtain ⟨extension_exponent, extension, extension_images⟩ :=
    injective_extension_of_finite_relations ideal first second
      ⟨kernel_exponent, kernel_annihilated⟩
  refine ⟨extension 1, ?_⟩
  apply (modulesSpecToSheaf.obj coefficient).eq_of_locally_eq'
    (fun generator : ↥generators => PrimeSpectrum.basicOpen generator.val) open_set
    (fun generator => homOfLE (contained generator.val generator.property).1)
    (by rw [iSup_subtype, covers])
  intro generator
  let relation : relations :=
    ⟨(powered_generator generator, powered_numerator generator), Submodule.subset_span ⟨generator, rfl⟩⟩
  have multiplied_membership : powered_generator generator ^ extension_exponent • relation ∈
      ideal ^ extension_exponent • (⊤ : Submodule ring relations) :=
    Submodule.smul_mem_smul
      (Ideal.pow_mem_pow (show powered_generator generator ∈ ideal from
        Ideal.subset_span ⟨generator, rfl⟩) extension_exponent) trivial
  have extension_image := extension_images
    (powered_generator generator ^ extension_exponent • relation) multiplied_membership
  change extension (powered_generator generator ^ extension_exponent * powered_generator generator) =
    powered_generator generator ^ extension_exponent • powered_numerator generator at extension_image
  have section_equation := congrArg (restrictSections coefficient
      (show open_set ≤ (⊤ : (Spec ring).Opens) from le_top)) extension_image
  rw [restrictSections_smul, powered_images] at section_equation
  have scalar_image : extension
      (powered_generator generator ^ extension_exponent * powered_generator generator) =
      powered_generator generator ^ (extension_exponent + 1) • extension 1 := by
    rw [pow_succ, ← extension.map_smul, smul_eq_mul, mul_one]
  rw [scalar_image, restrictSections_smul, ← mul_smul, ← pow_succ] at section_equation
  have local_equation := congrArg
    (restrictSections coefficient (contained generator.val generator.property).1) section_equation
  rw [restrictSections_smul, restrictSections_smul] at local_equation
  have regular := (coefficient.isSMulRegular_of_le_basicOpen
      (show PrimeSpectrum.basicOpen generator.val ≤ PrimeSpectrum.basicOpen generator.val
        from le_rfl)).pow
      ((exponents generator + 1) * (extension_exponent + 1))
  change restrictSections coefficient (contained generator.val generator.property).1
      (restrictSections coefficient le_top (extension 1)) =
    restrictSections coefficient (contained generator.val generator.property).1 element
  apply regular
  simpa only [powered_generator, ← pow_mul] using local_equation

theorem injectiveGlobalSections_isFlasque
    {ring : CommRingCat.{moduleUniverse}} [IsNoetherianRing ring]
    (coefficient : (Spec ring).Modules) [coefficient.IsQuasicoherent]
    [Module.Injective ring Γ(coefficient, ⊤)] : coefficient.presheaf.IsFlasque := by
  constructor
  intro first_open second_open inclusion
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro element
  obtain ⟨global_section, restriction_image⟩ :=
    injectiveGlobalSections_restriction_surjective coefficient second_open.unop element
  refine ⟨restrictSections coefficient
    (show first_open.unop ≤ ⊤ from le_top) global_section, ?_⟩
  change restrictSections coefficient
    (leOfHom inclusion.unop)
    (restrictSections coefficient (show first_open.unop ≤ ⊤ from le_top) global_section) = element
  rw [restrictSections_comp]
  exact restriction_image

theorem injectiveTilde_isFlasque
    {ring : CommRingCat.{moduleUniverse}} [IsNoetherianRing ring]
    (module : ModuleCat.{moduleUniverse} ring) [Injective module] :
    (tilde module).presheaf.IsFlasque := by
  let injective_module_for_tilde : Module.Injective ring module :=
    Module.injective_module_of_injective_object ring module
  let injective_tilde_global_sections : Module.Injective ring Γ(tilde module, ⊤) :=
    (Module.Baer.of_equiv (tilde.isoTop module).toLinearEquiv
      (Module.Baer.of_injective (inferInstance : Module.Injective ring module))).injective
  exact injectiveGlobalSections_isFlasque (tilde module)

end

end BondalThomsen.AffineHigherCohomologyVanishing
