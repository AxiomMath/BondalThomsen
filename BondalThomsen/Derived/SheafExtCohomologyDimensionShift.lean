module

public import BondalThomsen.Derived.SheafPositiveExtCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import BondalThomsen.Toric.Divisor.DivisorTensorEquivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite

namespace BondalThomsen.SheafExtCohomologyDimensionShift

universe u

noncomputable section

variable {scheme : Scheme.{u}}

open BondalThomsen.InvertibleSheafExtCohomology
open TauCeti.AlgebraicGeometry.Scheme.Modules

def injectiveCokernelSequence (target : scheme.Modules) : ShortComplex scheme.Modules :=
  ShortComplex.mk (Injective.ι target) (cokernel.π (Injective.ι target))
    (cokernel.condition _)

instance (target : scheme.Modules) : Injective (injectiveCokernelSequence target).X₂ :=
  inferInstanceAs (Injective (Injective.under target))

theorem injectiveCokernelSequence_shortExact (target : scheme.Modules) :
    (injectiveCokernelSequence target).ShortExact := by
  change (ShortComplex.mk (Injective.ι target) (cokernel.π (Injective.ι target))
    (cokernel.condition _)).ShortExact
  have exactness := ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk (Injective.ι target) (cokernel.π (Injective.ι target))
      (cokernel.condition _)) (cokernelIsCokernel (Injective.ι target))
  exact { exact := exactness }

section ShortExact

variable {sequence : ShortComplex scheme.Modules} (exact_sequence : sequence.ShortExact)
  [Injective sequence.X₂]

def extSuccEquiv (source : scheme.Modules) (degree : ℕ) :
    Abelian.Ext source sequence.X₃ (degree + 1) ≃+
      Abelian.Ext source sequence.X₁ (degree + 2) :=
  AddEquiv.ofBijective (exact_sequence.extClass.postcomp source rfl) (by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro extension vanishes
      obtain ⟨previous, rfl⟩ := Abelian.Ext.covariant_sequence_exact₃ source
        exact_sequence extension rfl vanishes
      rw [Abelian.Ext.eq_zero_of_injective previous, Abelian.Ext.zero_comp]
    · intro extension
      exact Abelian.Ext.covariant_sequence_exact₁ source exact_sequence extension
        (Abelian.Ext.eq_zero_of_injective _) rfl)

def cohomologySuccEquiv (degree : ℕ) :
    Cohomology sequence.X₃ (degree + 1) ≃+ Cohomology sequence.X₁ (degree + 2) :=
  AddEquiv.ofBijective (cohomologyδ exact_sequence (degree + 1) (degree + 2) rfl)
    ⟨cohomologyδ_injective_of_isFlasque exact_sequence degree,
      cohomologyδ_surjective_of_isFlasque exact_sequence _ _ rfl⟩

def extOneQuotientEquiv (source : scheme.Modules) :
    (Abelian.Ext source sequence.X₃ 0 ⧸
      ((Abelian.Ext.mk₀ sequence.g).postcomp source (add_zero 0)).range) ≃+
        Abelian.Ext source sequence.X₁ 1 :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
    ext extension
    change (∃ previous : Abelian.Ext source sequence.X₂ 0,
      previous.comp (Abelian.Ext.mk₀ sequence.g) (add_zero 0) =
      extension) ↔ extension.comp exact_sequence.extClass rfl = 0
    constructor
    · rintro ⟨previous, rfl⟩
      simp only [Abelian.Ext.comp_assoc_of_second_deg_zero,
        ShortComplex.ShortExact.comp_extClass, Abelian.Ext.comp_zero]
    · intro vanishes
      exact Abelian.Ext.covariant_sequence_exact₃ source exact_sequence extension rfl vanishes)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (exact_sequence.extClass.postcomp source rfl) (by
        intro extension
        exact Abelian.Ext.covariant_sequence_exact₁ source exact_sequence extension
          (Abelian.Ext.eq_zero_of_injective _) rfl))

def cohomologyOneQuotientEquiv :
    (Cohomology sequence.X₃ 0 ⧸ (cohomologyMap sequence.g 0).range) ≃+
      Cohomology sequence.X₁ 1 :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
    ext element
    exact (exact_cohomologyMap_cohomologyδ exact_sequence 0 1 rfl element).symm)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (cohomologyδ exact_sequence 0 1 rfl)
      (cohomologyδ_surjective_of_isFlasque exact_sequence 0 1 rfl))

end ShortExact

theorem structureSheafExtZero_naturality
    {target next_target : scheme.Modules}
    (extension : Abelian.Ext (structureSheaf scheme) target 0)
    (morphism : target ⟶ next_target) :
    structureSheafExtZeroCohomologyEquiv next_target
        (extension.comp (Abelian.Ext.mk₀ morphism) (add_zero 0)) =
      cohomologyMap morphism 0 (structureSheafExtZeroCohomologyEquiv target extension) := by
  obtain ⟨section_morphism, rfl⟩ := Abelian.Ext.addEquiv₀.symm.surjective extension
  simp only [Abelian.Ext.addEquiv₀_symm_apply, Abelian.Ext.mk₀_comp_mk₀]
  change structureSheafHomCohomologyZeroEquiv next_target
      (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (section_morphism ≫ morphism))) =
    cohomologyMap morphism 0 (structureSheafHomCohomologyZeroEquiv target
      (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ section_morphism)))
  simp only [← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  exact structureSheafHomCohomologyZeroEquiv_naturality section_morphism morphism

def structureSheafExtOneCohomologyEquiv_of_shortExact
    {sequence : ShortComplex scheme.Modules} (exact_sequence : sequence.ShortExact)
    [Injective sequence.X₂] :
    Abelian.Ext (structureSheaf scheme) sequence.X₁ 1 ≃+ Cohomology sequence.X₁ 1 :=
  (extOneQuotientEquiv exact_sequence (structureSheaf scheme)).symm.trans
    ((QuotientAddGroup.congr _ _ (structureSheafExtZeroCohomologyEquiv sequence.X₃) (by
      ext element
      rw [AddSubgroup.mem_map]
      constructor
      · rintro ⟨extension, ⟨previous, rfl⟩, rfl⟩
        exact ⟨structureSheafExtZeroCohomologyEquiv sequence.X₂ previous,
          (structureSheafExtZero_naturality previous sequence.g).symm⟩
      · rintro ⟨section_class, rfl⟩
        obtain ⟨previous, rfl⟩ :=
          (structureSheafExtZeroCohomologyEquiv sequence.X₂).surjective section_class
        exact ⟨previous.comp (Abelian.Ext.mk₀ sequence.g) (add_zero 0), ⟨previous, rfl⟩,
          structureSheafExtZero_naturality previous sequence.g⟩)).trans
      (cohomologyOneQuotientEquiv exact_sequence))

def structureSheafExtCohomologyEquiv : (degree : ℕ) → (target : scheme.Modules) →
    Abelian.Ext (structureSheaf scheme) target degree ≃+ Cohomology target degree
  | 0, target => structureSheafExtZeroCohomologyEquiv target
  | 1, target =>
      structureSheafExtOneCohomologyEquiv_of_shortExact
        (injectiveCokernelSequence_shortExact target)
  | degree + 2, target =>
      (extSuccEquiv (injectiveCokernelSequence_shortExact target)
        (structureSheaf scheme) degree).symm.trans
        ((structureSheafExtCohomologyEquiv (degree + 1) (cokernel (Injective.ι target))).trans
          (cohomologySuccEquiv (injectiveCokernelSequence_shortExact target) degree))

section Integral

variable [IsIntegral scheme]

local instance : MonoidalPreadditive scheme.Modules :=
  TauCeti.SheafOfModules.monoidalPreadditive scheme.sheaf

instance invertibleSheafIhom_additive
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    (ihom line_bundle.obj).Additive :=
  (ihom.adjunction line_bundle.obj).right_adjoint_additive

instance invertibleSheafIhom_isEquivalence
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    (ihom line_bundle.obj).IsEquivalence := by
  let := BondalThomsen.invertibleSheafTensor_isEquivalence line_bundle
  exact (ihom.adjunction line_bundle.obj).isEquivalence_right_of_isEquivalence_left

instance invertibleSheafIhom_preservesFiniteLimits
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    PreservesFiniteLimits (ihom line_bundle.obj) := by
  infer_instance

instance invertibleSheafIhom_preservesFiniteColimits
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    PreservesFiniteColimits (ihom line_bundle.obj) := by
  infer_instance

instance invertibleSheafIhom_preservesHomology
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    (ihom line_bundle.obj).PreservesHomology := by
  infer_instance

def extTensorUnitEquiv (source target : scheme.Modules) (degree : ℕ) :
    Abelian.Ext source target degree ≃+ Abelian.Ext (source ⊗ 𝟙_ scheme.Modules) target degree :=
  ((Abelian.extFunctor degree).mapIso (ρ_ source).op).app target
    |>.addCommGroupIsoToAddEquiv

def invertibleSheafExtStructureSheafEquiv
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (target : scheme.Modules) (degree : ℕ) :
    Abelian.Ext line_bundle.obj target degree ≃+
      Abelian.Ext (structureSheaf scheme) ((ihom line_bundle.obj).obj target) degree := by
  letI := BondalThomsen.invertibleSheafTensor_isEquivalence line_bundle
  exact (extTensorUnitEquiv line_bundle.obj target degree).trans
    (ihom.adjunction line_bundle.obj).extEquiv

def invertibleSheafExtCohomologyEquiv
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (target : scheme.Modules) (degree : ℕ) :
    Abelian.Ext line_bundle.obj target degree ≃+
      Cohomology ((ihom line_bundle.obj).obj target) degree :=
  (invertibleSheafExtStructureSheafEquiv line_bundle target degree).trans
    (structureSheafExtCohomologyEquiv degree ((ihom line_bundle.obj).obj target))

end Integral

end

end BondalThomsen.SheafExtCohomologyDimensionShift
