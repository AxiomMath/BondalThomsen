module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.LocalProperties.Projective

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct

namespace BondalThomsen.AffineInvertibleSheafTrivial

universe u

section RankOneDescent

variable {coefficient module : Type*} [CommRing coefficient]
    [AddCommGroup module] [Module coefficient module]
    (cover : Set coefficient) (spanning : Ideal.span cover = ⊤)
    (localRing : cover → Type*) [∀ index, CommRing (localRing index)]
    [∀ index, Algebra coefficient (localRing index)]
    [∀ index, IsLocalization.Away index.val (localRing index)]
    (localModule : cover → Type*) [∀ index, AddCommGroup (localModule index)]
    [∀ index, Module coefficient (localModule index)]
    [∀ index, Module (localRing index) (localModule index)]
    [∀ index, IsScalarTower coefficient (localRing index) (localModule index)]
    (restriction : ∀ index, module →ₗ[coefficient] localModule index)
    [∀ index, IsLocalizedModule.Away index.val (restriction index)]
    (coordinates : ∀ index, localModule index ≃ₗ[localRing index] localRing index)

include spanning restriction coordinates in

theorem finitePresentation_of_local_rankOne : Module.FinitePresentation coefficient module := by
  apply Module.FinitePresentation.of_localizationSpan' cover spanning (Rₚ := localRing) restriction
  intro index
  exact Module.FinitePresentation.of_equiv (coordinates index).symm

private theorem rankOne_end_eq_scalar (ring : Type*) [CommRing ring]
    (space : Type*) [AddCommGroup space] [Module ring space]
    (coordinate : space ≃ₗ[ring] ring) (endomorphism : space →ₗ[ring] space) :
    endomorphism = LinearMap.lsmul ring space
      (coordinate (endomorphism (coordinate.symm 1))) := by
  ext vector
  have decomposition : vector = coordinate vector • coordinate.symm 1 := by
    apply coordinate.injective
    simp [smul_eq_mul]
  conv_lhs => rw [decomposition]
  apply coordinate.injective
  simp [mul_comm, smul_eq_mul]

include spanning restriction coordinates in

theorem projective_of_local_rankOne : Module.Projective coefficient module := by
  letI := finitePresentation_of_local_rankOne cover spanning localRing localModule
    restriction coordinates
  apply Module.Projective.of_one_mem_range_dualTensorHom
  let endRestriction := fun index => IsLocalizedModule.mapExtendScalars
    (Submonoid.powers index.val) (restriction index) (restriction index) (localRing index)
  apply Submodule.mem_of_isLocalized_span cover spanning
    (fun index => localModule index →ₗ[localRing index] localModule index) endRestriction
  intro index
  let dualRestriction := IsLocalizedModule.mapExtendScalars (Submonoid.powers index.val)
    (restriction index) (Algebra.linearMap coefficient (localRing index)) (localRing index)
  obtain ⟨⟨functional, functionalDenominator⟩, functionalEquation⟩ :=
    IsLocalizedModule.surj (Submonoid.powers index.val) dualRestriction
      (coordinates index).toLinearMap
  obtain ⟨⟨generator, generatorDenominator⟩, generatorEquation⟩ :=
    IsLocalizedModule.surj (Submonoid.powers index.val) (restriction index)
      ((coordinates index).symm 1)
  refine ⟨dualTensorHom coefficient module module (functional ⊗ₜ[coefficient] generator),
    ⟨functional ⊗ₜ[coefficient] generator, rfl⟩,
    functionalDenominator * generatorDenominator, ?_⟩
  apply (IsLocalizedModule.mk'_eq_iff).mpr
  have tensorEquation : endRestriction index
      (dualTensorHom coefficient module module (functional ⊗ₜ[coefficient] generator)) =
      dualTensorHom (localRing index) (localModule index) (localModule index)
        (dualRestriction functional ⊗ₜ[localRing index] restriction index generator) := by
    apply LinearMap.restrictScalars_injective coefficient
    apply IsLocalizedModule.ext (Submonoid.powers index.val) (restriction index)
      (IsLocalizedModule.map_units (restriction index))
    ext vector
    simp [endRestriction, dualRestriction, IsLocalizedModule.mapExtendScalars,
      IsLocalizedModule.map_apply, dualTensorHom_apply, algebraMap_smul]
  rw [tensorEquation, ← functionalEquation, ← generatorEquation]
  have endIdentity : endRestriction index 1 = LinearMap.id := by
    apply LinearMap.restrictScalars_injective coefficient
    apply IsLocalizedModule.ext (Submonoid.powers index.val) (restriction index)
      (IsLocalizedModule.map_units (restriction index))
    ext vector
    simp [endRestriction, IsLocalizedModule.mapExtendScalars, IsLocalizedModule.map_apply]
  rw [endIdentity]
  ext vector
  have reconstruction : (coordinates index) vector • (coordinates index).symm 1 = vector := by
    apply (coordinates index).injective
    simp [smul_eq_mul]
  apply (coordinates index).injective
  simp [dualTensorHom_apply, LinearMap.smul_apply, Submonoid.smul_def, smul_smul,
    mul_comm]
  rw [reconstruction]

include spanning restriction coordinates in

theorem scalarEndomorphism_bijective_of_local_rankOne :
    Function.Bijective (LinearMap.lsmul coefficient module) := by
  letI := finitePresentation_of_local_rankOne cover spanning localRing localModule
    restriction coordinates
  let endRestriction := fun index => IsLocalizedModule.mapExtendScalars
    (Submonoid.powers index.val) (restriction index) (restriction index) (localRing index)
  have scalarRestriction (index : cover) (scalar : coefficient) :
      endRestriction index (LinearMap.lsmul coefficient module scalar) =
        LinearMap.lsmul (localRing index) (localModule index)
          (algebraMap coefficient (localRing index) scalar) := by
    apply LinearMap.restrictScalars_injective coefficient
    apply IsLocalizedModule.ext (Submonoid.powers index.val) (restriction index)
      (IsLocalizedModule.map_units (restriction index))
    ext vector
    simp [endRestriction, IsLocalizedModule.mapExtendScalars, IsLocalizedModule.map_apply,
      algebraMap_smul]
  constructor
  · intro first second same
    apply Module.eq_of_isLocalized_span cover spanning localRing
      (fun index => Algebra.linearMap coefficient (localRing index))
    intro index
    have localized := congrArg (endRestriction index) same
    rw [scalarRestriction, scalarRestriction] at localized
    have evaluated := LinearMap.congr_fun localized ((coordinates index).symm 1)
    change algebraMap coefficient (localRing index) first • (coordinates index).symm 1 =
      algebraMap coefficient (localRing index) second • (coordinates index).symm 1 at evaluated
    change algebraMap coefficient (localRing index) first =
      algebraMap coefficient (localRing index) second
    simpa only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one] using
      congrArg (coordinates index) evaluated
  · intro endomorphism
    change endomorphism ∈ (LinearMap.lsmul coefficient module).range
    apply Submodule.mem_of_isLocalized_span cover spanning
      (fun index => localModule index →ₗ[localRing index] localModule index) endRestriction
    intro index
    let scalar := coordinates index (endRestriction index endomorphism ((coordinates index).symm 1))
    have localScalar : endRestriction index endomorphism =
        LinearMap.lsmul (localRing index) (localModule index) scalar :=
      rankOne_end_eq_scalar _ _ (coordinates index) _
    obtain ⟨⟨numerator, denominator⟩, scalarEquation⟩ :=
      IsLocalizedModule.surj (Submonoid.powers index.val)
        (Algebra.linearMap coefficient (localRing index)) scalar
    change (denominator : coefficient) • scalar =
      algebraMap coefficient (localRing index) numerator at scalarEquation
    refine ⟨LinearMap.lsmul coefficient module numerator, ⟨numerator, rfl⟩,
      denominator, ?_⟩
    apply IsLocalizedModule.mk'_eq_iff.mpr
    rw [scalarRestriction, localScalar]
    ext vector
    change algebraMap coefficient (localRing index) numerator • vector = _
    rw [← scalarEquation]
    simp [Submonoid.smul_def, smul_assoc]

include spanning restriction coordinates in

theorem invertible_of_local_rankOne : Module.Invertible coefficient module := by
  letI := finitePresentation_of_local_rankOne cover spanning localRing localModule
    restriction coordinates
  letI := projective_of_local_rankOne cover spanning localRing localModule restriction coordinates
  let scalarEquiv := LinearEquiv.ofBijective (LinearMap.lsmul coefficient module)
    (scalarEndomorphism_bijective_of_local_rankOne cover spanning localRing localModule
      restriction coordinates)
  exact Module.Invertible.right
    ((dualTensorHomEquiv coefficient module module).trans scalarEquiv.symm)

end RankOneDescent

section Affine

variable (coefficient : CommRingCat.{u}) (sheaf : (Spec coefficient).Modules)
    [TauCeti.SheafOfModules.IsInvertible (R := (Spec coefficient).ringCatSheaf) sheaf]

noncomputable def invertibleSheafTildeGammaIso :
    tilde (moduleSpecΓFunctor.obj sheaf) ≅ sheaf := asIso sheaf.fromTildeΓ

theorem globalSections_isLocalized_basicOpen (element : coefficient) :
    IsLocalizedModule.Away element
      ((modulesSpecToSheaf.obj sheaf).presheaf.map
        (PrimeSpectrum.basicOpen element).leTop.op).hom :=
  (isIso_fromTildeΓ_iff_isLocalizing sheaf).mp inferInstance element

theorem exists_basicOpen_rankOne :
    ∃ cover : Set coefficient, Ideal.span cover = ⊤ ∧
      ∀ element : cover, Nonempty
        (Γ(sheaf, PrimeSpectrum.basicOpen element.val) ≃ₗ[
          Γ(Spec coefficient, PrimeSpectrum.basicOpen element.val)]
          Γ(Spec coefficient, PrimeSpectrum.basicOpen element.val)) := by
  classical
  let atlas := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible sheaf
  let cover : Set coefficient := {element | ∃ index, PrimeSpectrum.basicOpen element ≤ atlas.X index}
  refine ⟨cover, ?_, ?_⟩
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
    apply top_unique
    intro point member
    have covered := (Opens.coversTop_iff (Spec coefficient).carrier atlas.X).mp atlas.coversTop
    obtain ⟨index, contains⟩ := Opens.mem_iSup.mp (covered.symm ▸ member)
    obtain ⟨basic, basicMember, pointMember, subset⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open contains (atlas.X index).isOpen
    obtain ⟨basicOpen, ⟨⟨element, rfl⟩, rfl⟩⟩ := basicMember
    exact Opens.mem_iSup.mpr ⟨element, Opens.mem_iSup.mpr ⟨⟨index, subset⟩, pointMember⟩⟩
  · intro element
    obtain ⟨index, subset⟩ := element.property
    exact ⟨Scheme.Modules.trivializationCoordinate sheaf (atlas.iso index) (homOfLE subset)⟩

theorem globalSections_invertible :
    Module.Invertible coefficient (moduleSpecΓFunctor.obj sheaf) := by
  obtain ⟨cover, spanning, coordinates⟩ := exists_basicOpen_rankOne coefficient sheaf
  let restriction := fun element : cover => ((modulesSpecToSheaf.obj sheaf).presheaf.map
    (homOfLE (show (PrimeSpectrum.basicOpen element.val : (Spec coefficient).Opens) ≤ ⊤
      from le_top)).op).hom
  letI : ∀ element : cover, IsLocalizedModule.Away element.val (restriction element) :=
    fun element => globalSections_isLocalized_basicOpen coefficient sheaf element.val
  exact invertible_of_local_rankOne cover spanning
    (fun element => Γ(Spec coefficient, PrimeSpectrum.basicOpen element.val))
    (fun element => Γ(sheaf, PrimeSpectrum.basicOpen element.val)) restriction
    (fun element => (coordinates element).some)

noncomputable def invertibleSheafUnitIso [IsDomain coefficient]
    [UniqueFactorizationMonoid coefficient] :
    sheaf ≅ SheafOfModules.unit (Spec coefficient).ringCatSheaf := by
  letI := globalSections_invertible coefficient sheaf
  let linearTrivialization := (CommRing.Pic.mk_eq_mk_iff.mp
    (Subsingleton.elim (CommRing.Pic.mk coefficient (moduleSpecΓFunctor.obj sheaf))
      (CommRing.Pic.mk coefficient coefficient))).some
  exact (invertibleSheafTildeGammaIso coefficient sheaf).symm ≪≫
    (tilde.functor coefficient).mapIso linearTrivialization.toModuleIso ≪≫ tildeSelf

end Affine

end BondalThomsen.AffineInvertibleSheafTrivial
