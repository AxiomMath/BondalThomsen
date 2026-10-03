module

public import BondalThomsen.Toric.Scheme.CotangentSheafTildeIso
public import BondalThomsen.Toric.Canonical.Exterior

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace
open PrimeSpectrum

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace BondalThomsen.CanonicalTopExterior

noncomputable def exteriorPresheafHom {SchemeModel : Scheme}
    {source target : SchemeModel.PresheafOfModules}
    (morphism : source ⟶ target) (degree : ℕ) :
    exteriorPresheaf.{0, 0, 0, 0} source degree ⟶
      exteriorPresheaf.{0, 0, 0, 0} target degree where
  app domain := by
    let linear : source.obj domain →ₗ[SchemeModel.presheaf.obj domain] target.obj domain :=
      (morphism.app domain).hom
    exact ModuleCat.ofHom
      (X := ModuleCat.of (SchemeModel.presheaf.obj domain)
        ↥(⋀[SchemeModel.presheaf.obj domain]^degree (source.obj domain)))
      (Y := ModuleCat.of (SchemeModel.presheaf.obj domain)
        ↥(⋀[SchemeModel.presheaf.obj domain]^degree (target.obj domain)))
      (exteriorPower.map degree linear)
  naturality {domain smaller} restriction := by
    apply ModuleCat.hom_ext
    apply exteriorLinear_ext (Coefficient := SchemeModel.presheaf.obj domain)
      (Source := source.obj domain) (degree := degree)
    intro vectors
    let smallerLinear : source.obj smaller →ₗ[SchemeModel.presheaf.obj smaller]
        target.obj smaller := (morphism.app smaller).hom
    let domainLinear : source.obj domain →ₗ[SchemeModel.presheaf.obj domain]
        target.obj domain := (morphism.app domain).hom
    change exteriorPower.map degree smallerLinear
        ((exteriorPresheaf source degree).map restriction
          (exteriorPower.ιMulti (SchemeModel.presheaf.obj domain) degree vectors)) =
      (exteriorPresheaf target degree).map restriction
        (exteriorPower.map degree domainLinear
          (exteriorPower.ιMulti (SchemeModel.presheaf.obj domain) degree vectors))
    have sourceWedge := exteriorPresheaf_map_wedge
      (Coefficients := SchemeModel.presheaf) source degree restriction vectors
    have targetWedge := exteriorPresheaf_map_wedge
      (Coefficients := SchemeModel.presheaf) target degree restriction
        (fun index => domainLinear (vectors index))
    calc
      _ = exteriorPower.map degree smallerLinear
          (exteriorPower.ιMulti (SchemeModel.presheaf.obj smaller) degree
            (fun index => source.map restriction (vectors index))) :=
        congrArg (exteriorPower.map degree smallerLinear) sourceWedge
      _ = exteriorPower.ιMulti (M := target.obj smaller) (SchemeModel.presheaf.obj smaller) degree
          (fun index => smallerLinear (source.map restriction (vectors index))) :=
        exteriorPower.map_apply_ιMulti _ _
      _ = exteriorPower.ιMulti (M := target.obj smaller) (SchemeModel.presheaf.obj smaller) degree
          (fun index => (target.map restriction (domainLinear (vectors index)) :
            target.obj smaller)) := by
        congr 1
        funext index
        exact PresheafOfModules.naturality_apply morphism restriction (vectors index)
      _ = (exteriorPresheaf target degree).map restriction
          (exteriorPower.ιMulti (SchemeModel.presheaf.obj domain) degree
            (fun index => domainLinear (vectors index))) := targetWedge.symm
      _ = _ := congrArg (fun vector => (exteriorPresheaf target degree).map restriction vector)
        (exteriorPower.map_apply_ιMulti domainLinear vectors).symm

theorem exteriorPresheafHom_comp {SchemeModel : Scheme}
    {first middle last : SchemeModel.PresheafOfModules}
    (firstMap : first ⟶ middle) (secondMap : middle ⟶ last) (degree : ℕ) :
    exteriorPresheafHom (firstMap ≫ secondMap) degree =
      exteriorPresheafHom firstMap degree ≫ exteriorPresheafHom secondMap degree := by
  apply PresheafOfModules.hom_ext
  intro domain
  apply ModuleCat.hom_ext
  let firstLinear : first.obj domain →ₗ[SchemeModel.presheaf.obj domain] middle.obj domain :=
    (firstMap.app domain).hom
  let secondLinear : middle.obj domain →ₗ[SchemeModel.presheaf.obj domain] last.obj domain :=
    (secondMap.app domain).hom
  exact exteriorPower.map_comp firstLinear secondLinear

theorem exteriorPresheafHom_id {SchemeModel : Scheme}
    (modules : SchemeModel.PresheafOfModules) (degree : ℕ) :
    exteriorPresheafHom (𝟙 modules) degree = 𝟙 (exteriorPresheaf modules degree) := by
  apply PresheafOfModules.hom_ext
  intro domain
  apply ModuleCat.hom_ext
  exact exteriorPower.map_id (R := SchemeModel.presheaf.obj domain)
    (M := modules.obj domain) (n := degree)

noncomputable def exteriorSheafIso {SchemeModel : Scheme}
    {source target : SchemeModel.Modules} (comparison : source ≅ target) (degree : ℕ) :
    exteriorSheaf source degree ≅ exteriorSheaf target degree :=
  (PresheafOfModules.sheafification (𝟙 SchemeModel.ringCatSheaf.obj)).mapIso
    { hom := exteriorPresheafHom comparison.hom.val degree
      inv := exteriorPresheafHom comparison.inv.val degree
      hom_inv_id := by
        rw [← exteriorPresheafHom_comp, ← SheafOfModules.comp_val, comparison.hom_inv_id]
        exact exteriorPresheafHom_id source.val degree
      inv_hom_id := by
        rw [← exteriorPresheafHom_comp, ← SheafOfModules.comp_val, comparison.inv_hom_id]
        exact exteriorPresheafHom_id target.val degree }

noncomputable def canonicalExteriorSpecIso (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] (dimension : ℕ) :
    canonicalExteriorSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) dimension ≅
      exteriorSheaf (tilde (CanonicalAffine.differentialModule Base CoordinateRing)) dimension :=
  exteriorSheafIso (CotangentTilde.cotangentSheafSpecTildeIso Base CoordinateRing) dimension

end BondalThomsen.CanonicalTopExterior

namespace BondalThomsen.CanonicalTopExterior

variable (CoordinateRing : CommRingCat) (modules : ModuleCat CoordinateRing)
    {dimension : ℕ} (basis : Basis (Fin dimension) CoordinateRing modules)

noncomputable def tildeToBasicOpen (denominator : CoordinateRing) :
    modules ⟶ (ModuleCat.restrictScalars
      (algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator))).obj
        ((tilde modules).val.obj (op (basicOpen denominator))) := by
  let comparison := (AlgebraicGeometry.tilde.toOpen modules (basicOpen denominator)).hom
  exact ModuleCat.ofHom
    (X := modules)
    (Y := (ModuleCat.restrictScalars
      (algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator))).obj
        ((tilde modules).val.obj (op (basicOpen denominator))))
    { comparison.toAddHom with map_smul' := fun scalar vector => comparison.map_smul scalar vector }

instance tildeToBasicOpen_isLocalized (denominator : CoordinateRing) :
    IsLocalizedModule (.powers denominator) (tildeToBasicOpen CoordinateRing modules denominator).hom := by
  let SectionRing := Γ(Spec CoordinateRing, basicOpen denominator)
  let Native := (tilde modules).val.obj (op (basicOpen denominator))
  let Restricted := (ModuleCat.restrictScalars (algebraMap CoordinateRing SectionRing)).obj Native
  let comparison : (modulesSpecToSheaf.obj (tilde modules)).presheaf.obj
      (op (basicOpen denominator)) ≃ₗ[CoordinateRing] Restricted :=
    { toFun := fun vector => vector
      invFun := fun vector => vector
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact IsLocalizedModule.of_linearEquiv (.powers denominator)
    (AlgebraicGeometry.tilde.toOpen modules (basicOpen denominator)).hom comparison

noncomputable def tildeBasicOpenBasis (denominator : CoordinateRing) :
    Basis (Fin dimension) Γ(Spec CoordinateRing, basicOpen denominator)
      ((tilde modules).val.obj (op (basicOpen denominator))) := by
  let SectionRing := Γ(Spec CoordinateRing, basicOpen denominator)
  let Native := (tilde modules).val.obj (op (basicOpen denominator))
  letI : Module CoordinateRing Native := Module.compHom Native (algebraMap CoordinateRing SectionRing)
  haveI : IsScalarTower CoordinateRing SectionRing Native :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let localization : modules →ₗ[CoordinateRing] Native :=
    (tildeToBasicOpen CoordinateRing modules denominator).hom
  haveI : IsLocalizedModule (.powers denominator) localization :=
    tildeToBasicOpen_isLocalized CoordinateRing modules denominator
  exact basis.ofIsLocalizedModule SectionRing (.powers denominator) localization

theorem tildeBasicOpenBasis_apply (denominator : CoordinateRing) (index : Fin dimension) :
    tildeBasicOpenBasis CoordinateRing modules basis denominator index =
      tildeToBasicOpen CoordinateRing modules denominator (basis index) := by
  let SectionRing := Γ(Spec CoordinateRing, basicOpen denominator)
  let Native := (tilde modules).val.obj (op (basicOpen denominator))
  let : Module CoordinateRing Native := Module.compHom Native (algebraMap CoordinateRing SectionRing)
  have : IsScalarTower CoordinateRing SectionRing Native :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let localization : modules →ₗ[CoordinateRing] Native :=
    (tildeToBasicOpen CoordinateRing modules denominator).hom
  have : IsLocalizedModule (.powers denominator) localization :=
    tildeToBasicOpen_isLocalized CoordinateRing modules denominator
  exact Basis.ofIsLocalizedModule_apply SectionRing (.powers denominator)
    localization basis index

theorem tildeToBasicOpen_res (denominator smallerDenominator : CoordinateRing)
    (restriction : basicOpen smallerDenominator ⟶ basicOpen denominator) (vector : modules) :
    (tilde modules).val.map restriction.op (tildeToBasicOpen CoordinateRing modules denominator vector) =
      tildeToBasicOpen CoordinateRing modules smallerDenominator vector := rfl

theorem tildeBasicOpenBasis_res (denominator smallerDenominator : CoordinateRing)
    (restriction : basicOpen smallerDenominator ⟶ basicOpen denominator) (index : Fin dimension) :
    (tilde modules).val.map restriction.op
        (tildeBasicOpenBasis CoordinateRing modules basis denominator index) =
      tildeBasicOpenBasis CoordinateRing modules basis smallerDenominator index := by
  exact (congrArg (fun vector => (tilde modules).val.map restriction.op vector)
    (tildeBasicOpenBasis_apply CoordinateRing modules basis denominator index)).trans
      ((tildeToBasicOpen_res CoordinateRing modules denominator smallerDenominator restriction
        (basis index)).trans
          (tildeBasicOpenBasis_apply CoordinateRing modules basis smallerDenominator index).symm)

noncomputable def basicOpenTopSectionEquiv (denominator : CoordinateRing) :
    ↥(⋀[Γ(Spec CoordinateRing, basicOpen denominator)]^dimension
      ((tilde modules).val.obj (op (basicOpen denominator)))) ≃ₗ[
        Γ(Spec CoordinateRing, basicOpen denominator)]
          Γ(Spec CoordinateRing, basicOpen denominator) :=
  TopExterior.trivialization (tildeBasicOpenBasis CoordinateRing modules basis denominator)

theorem basicOpenTopSectionEquiv_frame (denominator : CoordinateRing) :
    basicOpenTopSectionEquiv CoordinateRing modules basis denominator
        (exteriorPower.ιMulti Γ(Spec CoordinateRing, basicOpen denominator) dimension
          (tildeBasicOpenBasis CoordinateRing modules basis denominator)) = 1 :=
  TopExterior.trivialization_frame _

theorem basicOpenTopSectionEquiv_symm (denominator : CoordinateRing)
    (scalar : Γ(Spec CoordinateRing, basicOpen denominator)) :
    (basicOpenTopSectionEquiv CoordinateRing modules basis denominator).symm scalar =
      scalar • exteriorPower.ιMulti Γ(Spec CoordinateRing, basicOpen denominator) dimension
        (tildeBasicOpenBasis CoordinateRing modules basis denominator) := rfl

theorem basicOpenTopFrame_res (denominator smallerDenominator : CoordinateRing)
    (restriction : basicOpen smallerDenominator ⟶ basicOpen denominator) :
    (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
      (tilde modules).val dimension).map restriction.op
        (exteriorPower.ιMulti
          (M := (tilde modules).val.obj (op (basicOpen denominator)))
          Γ(Spec CoordinateRing, basicOpen denominator) dimension
          (tildeBasicOpenBasis CoordinateRing modules basis denominator)) =
      exteriorPower.ιMulti
        (M := (tilde modules).val.obj (op (basicOpen smallerDenominator)))
        Γ(Spec CoordinateRing, basicOpen smallerDenominator) dimension
        (tildeBasicOpenBasis CoordinateRing modules basis smallerDenominator) := by
  have frameRestriction := exteriorPresheaf_map_wedge
    (Coefficients := (Spec CoordinateRing).presheaf) (tilde modules).val dimension restriction.op
      (tildeBasicOpenBasis CoordinateRing modules basis denominator)
  have restrictedBasis :
      (fun index => ((tilde modules).val.map restriction.op
        (tildeBasicOpenBasis CoordinateRing modules basis denominator index) :
          (tilde modules).val.obj (op (basicOpen smallerDenominator)))) =
      tildeBasicOpenBasis CoordinateRing modules basis smallerDenominator := by
    funext index
    exact tildeBasicOpenBasis_res CoordinateRing modules basis denominator smallerDenominator
      restriction index
  exact frameRestriction.trans
    (congrArg (exteriorPower.ιMulti
      (M := (tilde modules).val.obj (op (basicOpen smallerDenominator)))
      Γ(Spec CoordinateRing, basicOpen smallerDenominator) dimension)
      restrictedBasis)

end BondalThomsen.CanonicalTopExterior
