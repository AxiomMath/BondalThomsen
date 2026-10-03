module

public import BondalThomsen.Toric.Canonical.TopExteriorComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace PrimeSpectrum

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CanonicalExteriorDescent

noncomputable def singletonSectionEquiv (SectionRing : CommRingCat)
    (sections : Type) [AddCommGroup sections] [Module SectionRing sections]
    (frame : Basis (Fin 1) SectionRing sections) :
    sections ≃ₗ[SectionRing] SectionRing :=
  frame.equivFun.trans (LinearEquiv.funUnique (Fin 1) SectionRing SectionRing)

theorem singletonSectionEquiv_symm (SectionRing : CommRingCat)
    (sections : Type) [AddCommGroup sections] [Module SectionRing sections]
    (frame : Basis (Fin 1) SectionRing sections)
    (scalar : SectionRing) :
    (singletonSectionEquiv SectionRing sections frame).symm scalar = scalar • frame 0 := by
  change frame.equivFun.symm (fun _ => scalar) = _
  rw [Basis.equivFun_symm_apply, Fintype.sum_unique]
  rfl

theorem sheafificationUnit_ext (SchemeModel : Scheme)
    (source : SchemeModel.PresheafOfModules) (target : SchemeModel.Modules)
    (first second : (PresheafOfModules.sheafification
      (𝟙 SchemeModel.ringCatSheaf.obj)).obj source ⟶ target)
    (agrees : (PresheafOfModules.sheafificationAdjunction
        (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app source ≫ first.val =
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 SchemeModel.ringCatSheaf.obj)).unit.app source ≫ second.val) :
    first = second := by
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 SchemeModel.ringCatSheaf.obj)).homEquiv source target).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact agrees

theorem sheafification_hom_inv_of_basis (CoordinateRing : CommRingCat)
    (source : (Spec CoordinateRing).PresheafOfModules)
    (target : (Spec CoordinateRing).Modules)
    (basisIso : (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙ source.presheaf ≅
      (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙ target.val.presheaf)
    (forward : (PresheafOfModules.sheafification
      (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).obj source ⟶ target)
    (inverse : target ⟶ (PresheafOfModules.sheafification
      (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).obj source)
    (forwardBasis : ∀ (denominator : CoordinateRing)
      (vector : source.obj (op (basicOpen denominator))),
      forward.val.app (op (basicOpen denominator))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).unit.app source).app
              (op (basicOpen denominator)) vector) =
        basisIso.hom.app (op denominator) vector)
    (inverseBasis : ∀ (denominator : CoordinateRing)
      (vector : target.val.obj (op (basicOpen denominator))),
      inverse.val.app (op (basicOpen denominator)) vector =
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).unit.app source).app
            (op (basicOpen denominator)) (basisIso.inv.app (op denominator) vector)) :
    forward ≫ inverse = 𝟙 _ := by
  apply sheafificationUnit_ext
  apply CotangentTilde.basisModuleHom_ext CoordinateRing
  intro denominator vector
  let unit := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).unit.app source
  change inverse.val.app (op (basicOpen denominator))
      (forward.val.app (op (basicOpen denominator)) (unit.app (op (basicOpen denominator)) vector)) =
    unit.app (op (basicOpen denominator)) vector
  rw [forwardBasis, inverseBasis]
  exact congrArg (fun vectorSection => unit.app (op (basicOpen denominator)) vectorSection)
    (Iso.hom_inv_id_apply (basisIso.app (op denominator)) vector)

theorem sheafification_inv_hom_of_basis (CoordinateRing : CommRingCat)
    (source : (Spec CoordinateRing).PresheafOfModules)
    (target : (Spec CoordinateRing).Modules)
    (basisIso : (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙ source.presheaf ≅
      (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙ target.val.presheaf)
    (forward : (PresheafOfModules.sheafification
      (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).obj source ⟶ target)
    (inverse : target ⟶ (PresheafOfModules.sheafification
      (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).obj source)
    (forwardBasis : ∀ (denominator : CoordinateRing)
      (vector : source.obj (op (basicOpen denominator))),
      forward.val.app (op (basicOpen denominator))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).unit.app source).app
              (op (basicOpen denominator)) vector) =
        basisIso.hom.app (op denominator) vector)
    (inverseBasis : ∀ (denominator : CoordinateRing)
      (vector : target.val.obj (op (basicOpen denominator))),
      inverse.val.app (op (basicOpen denominator)) vector =
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).unit.app source).app
            (op (basicOpen denominator)) (basisIso.inv.app (op denominator) vector)) :
    inverse ≫ forward = 𝟙 target := by
  apply SheafOfModules.hom_ext
  apply CotangentTilde.basisModuleHom_ext CoordinateRing
  intro denominator vector
  change forward.val.app (op (basicOpen denominator))
      (inverse.val.app (op (basicOpen denominator)) vector) = vector
  rw [inverseBasis, forwardBasis]
  exact Iso.inv_hom_id_apply (basisIso.app (op denominator)) vector

variable (CoordinateRing : CommRingCat) (modules : ModuleCat.{0} CoordinateRing)
    {dimension : ℕ} (basis : Basis (Fin dimension) CoordinateRing modules)

noncomputable def topExteriorModule : ModuleCat CoordinateRing :=
  ModuleCat.of CoordinateRing ↥(⋀[CoordinateRing]^dimension modules)

noncomputable def topExteriorBasis :
    Basis (Fin 1) CoordinateRing (topExteriorModule CoordinateRing modules (dimension := dimension)) :=
  (Basis.singleton (Fin 1) CoordinateRing).map (TopExterior.trivialization basis).symm

theorem topExteriorBasis_apply :
    topExteriorBasis CoordinateRing modules basis 0 =
      exteriorPower.ιMulti CoordinateRing dimension basis := by
  rw [topExteriorBasis, Basis.map_apply, Basis.singleton_apply]
  change (1 : CoordinateRing) • exteriorPower.ιMulti CoordinateRing dimension basis = _
  exact one_smul _ _

noncomputable def tildeTopBasis (denominator : CoordinateRing) :
    Basis (Fin 1) Γ(Spec CoordinateRing, basicOpen denominator)
      ((tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val.obj
        (op (basicOpen denominator))) :=
  CanonicalTopExterior.tildeBasicOpenBasis CoordinateRing
    (topExteriorModule CoordinateRing modules (dimension := dimension))
    (topExteriorBasis CoordinateRing modules basis) denominator

theorem tildeTopBasis_res (denominator smallerDenominator : CoordinateRing)
    (restriction : basicOpen smallerDenominator ⟶ basicOpen denominator) :
    (tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val.map restriction.op
        (tildeTopBasis CoordinateRing modules basis denominator 0) =
      tildeTopBasis CoordinateRing modules basis smallerDenominator 0 :=
  CanonicalTopExterior.tildeBasicOpenBasis_res CoordinateRing
    (topExteriorModule CoordinateRing modules (dimension := dimension))
    (topExteriorBasis CoordinateRing modules basis) denominator smallerDenominator restriction 0

noncomputable def basicOpenTopEquiv (denominator : CoordinateRing) :
    ↥(⋀[Γ(Spec CoordinateRing, basicOpen denominator)]^dimension
      ((tilde modules).val.obj (op (basicOpen denominator)))) ≃ₗ[
        Γ(Spec CoordinateRing, basicOpen denominator)]
      ((tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val.obj
        (op (basicOpen denominator))) := by
  let SectionRing := Γ(Spec CoordinateRing, basicOpen denominator)
  let Native := (tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val.obj
    (op (basicOpen denominator))
  letI : Module SectionRing Native := Native.isModule
  let sourceEquiv :
      ↥(⋀[SectionRing]^dimension ((tilde modules).val.obj (op (basicOpen denominator)))) ≃ₗ[
        SectionRing] SectionRing :=
    TopExterior.trivialization
      (CanonicalTopExterior.tildeBasicOpenBasis CoordinateRing modules basis denominator)
  let targetEquiv : Native ≃ₗ[SectionRing] SectionRing :=
    singletonSectionEquiv SectionRing Native (tildeTopBasis CoordinateRing modules basis denominator)
  exact sourceEquiv.trans targetEquiv.symm

theorem basicOpenTopEquiv_apply (denominator : CoordinateRing)
    (vector : ↥(⋀[Γ(Spec CoordinateRing, basicOpen denominator)]^dimension
      ((tilde modules).val.obj (op (basicOpen denominator))))) :
    basicOpenTopEquiv CoordinateRing modules basis denominator vector =
      CanonicalTopExterior.basicOpenTopSectionEquiv CoordinateRing modules basis denominator vector •
        tildeTopBasis CoordinateRing modules basis denominator 0 :=
  singletonSectionEquiv_symm _ _ _ _

theorem basicOpenTopEquiv_frame (denominator : CoordinateRing) :
    basicOpenTopEquiv CoordinateRing modules basis denominator
        (exteriorPower.ιMulti Γ(Spec CoordinateRing, basicOpen denominator) dimension
          (CanonicalTopExterior.tildeBasicOpenBasis CoordinateRing modules basis denominator)) =
      tildeTopBasis CoordinateRing modules basis denominator 0 := by
  rw [basicOpenTopEquiv_apply, CanonicalTopExterior.basicOpenTopSectionEquiv_frame, one_smul]

theorem basicOpenTopCoordinate_res (denominator smallerDenominator : CoordinateRing)
    (restriction : basicOpen smallerDenominator ⟶ basicOpen denominator)
    (vector : ↥(⋀[Γ(Spec CoordinateRing, basicOpen denominator)]^dimension
      ((tilde modules).val.obj (op (basicOpen denominator))))) :
    CanonicalTopExterior.basicOpenTopSectionEquiv CoordinateRing modules basis smallerDenominator
        ((exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
          (tilde modules).val dimension).map restriction.op vector) =
      (Spec CoordinateRing).presheaf.map restriction.op
        (CanonicalTopExterior.basicOpenTopSectionEquiv CoordinateRing modules basis denominator
          vector) := by
  obtain ⟨scalar, rfl⟩ :=
    (CanonicalTopExterior.basicOpenTopSectionEquiv CoordinateRing modules basis denominator).symm.surjective
      vector
  rw [CanonicalTopExterior.basicOpenTopSectionEquiv_symm]
  rw [PresheafOfModules.map_smul,
    CanonicalTopExterior.basicOpenTopFrame_res CoordinateRing modules basis denominator
      smallerDenominator restriction]
  change CanonicalTopExterior.basicOpenTopSectionEquiv CoordinateRing modules basis smallerDenominator
      (((Spec CoordinateRing).presheaf.map restriction.op scalar) •
        exteriorPower.ιMulti Γ(Spec CoordinateRing, basicOpen smallerDenominator) dimension
          (CanonicalTopExterior.tildeBasicOpenBasis CoordinateRing modules basis smallerDenominator)) = _
  rw [map_smul, map_smul,
    CanonicalTopExterior.basicOpenTopSectionEquiv_frame,
    CanonicalTopExterior.basicOpenTopSectionEquiv_frame]
  simp only [smul_eq_mul, mul_one]

theorem basicOpenTopEquiv_res (denominator smallerDenominator : CoordinateRing)
    (restriction : basicOpen smallerDenominator ⟶ basicOpen denominator)
    (vector : ↥(⋀[Γ(Spec CoordinateRing, basicOpen denominator)]^dimension
      ((tilde modules).val.obj (op (basicOpen denominator))))) :
    basicOpenTopEquiv CoordinateRing modules basis smallerDenominator
        ((exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
          (tilde modules).val dimension).map restriction.op vector) =
      (tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val.map restriction.op
        (basicOpenTopEquiv CoordinateRing modules basis denominator vector) := by
  rw [basicOpenTopEquiv_apply, basicOpenTopEquiv_apply,
    PresheafOfModules.map_smul,
    tildeTopBasis_res CoordinateRing modules basis denominator smallerDenominator restriction,
    basicOpenTopCoordinate_res CoordinateRing modules basis denominator smallerDenominator restriction]
  rfl

noncomputable def basisTopAdditiveIso :
    (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙
        (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
          (tilde modules).val dimension).presheaf ≅
      (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙
        (tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val.presheaf :=
  NatIso.ofComponents
    (fun domain => (basicOpenTopEquiv CoordinateRing modules basis domain.unop).toAddEquiv.toAddCommGrpIso)
    (by
      intro domain smaller restriction
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro vector
      exact basicOpenTopEquiv_res CoordinateRing modules basis domain.unop smaller.unop
        restriction.unop.hom vector)

theorem basisTopAdditiveIso_hom_smul (denominator : CoordinateRing)
    (scalar : Γ(Spec CoordinateRing, basicOpen denominator))
    (vector : ↥(⋀[Γ(Spec CoordinateRing, basicOpen denominator)]^dimension
      ((tilde modules).val.obj (op (basicOpen denominator))))) :
    (basisTopAdditiveIso CoordinateRing modules basis).hom.app (op denominator) (scalar • vector) =
      @SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
        ((tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val.obj
          (op (basicOpen denominator))) inferInstance scalar
        ((basisTopAdditiveIso CoordinateRing modules basis).hom.app (op denominator) vector) :=
  (basicOpenTopEquiv CoordinateRing modules basis denominator).map_smul scalar vector

theorem basisTopAdditiveIso_inv_smul (denominator : CoordinateRing)
    (scalar : Γ(Spec CoordinateRing, basicOpen denominator))
    (vector : (tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val.obj
      (op (basicOpen denominator))) :
    (basisTopAdditiveIso CoordinateRing modules basis).inv.app (op denominator) (scalar • vector) =
      @SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
        ((exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
          (tilde modules).val dimension).obj (op (basicOpen denominator))) inferInstance scalar
        ((basisTopAdditiveIso CoordinateRing modules basis).inv.app (op denominator) vector) :=
  (basicOpenTopEquiv CoordinateRing modules basis denominator).symm.map_smul scalar vector

noncomputable def exteriorPresheafToTilde :
    exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
        (tilde modules).val dimension ⟶
      (tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val :=
  CotangentTilde.extendBasisModuleHom CoordinateRing
    (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
      (tilde modules).val dimension)
    (tilde (topExteriorModule CoordinateRing modules (dimension := dimension)))
    (basisTopAdditiveIso CoordinateRing modules basis).hom
    (basisTopAdditiveIso_hom_smul CoordinateRing modules basis)

noncomputable def exteriorUnit :
    exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
        (tilde modules).val dimension ⟶
      (exteriorSheaf (tilde modules) dimension).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).unit.app
      (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
        (tilde modules).val dimension)

noncomputable def tildeToExteriorSheaf :
    tilde (topExteriorModule CoordinateRing modules (dimension := dimension)) ⟶
      exteriorSheaf (tilde modules) dimension :=
  ⟨CotangentTilde.extendBasisModuleHom CoordinateRing
    (tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val
    (exteriorSheaf (tilde modules) dimension)
    ((basisTopAdditiveIso CoordinateRing modules basis).inv ≫
      Functor.whiskerLeft (CanonicalAffine.basicOpenFunctor CoordinateRing).op
        ((PresheafOfModules.toPresheaf (Spec CoordinateRing).ringCatSheaf.obj).map
          (exteriorUnit CoordinateRing modules (dimension := dimension))))
    (by
      intro denominator scalar vector
      change (exteriorUnit CoordinateRing modules (dimension := dimension)).app
          (op (basicOpen denominator))
          ((basisTopAdditiveIso CoordinateRing modules basis).inv.app
            (op denominator) (scalar • vector)) = _
      rw [basisTopAdditiveIso_inv_smul]
      exact (exteriorUnit CoordinateRing modules (dimension := dimension)).app
        (op (basicOpen denominator)) |>.hom.map_smul scalar _)⟩

noncomputable def exteriorSheafToTilde :
    exteriorSheaf (tilde modules) dimension ⟶
      tilde (topExteriorModule CoordinateRing modules (dimension := dimension)) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).symm
      (exteriorPresheafToTilde CoordinateRing modules basis)

theorem exteriorSheafToTilde_unit :
    exteriorUnit CoordinateRing modules (dimension := dimension) ≫
        (exteriorSheafToTilde CoordinateRing modules basis).val =
      exteriorPresheafToTilde CoordinateRing modules basis := by
  apply (PresheafOfModules.toPresheaf (Spec CoordinateRing).ringCatSheaf.obj).map_injective
  change CategoryTheory.toSheafify (Opens.grothendieckTopology (Spec CoordinateRing))
      (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
        (tilde modules).val dimension).presheaf ≫
        (PresheafOfModules.toPresheaf (Spec CoordinateRing).ringCatSheaf.obj).map
          (exteriorSheafToTilde CoordinateRing modules basis).val = _
  rw [← PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  exact congrArg
    ((PresheafOfModules.toPresheaf (Spec CoordinateRing).ringCatSheaf.obj).map)
    ((PresheafOfModules.sheafificationHomEquiv
      (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)
      (P := exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
        (tilde modules).val dimension)
      (F := tilde (topExteriorModule CoordinateRing modules (dimension := dimension)))).apply_symm_apply
        (exteriorPresheafToTilde CoordinateRing modules basis))

theorem exteriorSheafToTilde_unit_app (denominator : CoordinateRing)
    (vector : ↥(⋀[Γ(Spec CoordinateRing, basicOpen denominator)]^dimension
      ((tilde modules).val.obj (op (basicOpen denominator))))) :
    (exteriorSheafToTilde CoordinateRing modules basis).val.app (op (basicOpen denominator))
        ((exteriorUnit CoordinateRing modules (dimension := dimension)).app
          (op (basicOpen denominator)) vector) =
      (basisTopAdditiveIso CoordinateRing modules basis).hom.app (op denominator) vector :=
  (congrArg (fun comparison => comparison.app (op (basicOpen denominator)) vector)
    (exteriorSheafToTilde_unit CoordinateRing modules basis)).trans
      (CotangentTilde.extendBasisModuleHom_app CoordinateRing
        (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
          (tilde modules).val dimension)
        (tilde (topExteriorModule CoordinateRing modules (dimension := dimension)))
        (basisTopAdditiveIso CoordinateRing modules basis).hom
        (basisTopAdditiveIso_hom_smul CoordinateRing modules basis) denominator vector)

theorem tildeToExteriorSheaf_app (denominator : CoordinateRing)
    (vector : (tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val.obj
      (op (basicOpen denominator))) :
    (tildeToExteriorSheaf CoordinateRing modules basis).val.app (op (basicOpen denominator)) vector =
      (exteriorUnit CoordinateRing modules (dimension := dimension)).app (op (basicOpen denominator))
        ((basisTopAdditiveIso CoordinateRing modules basis).inv.app (op denominator) vector) :=
  CotangentTilde.extendBasisModuleHom_app CoordinateRing
    (tilde (topExteriorModule CoordinateRing modules (dimension := dimension))).val
    (exteriorSheaf (tilde modules) dimension)
    ((basisTopAdditiveIso CoordinateRing modules basis).inv ≫
      Functor.whiskerLeft (CanonicalAffine.basicOpenFunctor CoordinateRing).op
        ((PresheafOfModules.toPresheaf (Spec CoordinateRing).ringCatSheaf.obj).map
          (exteriorUnit CoordinateRing modules (dimension := dimension))))
    (by
      intro denominator scalar vector
      change (exteriorUnit CoordinateRing modules (dimension := dimension)).app
          (op (basicOpen denominator))
          ((basisTopAdditiveIso CoordinateRing modules basis).inv.app
            (op denominator) (scalar • vector)) = _
      rw [basisTopAdditiveIso_inv_smul]
      exact (exteriorUnit CoordinateRing modules (dimension := dimension)).app
        (op (basicOpen denominator)) |>.hom.map_smul scalar _) denominator vector

theorem exteriorSheafToTilde_hom_inv_id :
    exteriorSheafToTilde CoordinateRing modules basis ≫
        tildeToExteriorSheaf CoordinateRing modules basis =
      𝟙 (exteriorSheaf (tilde modules) dimension) := by
  exact sheafification_hom_inv_of_basis CoordinateRing
    (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
      (tilde modules).val dimension)
    (tilde (topExteriorModule CoordinateRing modules (dimension := dimension)))
    (basisTopAdditiveIso CoordinateRing modules basis)
    (exteriorSheafToTilde CoordinateRing modules basis)
    (tildeToExteriorSheaf CoordinateRing modules basis)
    (exteriorSheafToTilde_unit_app CoordinateRing modules basis)
    (tildeToExteriorSheaf_app CoordinateRing modules basis)

theorem exteriorSheafToTilde_inv_hom_id :
    tildeToExteriorSheaf CoordinateRing modules basis ≫
        exteriorSheafToTilde CoordinateRing modules basis =
      𝟙 (tilde (topExteriorModule CoordinateRing modules (dimension := dimension))) := by
  exact sheafification_inv_hom_of_basis CoordinateRing
    (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := (Spec CoordinateRing).presheaf)
      (tilde modules).val dimension)
    (tilde (topExteriorModule CoordinateRing modules (dimension := dimension)))
    (basisTopAdditiveIso CoordinateRing modules basis)
    (exteriorSheafToTilde CoordinateRing modules basis)
    (tildeToExteriorSheaf CoordinateRing modules basis)
    (exteriorSheafToTilde_unit_app CoordinateRing modules basis)
    (tildeToExteriorSheaf_app CoordinateRing modules basis)

noncomputable def exteriorSheafTildeIso :
    exteriorSheaf (tilde modules) dimension ≅
      tilde (topExteriorModule CoordinateRing modules (dimension := dimension)) where
  hom := exteriorSheafToTilde CoordinateRing modules basis
  inv := tildeToExteriorSheaf CoordinateRing modules basis
  hom_inv_id := exteriorSheafToTilde_hom_inv_id CoordinateRing modules basis
  inv_hom_id := exteriorSheafToTilde_inv_hom_id CoordinateRing modules basis

end BondalThomsen.CanonicalExteriorDescent

namespace BondalThomsen.CanonicalExteriorDescent

noncomputable def canonicalExteriorSpecTildeIso (Base CoordinateRing : CommRingCat)
    [Algebra Base CoordinateRing] {dimension : ℕ}
    (basis : Basis (Fin dimension) CoordinateRing (KaehlerDifferential Base CoordinateRing)) :
    canonicalExteriorSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) dimension ≅
      tilde (topExteriorModule CoordinateRing
        (CanonicalAffine.differentialModule Base CoordinateRing) (dimension := dimension)) :=
  (CanonicalTopExterior.canonicalExteriorSpecIso Base CoordinateRing dimension).trans
    (exteriorSheafTildeIso CoordinateRing (CanonicalAffine.differentialModule Base CoordinateRing) basis)

end BondalThomsen.CanonicalExteriorDescent

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

noncomputable def basisConeCanonicalExteriorTildeIso (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) :
    let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    BondalThomsen.canonicalExteriorSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 CoordinateRing))) dimension ≅
      tilde (BondalThomsen.CanonicalExteriorDescent.topExteriorModule CoordinateRing
        (BondalThomsen.CanonicalAffine.differentialModule (CommRingCat.of 𝕜) CoordinateRing)
        (dimension := dimension)) :=
  BondalThomsen.CanonicalExteriorDescent.canonicalExteriorSpecTildeIso (CommRingCat.of 𝕜) _
    (fan.basisConeDifferentialBasis 𝕜 basis)

end TauCeti.Toric.Fan
