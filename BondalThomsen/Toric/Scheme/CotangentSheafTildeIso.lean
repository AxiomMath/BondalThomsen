module

public import BondalThomsen.Toric.Canonical.AffineComparison
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace
open PrimeSpectrum

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace BondalThomsen.CotangentTilde

universe coefficientUniverse

variable (CoordinateRing : CommRingCat.{coefficientUniverse})

instance basicOpenFunctor_full : (CanonicalAffine.basicOpenFunctor CoordinateRing).Full :=
  InducedCategory.full _

noncomputable def extendBasisModuleHom
    (source : (Spec CoordinateRing).PresheafOfModules)
    (target : (Spec CoordinateRing).Modules)
    (basisMap : (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙ source.presheaf ⟶
      (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙ target.val.presheaf)
    (basisLinear : ∀ (denominator : CoordinateRing)
      (scalar : Γ(Spec CoordinateRing, basicOpen denominator))
      (vector : source.obj (op (basicOpen denominator))),
      basisMap.app (op denominator) (scalar • vector) =
        @SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
          (target.val.obj (op (basicOpen denominator))) inferInstance scalar
          (basisMap.app (op denominator) vector)) : source ⟶ target.val := by
  let extension : source.presheaf ⟶ target.val.presheaf :=
    Functor.IsCoverDense.sheafHom
      (G := CanonicalAffine.basicOpenFunctor CoordinateRing)
      (ℱ' := (SheafOfModules.toSheaf (Spec CoordinateRing).ringCatSheaf).obj target) basisMap
  have onBasis : ∀ denominator : CoordinateRing,
      extension.app (op (basicOpen denominator)) = basisMap.app (op denominator) := by
    intro denominator
    exact NatTrans.congr_app
      (Functor.IsCoverDense.sheafHom_restrict_eq
        (G := CanonicalAffine.basicOpenFunctor CoordinateRing)
        (ℱ' := (SheafOfModules.toSheaf (Spec CoordinateRing).ringCatSheaf).obj target)
        basisMap) (op denominator)
  exact PresheafOfModules.homMk extension (by
    intro domain scalar vector
    apply TopCat.Presheaf.IsSheaf.section_ext target.isSheaf
    intro point contains
    obtain ⟨basisOpen, ⟨denominator, rfl⟩, containsBasis, contained⟩ :=
      (Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) contains
    refine ⟨basicOpen denominator, contained, containsBasis, ?_⟩
    have naturality (vectorSection : source.obj domain) :=
      ConcreteCategory.congr_hom (extension.naturality (homOfLE contained).op) vectorSection
    calc
      _ = extension.app (op (basicOpen denominator))
          (source.map (homOfLE contained).op (scalar • vector)) := (naturality _).symm
      _ = basisMap.app (op denominator)
          (@SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
            (source.obj (op (basicOpen denominator))) inferInstance
            ((Spec CoordinateRing).presheaf.map (homOfLE contained).op scalar)
            (source.map (homOfLE contained).op vector)) := by
        rw [onBasis]
        exact congrArg (fun vectorSection => basisMap.app (op denominator) vectorSection)
          (source.map_smul (homOfLE contained).op scalar vector)
      _ = @SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
          (target.val.obj (op (basicOpen denominator))) inferInstance
          ((Spec CoordinateRing).presheaf.map (homOfLE contained).op scalar)
          (basisMap.app (op denominator) (source.map (homOfLE contained).op vector)) :=
        basisLinear denominator _ _
      _ = @SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
          (target.val.obj (op (basicOpen denominator))) inferInstance
          ((Spec CoordinateRing).presheaf.map (homOfLE contained).op scalar)
          (target.val.map (homOfLE contained).op (extension.app domain vector)) := by
        rw [← onBasis]
        exact congrArg (fun vectorSection =>
          (Spec CoordinateRing).presheaf.map (homOfLE contained).op scalar •
            (vectorSection : target.val.obj (op (basicOpen denominator))))
          (naturality vector)
      _ = _ := (target.val.map_smul (homOfLE contained).op scalar
        (extension.app domain vector)).symm)

theorem extendBasisModuleHom_app
    (source : (Spec CoordinateRing).PresheafOfModules)
    (target : (Spec CoordinateRing).Modules)
    (basisMap : (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙ source.presheaf ⟶
      (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙ target.val.presheaf)
    (basisLinear : ∀ (denominator : CoordinateRing)
      (scalar : Γ(Spec CoordinateRing, basicOpen denominator))
      (vector : source.obj (op (basicOpen denominator))),
      basisMap.app (op denominator) (scalar • vector) =
        @SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
          (target.val.obj (op (basicOpen denominator))) inferInstance scalar
          (basisMap.app (op denominator) vector))
    (denominator : CoordinateRing) (vector : source.obj (op (basicOpen denominator))) :
    (extendBasisModuleHom CoordinateRing source target basisMap basisLinear).app
        (op (basicOpen denominator)) vector = basisMap.app (op denominator) vector := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (Functor.IsCoverDense.sheafHom_restrict_eq
        (G := CanonicalAffine.basicOpenFunctor CoordinateRing)
        (ℱ' := (SheafOfModules.toSheaf (Spec CoordinateRing).ringCatSheaf).obj target) basisMap)
      (op denominator)) vector

end BondalThomsen.CotangentTilde

namespace BondalThomsen.CotangentTilde

universe coefficientUniverse

noncomputable def differentialBaseIso
    {FirstBase SecondBase SectionRing : CommRingCat.{coefficientUniverse}}
    (first : FirstBase ⟶ SectionRing) (second : SecondBase ⟶ SectionRing)
    (coefficients : FirstBase ≅ SecondBase) (compatible : coefficients.hom ≫ second = first) :
    CommRingCat.KaehlerDifferential first ≅ CommRingCat.KaehlerDifferential second := by
  let forwardDerivation : (CommRingCat.KaehlerDifferential second).Derivation first :=
    ModuleCat.Derivation.mk
      (fun regularFunction => CommRingCat.KaehlerDifferential.d (f := second) regularFunction)
      (fun _ _ => (CommRingCat.KaehlerDifferential.D second).d_add _ _)
      (fun _ _ => (CommRingCat.KaehlerDifferential.D second).d_mul _ _)
      (fun scalar => by
        have evaluates := ConcreteCategory.congr_hom compatible scalar
        change CommRingCat.KaehlerDifferential.d (f := second) (first scalar) = 0
        exact (congrArg (CommRingCat.KaehlerDifferential.d (f := second)) evaluates.symm).trans
          ((CommRingCat.KaehlerDifferential.D second).d_map (coefficients.hom scalar)))
  have compatibleInverse : coefficients.inv ≫ first = second := by
    rw [← compatible]
    simp
  let backwardDerivation : (CommRingCat.KaehlerDifferential first).Derivation second :=
    ModuleCat.Derivation.mk
      (fun regularFunction => CommRingCat.KaehlerDifferential.d (f := first) regularFunction)
      (fun _ _ => (CommRingCat.KaehlerDifferential.D first).d_add _ _)
      (fun _ _ => (CommRingCat.KaehlerDifferential.D first).d_mul _ _)
      (fun scalar => by
        have evaluates := ConcreteCategory.congr_hom compatibleInverse scalar
        change CommRingCat.KaehlerDifferential.d (f := first) (second scalar) = 0
        exact (congrArg (CommRingCat.KaehlerDifferential.d (f := first)) evaluates.symm).trans
          ((CommRingCat.KaehlerDifferential.D first).d_map (coefficients.inv scalar)))
  exact
    { hom := forwardDerivation.desc
      inv := backwardDerivation.desc
      hom_inv_id := by
        apply CommRingCat.KaehlerDifferential.ext
        intro regularFunction
        change backwardDerivation.desc
          (forwardDerivation.desc (CommRingCat.KaehlerDifferential.d regularFunction)) = _
        rw [ModuleCat.Derivation.desc_d]
        change backwardDerivation.desc
          (CommRingCat.KaehlerDifferential.d (f := second) regularFunction) =
            CommRingCat.KaehlerDifferential.d (f := first) regularFunction
        exact ModuleCat.Derivation.desc_d backwardDerivation regularFunction
      inv_hom_id := by
        apply CommRingCat.KaehlerDifferential.ext
        intro regularFunction
        change forwardDerivation.desc
          (backwardDerivation.desc (CommRingCat.KaehlerDifferential.d regularFunction)) = _
        rw [ModuleCat.Derivation.desc_d]
        change forwardDerivation.desc
          (CommRingCat.KaehlerDifferential.d (f := first) regularFunction) =
            CommRingCat.KaehlerDifferential.d (f := second) regularFunction
        exact ModuleCat.Derivation.desc_d forwardDerivation regularFunction }

theorem differentialBaseIso_d
    {FirstBase SecondBase SectionRing : CommRingCat.{coefficientUniverse}}
    (first : FirstBase ⟶ SectionRing) (second : SecondBase ⟶ SectionRing)
    (coefficients : FirstBase ≅ SecondBase) (compatible : coefficients.hom ≫ second = first)
    (regularFunction : SectionRing) :
    (differentialBaseIso first second coefficients compatible).hom
        (CommRingCat.KaehlerDifferential.d regularFunction) =
      CommRingCat.KaehlerDifferential.d regularFunction := by
  dsimp only [differentialBaseIso]
  exact ModuleCat.Derivation.desc_d _ regularFunction

theorem cotangentCoefficientMap_spec
    (Base CoordinateRing : CommRingCat.{coefficientUniverse}) [Algebra Base CoordinateRing]
    (domain : (Spec CoordinateRing).Opensᵒᵖ) :
    (Scheme.ΓSpecIso Base).hom ≫
        (CanonicalAffine.sectionCoefficientMap Base CoordinateRing).app domain =
      (cotangentCoefficientMap
        (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))).app domain := by
  let structureMap := Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))
  have restricts : structureMap.appTop ≫
      (Spec CoordinateRing).presheaf.map (homOfLE (show domain.unop ≤ ⊤ from le_top)).op =
      structureMap.appLE ⊤ domain.unop (by simp) :=
    structureMap.appLE_map (by simp) (homOfLE le_top).op
  have constants : (Scheme.ΓSpecIso Base).inv ≫
      (cotangentCoefficientMap structureMap).app domain =
      (CanonicalAffine.sectionCoefficientMap Base CoordinateRing).app domain := by
    change (Scheme.ΓSpecIso Base).inv ≫ structureMap.appLE ⊤ domain.unop (by simp) = _
    rw [← restricts, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Scheme.ΓSpecIso_inv]
    rfl
  rw [← constants]
  simp
  rfl

end BondalThomsen.CotangentTilde

namespace BondalThomsen.CotangentTilde

universe coefficientUniverse

theorem basisModuleHom_ext (CoordinateRing : CommRingCat.{coefficientUniverse})
    {source : (Spec CoordinateRing).PresheafOfModules}
    {target : (Spec CoordinateRing).Modules} {first second : source ⟶ target.val}
    (agrees : ∀ (denominator : CoordinateRing)
      (vector : source.obj (op (basicOpen denominator))),
      first.app (op (basicOpen denominator)) vector =
        second.app (op (basicOpen denominator)) vector) : first = second := by
  apply PresheafOfModules.hom_ext
  intro domain
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro vector
  apply TopCat.Presheaf.IsSheaf.section_ext target.isSheaf
  intro point contains
  obtain ⟨basisOpen, ⟨denominator, rfl⟩, containsBasis, contained⟩ :=
    (Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) contains
  refine ⟨basicOpen denominator, contained, containsBasis, ?_⟩
  exact (PresheafOfModules.naturality_apply first (homOfLE contained).op vector).symm.trans
    ((agrees denominator (source.map (homOfLE contained).op vector)).trans
      (PresheafOfModules.naturality_apply second (homOfLE contained).op vector))

end BondalThomsen.CotangentTilde

namespace BondalThomsen.CotangentTilde

universe coefficientUniverse

variable (Base CoordinateRing : CommRingCat.{coefficientUniverse}) [Algebra Base CoordinateRing]

noncomputable def basisDifferentialAdditiveIso :
    (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙
        (tilde (CanonicalAffine.differentialModule Base CoordinateRing)).val.presheaf ≅
      (CanonicalAffine.basicOpenFunctor CoordinateRing).op ⋙
        (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing).presheaf :=
  Functor.mapIso
    ((Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat CoordinateRing) AddCommGrpCat))
    (CanonicalAffine.basicOpenDifferentialPresheafIso Base CoordinateRing)

theorem basisDifferentialAdditiveIso_hom_smul (denominator : CoordinateRing)
    (scalar : Γ(Spec CoordinateRing, basicOpen denominator))
    (vector : (tilde (CanonicalAffine.differentialModule Base CoordinateRing)).val.obj
      (op (basicOpen denominator))) :
    (basisDifferentialAdditiveIso Base CoordinateRing).hom.app (op denominator) (scalar • vector) =
      @SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
        ((CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing).obj
          (op (basicOpen denominator))) inferInstance scalar
        ((basisDifferentialAdditiveIso Base CoordinateRing).hom.app (op denominator) vector) :=
  (CanonicalAffine.basicOpenDifferentialIso Base CoordinateRing denominator).hom.hom.map_smul
    scalar vector

theorem basisDifferentialAdditiveIso_inv_smul (denominator : CoordinateRing)
    (scalar : Γ(Spec CoordinateRing, basicOpen denominator))
    (vector : (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing).obj
      (op (basicOpen denominator))) :
    (basisDifferentialAdditiveIso Base CoordinateRing).inv.app (op denominator) (scalar • vector) =
      @SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
        ((tilde (CanonicalAffine.differentialModule Base CoordinateRing)).val.obj
          (op (basicOpen denominator))) inferInstance scalar
        ((basisDifferentialAdditiveIso Base CoordinateRing).inv.app (op denominator) vector) := by
  apply (CanonicalAffine.basicOpenDifferentialEquiv Base CoordinateRing denominator).injective
  change (basisDifferentialAdditiveIso Base CoordinateRing).hom.app (op denominator)
      ((basisDifferentialAdditiveIso Base CoordinateRing).inv.app (op denominator) (scalar • vector)) =
    (basisDifferentialAdditiveIso Base CoordinateRing).hom.app (op denominator)
      (@SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
        ((tilde (CanonicalAffine.differentialModule Base CoordinateRing)).val.obj
          (op (basicOpen denominator))) inferInstance scalar
        ((basisDifferentialAdditiveIso Base CoordinateRing).inv.app (op denominator) vector))
  calc
    _ = scalar • vector := Iso.inv_hom_id_apply
      ((basisDifferentialAdditiveIso Base CoordinateRing).app (op denominator)) _
    _ = @SMul.smul Γ(Spec CoordinateRing, basicOpen denominator)
        ((CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing).obj
          (op (basicOpen denominator))) inferInstance scalar
        ((basisDifferentialAdditiveIso Base CoordinateRing).hom.app (op denominator)
          ((basisDifferentialAdditiveIso Base CoordinateRing).inv.app (op denominator) vector)) :=
      congrArg (fun vectorSection => scalar • vectorSection)
        (Iso.inv_hom_id_apply ((basisDifferentialAdditiveIso Base CoordinateRing).app
          (op denominator)) vector).symm
    _ = _ := (basisDifferentialAdditiveIso_hom_smul Base CoordinateRing denominator scalar
      ((basisDifferentialAdditiveIso Base CoordinateRing).inv.app (op denominator) vector)).symm

noncomputable def affineDifferentialToTilde :
    CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing ⟶
      (tilde (CanonicalAffine.differentialModule Base CoordinateRing)).val :=
  extendBasisModuleHom CoordinateRing
    (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing)
    (tilde (CanonicalAffine.differentialModule Base CoordinateRing))
    (basisDifferentialAdditiveIso Base CoordinateRing).inv
    (basisDifferentialAdditiveIso_inv_smul Base CoordinateRing)

noncomputable def affineDifferentialSheaf : (Spec CoordinateRing).Modules :=
  (PresheafOfModules.sheafification (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).obj
    (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing)

noncomputable def affineDifferentialUnit :
    CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing ⟶
      (affineDifferentialSheaf Base CoordinateRing).val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).unit.app
      (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing)

noncomputable def tildeToAffineDifferentialSheaf :
    tilde (CanonicalAffine.differentialModule Base CoordinateRing) ⟶
      affineDifferentialSheaf Base CoordinateRing :=
  ⟨extendBasisModuleHom CoordinateRing
    (tilde (CanonicalAffine.differentialModule Base CoordinateRing)).val
    (affineDifferentialSheaf Base CoordinateRing)
    ((basisDifferentialAdditiveIso Base CoordinateRing).hom ≫
      Functor.whiskerLeft (CanonicalAffine.basicOpenFunctor CoordinateRing).op
        ((PresheafOfModules.toPresheaf (Spec CoordinateRing).ringCatSheaf.obj).map
          (affineDifferentialUnit Base CoordinateRing)))
    (by
      intro denominator scalar vector
      change (affineDifferentialUnit Base CoordinateRing).app (op (basicOpen denominator))
          ((basisDifferentialAdditiveIso Base CoordinateRing).hom.app
            (op denominator) (scalar • vector)) = _
      rw [basisDifferentialAdditiveIso_hom_smul]
      exact (affineDifferentialUnit Base CoordinateRing).app
        (op (basicOpen denominator)) |>.hom.map_smul scalar _)⟩

noncomputable def affineDifferentialSheafToTilde :
    affineDifferentialSheaf Base CoordinateRing ⟶
      tilde (CanonicalAffine.differentialModule Base CoordinateRing) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).symm
      (affineDifferentialToTilde Base CoordinateRing)

theorem affineDifferentialSheafToTilde_unit :
    affineDifferentialUnit Base CoordinateRing ≫
        (affineDifferentialSheafToTilde Base CoordinateRing).val =
      affineDifferentialToTilde Base CoordinateRing := by
  apply (PresheafOfModules.toPresheaf (Spec CoordinateRing).ringCatSheaf.obj).map_injective
  change CategoryTheory.toSheafify (Opens.grothendieckTopology (Spec CoordinateRing))
      (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing).presheaf ≫
        (PresheafOfModules.toPresheaf (Spec CoordinateRing).ringCatSheaf.obj).map
          (affineDifferentialSheafToTilde Base CoordinateRing).val = _
  rw [← PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  exact congrArg
    ((PresheafOfModules.toPresheaf (Spec CoordinateRing).ringCatSheaf.obj).map)
    ((PresheafOfModules.sheafificationHomEquiv
      (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)
      (P := CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing)
      (F := tilde (CanonicalAffine.differentialModule Base CoordinateRing))).apply_symm_apply
        (affineDifferentialToTilde Base CoordinateRing))

theorem affineDifferentialSheafToTilde_unit_app (denominator : CoordinateRing)
    (vector : (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing).obj
      (op (basicOpen denominator))) :
    (affineDifferentialSheafToTilde Base CoordinateRing).val.app (op (basicOpen denominator))
        ((affineDifferentialUnit Base CoordinateRing).app (op (basicOpen denominator)) vector) =
      (basisDifferentialAdditiveIso Base CoordinateRing).inv.app (op denominator) vector :=
  (ConcreteCategory.congr_hom
    (congrArg (fun morphism => morphism.app (op (basicOpen denominator)))
      (affineDifferentialSheafToTilde_unit Base CoordinateRing)) vector).trans
    (extendBasisModuleHom_app CoordinateRing
      (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing)
      (tilde (CanonicalAffine.differentialModule Base CoordinateRing))
      (basisDifferentialAdditiveIso Base CoordinateRing).inv
      (basisDifferentialAdditiveIso_inv_smul Base CoordinateRing) denominator vector)

theorem tildeToAffineDifferentialSheaf_app (denominator : CoordinateRing)
    (vector : (tilde (CanonicalAffine.differentialModule Base CoordinateRing)).val.obj
      (op (basicOpen denominator))) :
    (tildeToAffineDifferentialSheaf Base CoordinateRing).val.app
        (op (basicOpen denominator)) vector =
      (affineDifferentialUnit Base CoordinateRing).app (op (basicOpen denominator))
        ((basisDifferentialAdditiveIso Base CoordinateRing).hom.app (op denominator) vector) :=
  extendBasisModuleHom_app CoordinateRing
    (tilde (CanonicalAffine.differentialModule Base CoordinateRing)).val
    (affineDifferentialSheaf Base CoordinateRing)
    ((basisDifferentialAdditiveIso Base CoordinateRing).hom ≫
      Functor.whiskerLeft (CanonicalAffine.basicOpenFunctor CoordinateRing).op
        ((PresheafOfModules.toPresheaf (Spec CoordinateRing).ringCatSheaf.obj).map
          (affineDifferentialUnit Base CoordinateRing)))
    (by
      intro denominator scalar vector
      change (affineDifferentialUnit Base CoordinateRing).app (op (basicOpen denominator))
          ((basisDifferentialAdditiveIso Base CoordinateRing).hom.app
            (op denominator) (scalar • vector)) = _
      rw [basisDifferentialAdditiveIso_hom_smul]
      exact (affineDifferentialUnit Base CoordinateRing).app
        (op (basicOpen denominator)) |>.hom.map_smul scalar _) denominator vector

theorem affineDifferentialSheafToTilde_hom_inv_id :
    affineDifferentialSheafToTilde Base CoordinateRing ≫
        tildeToAffineDifferentialSheaf Base CoordinateRing =
      𝟙 (affineDifferentialSheaf Base CoordinateRing) := by
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).homEquiv
      (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing)
      (affineDifferentialSheaf Base CoordinateRing)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change affineDifferentialUnit Base CoordinateRing ≫
      (affineDifferentialSheafToTilde Base CoordinateRing ≫
        tildeToAffineDifferentialSheaf Base CoordinateRing).val =
    affineDifferentialUnit Base CoordinateRing ≫
      𝟙 (affineDifferentialSheaf Base CoordinateRing).val
  apply basisModuleHom_ext CoordinateRing
  intro denominator vector
  change (tildeToAffineDifferentialSheaf Base CoordinateRing).val.app (op (basicOpen denominator))
      ((affineDifferentialSheafToTilde Base CoordinateRing).val.app (op (basicOpen denominator))
        ((affineDifferentialUnit Base CoordinateRing).app (op (basicOpen denominator)) vector)) =
    (affineDifferentialUnit Base CoordinateRing).app (op (basicOpen denominator)) vector
  calc
    _ = (tildeToAffineDifferentialSheaf Base CoordinateRing).val.app (op (basicOpen denominator))
        ((basisDifferentialAdditiveIso Base CoordinateRing).inv.app (op denominator) vector) :=
      congrArg (fun vectorSection =>
        (tildeToAffineDifferentialSheaf Base CoordinateRing).val.app
          (op (basicOpen denominator)) vectorSection)
        (affineDifferentialSheafToTilde_unit_app Base CoordinateRing denominator vector)
    _ = (affineDifferentialUnit Base CoordinateRing).app (op (basicOpen denominator))
        ((basisDifferentialAdditiveIso Base CoordinateRing).hom.app (op denominator)
          ((basisDifferentialAdditiveIso Base CoordinateRing).inv.app (op denominator) vector)) :=
      tildeToAffineDifferentialSheaf_app Base CoordinateRing denominator _
    _ = _ := congrArg (fun vectorSection =>
      (affineDifferentialUnit Base CoordinateRing).app (op (basicOpen denominator)) vectorSection)
      (Iso.inv_hom_id_apply ((basisDifferentialAdditiveIso Base CoordinateRing).app
        (op denominator)) vector)

theorem affineDifferentialSheafToTilde_inv_hom_id :
    tildeToAffineDifferentialSheaf Base CoordinateRing ≫
        affineDifferentialSheafToTilde Base CoordinateRing =
      𝟙 (tilde (CanonicalAffine.differentialModule Base CoordinateRing)) := by
  apply SheafOfModules.hom_ext
  apply basisModuleHom_ext CoordinateRing
  intro denominator vector
  change (affineDifferentialSheafToTilde Base CoordinateRing).val.app (op (basicOpen denominator))
      ((tildeToAffineDifferentialSheaf Base CoordinateRing).val.app (op (basicOpen denominator))
        vector) = vector
  calc
    _ = (affineDifferentialSheafToTilde Base CoordinateRing).val.app (op (basicOpen denominator))
        ((affineDifferentialUnit Base CoordinateRing).app (op (basicOpen denominator))
          ((basisDifferentialAdditiveIso Base CoordinateRing).hom.app (op denominator) vector)) :=
      congrArg (fun vectorSection =>
        (affineDifferentialSheafToTilde Base CoordinateRing).val.app
          (op (basicOpen denominator)) vectorSection)
        (tildeToAffineDifferentialSheaf_app Base CoordinateRing denominator vector)
    _ = (basisDifferentialAdditiveIso Base CoordinateRing).inv.app (op denominator)
        ((basisDifferentialAdditiveIso Base CoordinateRing).hom.app (op denominator) vector) :=
      affineDifferentialSheafToTilde_unit_app Base CoordinateRing denominator _
    _ = _ := Iso.hom_inv_id_apply
      ((basisDifferentialAdditiveIso Base CoordinateRing).app (op denominator)) vector

noncomputable def affineDifferentialSheafTildeIso :
    affineDifferentialSheaf Base CoordinateRing ≅
      tilde (CanonicalAffine.differentialModule Base CoordinateRing) where
  hom := affineDifferentialSheafToTilde Base CoordinateRing
  inv := tildeToAffineDifferentialSheaf Base CoordinateRing
  hom_inv_id := affineDifferentialSheafToTilde_hom_inv_id Base CoordinateRing
  inv_hom_id := affineDifferentialSheafToTilde_inv_hom_id Base CoordinateRing

noncomputable def cotangentSpecSectionIso (domain : (Spec CoordinateRing).Opensᵒᵖ) :
    (cotangentPresheaf
      (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))).obj domain ≅
      (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing).obj domain :=
  differentialBaseIso
    ((cotangentCoefficientMap
      (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))).app domain)
    ((CanonicalAffine.sectionCoefficientMap Base CoordinateRing).app domain)
    (Scheme.ΓSpecIso Base) (cotangentCoefficientMap_spec Base CoordinateRing domain)

theorem cotangentSpecSectionIso_d (domain : (Spec CoordinateRing).Opensᵒᵖ)
    (regularFunction : (Spec CoordinateRing).presheaf.obj domain) :
    (cotangentSpecSectionIso Base CoordinateRing domain).hom
        (CommRingCat.KaehlerDifferential.d regularFunction) =
      CommRingCat.KaehlerDifferential.d regularFunction :=
  differentialBaseIso_d _ _ _ _ regularFunction

noncomputable def cotangentSpecPresheafIso :
    cotangentPresheaf (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) ≅
      CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing := by
  refine PresheafOfModules.isoMk (cotangentSpecSectionIso Base CoordinateRing) ?_
  intro domain smaller restriction
  apply CommRingCat.KaehlerDifferential.ext
  intro regularFunction
  change (cotangentSpecSectionIso Base CoordinateRing smaller).hom
      ((cotangentPresheaf
        (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))).map
          restriction (CommRingCat.KaehlerDifferential.d regularFunction)) =
    (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing).map restriction
      ((cotangentSpecSectionIso Base CoordinateRing domain).hom
        (CommRingCat.KaehlerDifferential.d regularFunction))
  have sourceRestriction :=
    PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
      (cotangentCoefficientMap
        (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing)))) restriction regularFunction
  have targetRestriction :=
    PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
      (CanonicalAffine.sectionCoefficientMap Base CoordinateRing) restriction regularFunction
  calc
    _ = (cotangentSpecSectionIso Base CoordinateRing smaller).hom
        (CommRingCat.KaehlerDifferential.d
          ((Spec CoordinateRing).presheaf.map restriction regularFunction)) :=
      congrArg (fun differential =>
        (cotangentSpecSectionIso Base CoordinateRing smaller).hom differential) sourceRestriction
    _ = CommRingCat.KaehlerDifferential.d
        ((Spec CoordinateRing).presheaf.map restriction regularFunction) :=
      cotangentSpecSectionIso_d Base CoordinateRing smaller _
    _ = (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing).map restriction
        (CommRingCat.KaehlerDifferential.d regularFunction) := targetRestriction.symm
    _ = _ := congrArg (fun differential =>
      (CanonicalAffine.affineDifferentialPresheaf Base CoordinateRing).map restriction differential)
      (cotangentSpecSectionIso_d Base CoordinateRing domain regularFunction).symm

noncomputable def cotangentSheafSpecTildeIso :
    cotangentSheaf (Spec.map (CommRingCat.ofHom (algebraMap Base CoordinateRing))) ≅
      tilde (CanonicalAffine.differentialModule Base CoordinateRing) :=
  (PresheafOfModules.sheafification (𝟙 (Spec CoordinateRing).ringCatSheaf.obj)).mapIso
    (cotangentSpecPresheafIso Base CoordinateRing) ≪≫
      affineDifferentialSheafTildeIso Base CoordinateRing

end BondalThomsen.CotangentTilde
