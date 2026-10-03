module

public import BondalThomsen.Toric.Canonical.ChartComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Etale.Kaehler

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace
open PrimeSpectrum

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace BondalThomsen.CanonicalAffine

universe coefficientUniverse

variable (Base CoordinateRing : CommRingCat.{coefficientUniverse})
    [Algebra Base CoordinateRing]

noncomputable def differentialModule : ModuleCat CoordinateRing :=
  ModuleCat.of CoordinateRing (KaehlerDifferential Base CoordinateRing)

noncomputable def sectionDifferentialModule (domain : (Spec CoordinateRing).Opens) :
    ModuleCat Γ(Spec CoordinateRing, domain) :=
  letI := ((algebraMap CoordinateRing Γ(Spec CoordinateRing, domain)).comp
    (algebraMap Base CoordinateRing)).toAlgebra
  ModuleCat.of Γ(Spec CoordinateRing, domain)
    (KaehlerDifferential Base Γ(Spec CoordinateRing, domain))

noncomputable def sectionCoefficientMap :
    (Functor.const (Spec CoordinateRing).Opensᵒᵖ).obj Base ⟶ (Spec CoordinateRing).presheaf where
  app domain := CommRingCat.ofHom
    ((algebraMap CoordinateRing Γ(Spec CoordinateRing, domain.unop)).comp
      (algebraMap Base CoordinateRing))
  naturality := fun _ _ _ => rfl

noncomputable def affineDifferentialPresheaf : (Spec CoordinateRing).PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (sectionCoefficientMap Base CoordinateRing)

noncomputable def basicOpenDifferentialEquiv (denominator : CoordinateRing) :
    (modulesSpecToSheaf.obj (tilde (differentialModule Base CoordinateRing))).presheaf.obj
        (op (basicOpen denominator)) ≃ₗ[CoordinateRing]
      (ModuleCat.restrictScalars
        (algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator))).obj
          (sectionDifferentialModule Base CoordinateRing (basicOpen denominator)) := by
  letI := ((algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator)).comp
    (algebraMap Base CoordinateRing)).toAlgebra
  letI : IsScalarTower Base CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI := KaehlerDifferential.isLocalizedModule_map Base CoordinateRing
    Γ(Spec CoordinateRing, basicOpen denominator) (.powers denominator)
  let comparison := IsLocalizedModule.linearEquiv (.powers denominator)
    (AlgebraicGeometry.tilde.toOpen (differentialModule Base CoordinateRing)
      (basicOpen denominator)).hom
    (KaehlerDifferential.map Base Base CoordinateRing
      Γ(Spec CoordinateRing, basicOpen denominator))
  exact
    { comparison.toAddEquiv with
      map_smul' := fun scalar vector => by
        change comparison (scalar • vector) =
          algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator) scalar •
            comparison vector
        exact (comparison.map_smul scalar vector).trans
          (IsScalarTower.algebraMap_smul
            Γ(Spec CoordinateRing, basicOpen denominator) scalar (comparison vector)).symm }

theorem basicOpenDifferentialEquiv_toOpen_D (denominator regularFunction : CoordinateRing) :
    basicOpenDifferentialEquiv Base CoordinateRing denominator
        (AlgebraicGeometry.tilde.toOpen (differentialModule Base CoordinateRing)
          (basicOpen denominator) (KaehlerDifferential.D Base CoordinateRing regularFunction)) =
      letI := ((algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator)).comp
        (algebraMap Base CoordinateRing)).toAlgebra
      KaehlerDifferential.D Base Γ(Spec CoordinateRing, basicOpen denominator)
        (algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator) regularFunction) := by
  let := ((algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator)).comp
    (algebraMap Base CoordinateRing)).toAlgebra
  let : IsScalarTower Base CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have := KaehlerDifferential.isLocalizedModule_map Base CoordinateRing
    Γ(Spec CoordinateRing, basicOpen denominator) (.powers denominator)
  change IsLocalizedModule.linearEquiv (.powers denominator)
      (AlgebraicGeometry.tilde.toOpen (differentialModule Base CoordinateRing)
        (basicOpen denominator)).hom
      (KaehlerDifferential.map Base Base CoordinateRing
        Γ(Spec CoordinateRing, basicOpen denominator))
      ((AlgebraicGeometry.tilde.toOpen (differentialModule Base CoordinateRing)
        (basicOpen denominator)).hom (KaehlerDifferential.D Base CoordinateRing regularFunction)) = _
  exact (IsLocalizedModule.linearEquiv_apply _ _ _ _).trans
    (KaehlerDifferential.map_D Base Base CoordinateRing
      Γ(Spec CoordinateRing, basicOpen denominator) regularFunction)

noncomputable def basicOpenDifferentialIso (denominator : CoordinateRing) :
    (tilde (differentialModule Base CoordinateRing)).val.obj (op (basicOpen denominator)) ≅
      sectionDifferentialModule Base CoordinateRing (basicOpen denominator) := by
  let SectionRing := Γ(Spec CoordinateRing, basicOpen denominator)
  let Source := (tilde (differentialModule Base CoordinateRing)).val.obj
    (op (basicOpen denominator))
  let Target := sectionDifferentialModule Base CoordinateRing (basicOpen denominator)
  letI : Module CoordinateRing Source := Module.compHom Source (algebraMap CoordinateRing SectionRing)
  letI : Module CoordinateRing Target := Module.compHom Target (algebraMap CoordinateRing SectionRing)
  haveI : IsScalarTower CoordinateRing SectionRing Source :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower CoordinateRing SectionRing Target :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let comparison := basicOpenDifferentialEquiv Base CoordinateRing denominator
  let linear : Source →ₗ[CoordinateRing] Target :=
    { comparison.toAddMonoidHom with
      map_smul' := fun scalar vector => by
        exact comparison.map_smul scalar vector }
  exact (LinearEquiv.ofBijective
    (linear.extendScalarsOfIsLocalization (.powers denominator) SectionRing)
      comparison.bijective).toModuleIso

noncomputable def affineDifferentialSections :
    (Spec CoordinateRing).Opensᵒᵖ ⥤ ModuleCat CoordinateRing where
  obj domain := (ModuleCat.restrictScalars
    (algebraMap CoordinateRing Γ(Spec CoordinateRing, domain.unop))).obj
      (sectionDifferentialModule Base CoordinateRing domain.unop)
  map {domain smaller} restriction := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars
      (algebraMap CoordinateRing Γ(Spec CoordinateRing, domain.unop))).obj
        (sectionDifferentialModule Base CoordinateRing domain.unop))
    (Y := (ModuleCat.restrictScalars
      (algebraMap CoordinateRing Γ(Spec CoordinateRing, smaller.unop))).obj
        (sectionDifferentialModule Base CoordinateRing smaller.unop))
    { toFun := (affineDifferentialPresheaf Base CoordinateRing).map restriction
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun scalar vector => by
        exact (affineDifferentialPresheaf Base CoordinateRing).map_smul restriction
          (algebraMap CoordinateRing Γ(Spec CoordinateRing, _) scalar) vector }
  map_id domain := by
    ext vector
    exact ConcreteCategory.congr_hom
      ((affineDifferentialPresheaf Base CoordinateRing).map_id domain) vector
  map_comp first second := by
    ext vector
    exact ConcreteCategory.congr_hom
      ((affineDifferentialPresheaf Base CoordinateRing).map_comp first second) vector

noncomputable def basicOpenDifferentialSectionsIso (denominator : CoordinateRing) :
    (modulesSpecToSheaf.obj (tilde (differentialModule Base CoordinateRing))).presheaf.obj
        (op (basicOpen denominator)) ≅
      (affineDifferentialSections Base CoordinateRing).obj (op (basicOpen denominator)) :=
  (basicOpenDifferentialEquiv Base CoordinateRing denominator).toModuleIso

theorem affineDifferentialSections_map_D {domain smaller : (Spec CoordinateRing).Opens}
    (restriction : smaller ⟶ domain) (regularFunction : Γ(Spec CoordinateRing, domain)) :
    (affineDifferentialSections Base CoordinateRing).map restriction.op
        (CommRingCat.KaehlerDifferential.d regularFunction) =
      CommRingCat.KaehlerDifferential.d
        ((Spec CoordinateRing).presheaf.map restriction.op regularFunction) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
    (sectionCoefficientMap Base CoordinateRing) restriction.op regularFunction

theorem basicOpenDifferentialSectionsIso_naturality
    (denominator smallerDenominator : CoordinateRing)
    (restriction : basicOpen smallerDenominator ⟶ basicOpen denominator) :
    (modulesSpecToSheaf.obj (tilde (differentialModule Base CoordinateRing))).presheaf.map
        restriction.op ≫
      (basicOpenDifferentialSectionsIso Base CoordinateRing smallerDenominator).hom =
    (basicOpenDifferentialSectionsIso Base CoordinateRing denominator).hom ≫
      (affineDifferentialSections Base CoordinateRing).map restriction.op := by
  let Source := (modulesSpecToSheaf.obj
    (tilde (differentialModule Base CoordinateRing))).presheaf
  let Target := affineDifferentialSections Base CoordinateRing
  let : Module Γ(Spec CoordinateRing, basicOpen smallerDenominator)
      (Target.obj (op (basicOpen smallerDenominator))) :=
    (sectionDifferentialModule Base CoordinateRing (basicOpen smallerDenominator)).isModule
  let first : Source.obj (op (basicOpen denominator)) →ₗ[CoordinateRing]
      Target.obj (op (basicOpen smallerDenominator)) :=
    ((basicOpenDifferentialSectionsIso Base CoordinateRing smallerDenominator).hom.hom).comp
      (Source.map restriction.op).hom
  let second : Source.obj (op (basicOpen denominator)) →ₗ[CoordinateRing]
      Target.obj (op (basicOpen smallerDenominator)) :=
    (Target.map restriction.op).hom.comp
      (basicOpenDifferentialSectionsIso Base CoordinateRing denominator).hom.hom
  have units : ∀ scalar : Submonoid.powers denominator,
      IsUnit (algebraMap CoordinateRing
        (Module.End CoordinateRing (Target.obj (op (basicOpen smallerDenominator)))) scalar) := by
    intro scalar
    have unit := (IsLocalization.map_units
      Γ(Spec CoordinateRing, basicOpen denominator) scalar).map
        ((Spec CoordinateRing).presheaf.map restriction.op).hom
    apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun vector : Target.obj (op (basicOpen smallerDenominator)) =>
      algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen smallerDenominator)
        scalar.val • vector)
    exact unit.smul_bijective
  have agrees : first = second := by
    apply IsLocalizedModule.ext (.powers denominator)
      (AlgebraicGeometry.tilde.toOpen (differentialModule Base CoordinateRing)
        (basicOpen denominator)).hom units
    apply LinearMap.ext
    intro differential
    obtain ⟨coefficients, rfl⟩ :=
      KaehlerDifferential.linearCombination_surjective Base CoordinateRing differential
    induction coefficients using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add firstCoefficients secondCoefficients first_eq second_eq =>
        simp only [map_add, first_eq, second_eq]
    | single regularFunction coefficient =>
        simp only [Finsupp.linearCombination_single, map_smul]
        congr 1
        change basicOpenDifferentialEquiv Base CoordinateRing smallerDenominator
          (Source.map restriction.op
            (AlgebraicGeometry.tilde.toOpen (differentialModule Base CoordinateRing)
              (basicOpen denominator) (KaehlerDifferential.D Base CoordinateRing regularFunction))) =
          Target.map restriction.op
            (basicOpenDifferentialEquiv Base CoordinateRing denominator
              (AlgebraicGeometry.tilde.toOpen (differentialModule Base CoordinateRing)
                (basicOpen denominator) (KaehlerDifferential.D Base CoordinateRing regularFunction)))
        have restricts := ConcreteCategory.congr_hom
          (AlgebraicGeometry.tilde.toOpen_res (differentialModule Base CoordinateRing)
            (basicOpen denominator) (basicOpen smallerDenominator) restriction)
          (KaehlerDifferential.D Base CoordinateRing regularFunction)
        change Source.map restriction.op
          (AlgebraicGeometry.tilde.toOpen (differentialModule Base CoordinateRing)
            (basicOpen denominator) (KaehlerDifferential.D Base CoordinateRing regularFunction)) =
          AlgebraicGeometry.tilde.toOpen (differentialModule Base CoordinateRing)
            (basicOpen smallerDenominator) (KaehlerDifferential.D Base CoordinateRing regularFunction)
          at restricts
        calc
          _ = basicOpenDifferentialEquiv Base CoordinateRing smallerDenominator
              (AlgebraicGeometry.tilde.toOpen (differentialModule Base CoordinateRing)
                (basicOpen smallerDenominator)
                (KaehlerDifferential.D Base CoordinateRing regularFunction)) :=
            congrArg (basicOpenDifferentialEquiv Base CoordinateRing smallerDenominator) restricts
          _ = CommRingCat.KaehlerDifferential.d
              (f := (sectionCoefficientMap Base CoordinateRing).app
                (op (basicOpen smallerDenominator)))
              (algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen smallerDenominator)
                regularFunction) :=
            basicOpenDifferentialEquiv_toOpen_D Base CoordinateRing smallerDenominator regularFunction
          _ = Target.map restriction.op
              (CommRingCat.KaehlerDifferential.d
                (f := (sectionCoefficientMap Base CoordinateRing).app (op (basicOpen denominator)))
                (algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator)
                  regularFunction)) :=
            (affineDifferentialSections_map_D Base CoordinateRing
              (domain := basicOpen denominator) (smaller := basicOpen smallerDenominator)
              restriction
              (algebraMap CoordinateRing Γ(Spec CoordinateRing, basicOpen denominator)
                regularFunction)).symm
          _ = _ := congrArg (fun vector => Target.map restriction.op vector)
            (basicOpenDifferentialEquiv_toOpen_D Base CoordinateRing denominator regularFunction).symm
  exact ModuleCat.hom_ext agrees

end BondalThomsen.CanonicalAffine

namespace BondalThomsen.CanonicalAffine

universe coefficientUniverse

abbrev BasicOpenCategory (CoordinateRing : CommRingCat.{coefficientUniverse}) :=
  InducedCategory (Spec CoordinateRing).Opens (fun denominator : CoordinateRing =>
    (basicOpen denominator : (Spec CoordinateRing).Opens))

def basicOpenFunctor (CoordinateRing : CommRingCat.{coefficientUniverse}) :
    BasicOpenCategory CoordinateRing ⥤ (Spec CoordinateRing).Opens :=
  inducedFunctor (fun denominator : CoordinateRing =>
    (basicOpen denominator : (Spec CoordinateRing).Opens))

instance basicOpenFunctor_isCoverDense (CoordinateRing : CommRingCat.{coefficientUniverse}) :
    (basicOpenFunctor CoordinateRing).IsCoverDense
      (Opens.grothendieckTopology (Spec CoordinateRing)) := by
  exact TopCat.Opens.coverDense_inducedFunctor
    (X := (Spec CoordinateRing).toTopCat)
    (B := fun denominator : CoordinateRing =>
      (basicOpen denominator : (Spec CoordinateRing).Opens))
    PrimeSpectrum.isBasis_basic_opens

noncomputable def basicOpenDifferentialPresheafIso
    (Base CoordinateRing : CommRingCat.{coefficientUniverse}) [Algebra Base CoordinateRing] :
    (basicOpenFunctor CoordinateRing).op ⋙
        (modulesSpecToSheaf.obj (tilde (differentialModule Base CoordinateRing))).presheaf ≅
      (basicOpenFunctor CoordinateRing).op ⋙ affineDifferentialSections Base CoordinateRing :=
  NatIso.ofComponents
    (fun domain => basicOpenDifferentialSectionsIso Base CoordinateRing domain.unop)
    (fun {domain smaller} restriction => basicOpenDifferentialSectionsIso_naturality
      Base CoordinateRing domain.unop smaller.unop restriction.unop.hom)

end BondalThomsen.CanonicalAffine
