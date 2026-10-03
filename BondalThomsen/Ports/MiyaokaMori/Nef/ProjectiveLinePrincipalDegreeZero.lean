module

public import BondalThomsen.Ports.MiyaokaMori.Nef.ProjectiveLineChartRing
public import BondalThomsen.Ports.MiyaokaMori.Nef.OpenImmersionOrder
public import BondalThomsen.Ports.MiyaokaMori.Nef.ResidueDegreeComposition
public import BondalThomsen.Ports.MiyaokaMori.Nef.AffineLinePrincipalOrder
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveChartRing AlgebraicGeometry.AffineLinePrincipalOrder
open scoped Classical BigOperators

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveLinePrincipalDegree

theorem germ_app_of_eq_SpecMap_fromSpec {source : Scheme.{u}} {region : source.Opens}
    (affine : IsAffineOpen region) {ring : CommRingCat.{u}} (ringMap : Γ(source, region) ⟶ ring)
    (morphism : Spec ring ⟶ source) (factorization : morphism = Spec.map ringMap ≫ affine.fromSpec)
    (sectionValue : Γ(source, region)) (point : Spec ring) (contains : point ∈ morphism ⁻¹ᵁ region) :
    (Spec ring).presheaf.germ (morphism ⁻¹ᵁ region) point contains (morphism.app region sectionValue) =
      (Spec ring).presheaf.germ ⊤ point trivial ((Scheme.ΓSpecIso ring).inv (ringMap sectionValue)) := by
  subst factorization
  rw [Scheme.Hom.comp_app]
  erw [CommRingCat.comp_apply]
  rw [IsAffineOpen.fromSpec_app_self]
  erw [CommRingCat.comp_apply]
  have naturality := congrArg (fun map => map.hom ((Scheme.ΓSpecIso Γ(source, region)).inv sectionValue))
    ((Spec.map ringMap).naturality (eqToHom affine.fromSpec_preimage_self).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at naturality
  erw [naturality]
  have topNaturality := congrArg (fun map => map.hom sectionValue) (Scheme.ΓSpecIso_inv_naturality ringMap)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop] at topNaturality
  erw [← topNaturality]
  exact (Spec ring).presheaf.germ_res_apply' _ point contains _

theorem awayι_eq_SpecMap_fromSpec {subobjects : Type*} {ring : Type u} [CommRing ring]
    [SetLike subobjects ring] [AddSubgroupClass subobjects ring] (grading : ℕ → subobjects)
    [GradedRing grading] (element : ring) {degree : ℕ} (homogeneous : element ∈ grading degree)
    (positive : 0 < degree) :
    Proj.awayι grading element homogeneous positive =
      Spec.map (Proj.basicOpenIsoAway grading element homogeneous positive).inv ≫
        (Proj.isAffineOpen_basicOpen grading element homogeneous positive).fromSpec := by
  rw [Proj.awayι, IsAffineOpen.fromSpec, ← Category.assoc]
  congr 1
  rw [← cancel_epi (Proj.basicOpenIsoSpec grading element homogeneous positive).hom,
    Iso.hom_inv_id, Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec, Category.assoc,
    ← Spec.map_comp_assoc, ← Proj.basicOpenIsoAway_hom grading element homogeneous positive,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp, ← IsAffineOpen.isoSpec_hom, Iso.hom_inv_id]
  exact Proj.isAffineOpen_basicOpen grading element homogeneous positive

variable (baseField : Type u) [Field baseField]

abbrev projectiveLine := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)

theorem adjoin_variables :
    Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) baseField)) = ⊤ := by
  apply top_unique
  intro polynomial member
  clear member
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    exact (Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) baseField))).algebraMap_mem
        ⟨MvPolynomial.C scalar, MvPolynomial.isHomogeneous_C (Fin 2) scalar⟩
  | add first second firstMember secondMember => exact add_mem firstMember secondMember
  | mul_X polynomial index member => exact mul_mem member (Algebra.subset_adjoin ⟨index, rfl⟩)

theorem coordinateOpens_cover :
    (⨆ chart : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
      (MvPolynomial.X chart)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) MvPolynomial.X
    (fun chart => ⟨1, MvPolynomial.isHomogeneous_X baseField chart⟩) (adjoin_variables baseField)

theorem exists_coordinateOpen (point : projectiveLine baseField) :
    ∃ chart : Fin 2, point ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
      (MvPolynomial.X chart) := by
  apply Opens.mem_iSup.mp
  rw [coordinateOpens_cover]
  trivial

def otherIndex (chart : Fin 2) : {index : Fin 2 // index ≠ chart} :=
  ⟨1 - chart, by fin_cases chart <;> decide⟩

@[instance_reducible] def uniqueOther (chart : Fin 2) : Unique {index : Fin 2 // index ≠ chart} where
  default := otherIndex chart
  uniq := fun ⟨index, distinct⟩ => Subtype.ext (by
    fin_cases chart <;> fin_cases index <;> first | rfl | exact (distinct rfl).elim)

attribute [local instance] uniqueOther

def chartCoord (chart : Fin 2) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)
      ≃+* Polynomial baseField :=
  (chartRingEquiv 1 baseField chart).trans
    (MvPolynomial.uniqueAlgEquiv baseField {index : Fin 2 // index ≠ chart}).toRingEquiv

def chartι (chart : Fin 2) : Spec (CommRingCat.of (Polynomial baseField)) ⟶ projectiveLine baseField :=
  Spec.map (chartCoord baseField chart).toCommRingCatIso.hom ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)
      (X_mem 1 baseField chart) Nat.one_pos

instance chartι_isOpenImmersion (chart : Fin 2) : IsOpenImmersion (chartι baseField chart) := by
  unfold chartι
  exact @IsOpenImmersion.comp _ _ _ _ _ inferInstance
    (inferInstanceAs (IsOpenImmersion (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
      (MvPolynomial.X chart) (X_mem 1 baseField chart) Nat.one_pos)))

theorem opensRange_chartι (chart : Fin 2) :
    (chartι baseField chart).opensRange =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart) := by
  apply Opens.ext
  ext point
  change (∃ preimage, chartι baseField chart preimage = point) ↔ _
  rw [← Proj.opensRange_awayι _ _ (X_mem 1 baseField chart) Nat.one_pos]
  constructor
  · rintro ⟨preimage, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨preimage, equation⟩
    obtain ⟨polynomialPoint, rfl⟩ :=
      (Spec.map (chartCoord baseField chart).toCommRingCatIso.hom).homeomorph.surjective preimage
    exact ⟨polynomialPoint, equation⟩

def chartOpenCover : (projectiveLine baseField).OpenCover where
  I₀ := Fin 2
  X := fun _ => Spec (CommRingCat.of (Polynomial baseField))
  f := chartι baseField
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro point
    obtain ⟨chart, contains⟩ := exists_coordinateOpen baseField point
    rw [← opensRange_chartι] at contains
    exact ⟨chart, contains⟩

instance projIsLocallyNoetherian : IsLocallyNoetherian (projectiveLine baseField) := by
  apply (isLocallyNoetherian_iff_openCover (chartOpenCover baseField)).mpr
  intro chart
  change IsLocallyNoetherian (Spec (CommRingCat.of (Polynomial baseField)))
  infer_instance

instance projIsReduced : IsReduced (projectiveLine baseField) := by
  apply (IsReduced.iff_of_openCover _ (chartOpenCover baseField)).mpr
  intro chart
  change IsReduced (Spec (CommRingCat.of (Polynomial baseField)))
  infer_instance

instance projIrreducible : IrreducibleSpace (projectiveLine baseField) := by
  change IrreducibleSpace (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 2) baseField))
  let generic : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) :=
    { asHomogeneousIdeal := ⊥
      isPrime := by rw [HomogeneousIdeal.toIdeal_bot]; infer_instance
      not_irrelevant_le := by
        intro subset
        have member : MvPolynomial.X (0 : Fin 2) ∈
            (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)) :=
          subset (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
            (MvPolynomial.isHomogeneous_X baseField 0))
        change MvPolynomial.X (0 : Fin 2) ∈ (⊥ : Ideal (MvPolynomial (Fin 2) baseField)) at member
        exact MvPolynomial.X_ne_zero (0 : Fin 2) (Ideal.mem_bot.mp member) }
  have closureEquation : closure ({generic} : Set (ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin 2) baseField))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro point
    apply (ProjectiveSpectrum.le_iff_mem_closure _ generic point).mp
    change (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)) ≤ point.asHomogeneousIdeal
    exact bot_le
  apply (irreducibleSpace_def _).mpr
  simpa only [closureEquation, Set.top_eq_univ] using (isIrreducible_singleton (x := generic)).closure

instance projIsIntegral : IsIntegral (projectiveLine baseField) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

def structureMap : projectiveLine baseField ⟶ Spec (CommRingCat.of baseField) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) ≫
    Spec.map (CommRingCat.ofHom (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0)))

def inftyPoint : projectiveLine baseField := chartι baseField 1 (originPoint baseField)

theorem chartCoord_algebraMap (chart : Fin 2) (scalar : baseField) :
    chartCoord baseField chart (algebraMap (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0) _
      (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0) scalar)) = Polynomial.C scalar := by
  have equality : chartRingEquiv 1 baseField chart
      (algebraMap (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0) _
        (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0) scalar)) = MvPolynomial.C scalar := by
    rw [← polyToChart_C]
    exact RingHom.congr_fun (chartToPoly_comp_polyToChart 1 baseField chart) (MvPolynomial.C scalar)
  show MvPolynomial.uniqueAlgEquiv baseField {index : Fin 2 // index ≠ chart}
    (chartRingEquiv 1 baseField chart _) = _
  rw [equality, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
  rfl

theorem chartι_comp_structureMap (chart : Fin 2) :
    chartι baseField chart ≫ structureMap baseField = AffineLinePrincipalOrder.structureMap baseField := by
  change Spec.map (chartCoord baseField chart).toCommRingCatIso.hom ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)
      (X_mem 1 baseField chart) Nat.one_pos ≫
    (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) ≫
      Spec.map (CommRingCat.ofHom (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0)))) =
    Spec.map (CommRingCat.ofHom (algebraMap baseField (Polynomial baseField)))
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun scalar => ?_)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  exact chartCoord_algebraMap baseField chart scalar

theorem chartCoord_isLocalizationElem (chart index : Fin 2) (distinct : index ≠ chart) :
    chartCoord baseField chart (HomogeneousLocalization.Away.isLocalizationElem (X_mem 1 baseField chart)
      (X_mem 1 baseField index)) = Polynomial.X := by
  have equality : chartRingEquiv 1 baseField chart (HomogeneousLocalization.Away.isLocalizationElem
      (X_mem 1 baseField chart) (X_mem 1 baseField index)) = MvPolynomial.X ⟨index, distinct⟩ := by
    show chartToPoly 1 baseField chart
      (HomogeneousLocalization.Away.mk _ (X_mem 1 baseField chart) 1 (MvPolynomial.X index ^ 1) _) = _
    rw [chartToPoly_mk, map_pow, dehomogenize_X_of_ne 1 baseField chart distinct, pow_one]
  show MvPolynomial.uniqueAlgEquiv baseField {index : Fin 2 // index ≠ chart} (chartRingEquiv 1 baseField chart _) = _
  rw [equality]
  show MvPolynomial.uniqueAlgEquiv baseField {index : Fin 2 // index ≠ chart}
    (MvPolynomial.monomial (Finsupp.single ⟨index, distinct⟩ 1) 1) = _
  rw [MvPolynomial.uniqueAlgEquiv_monomial,
    Subsingleton.elim (default : {index : Fin 2 // index ≠ chart}) ⟨index, distinct⟩,
    Finsupp.single_eq_same, Polynomial.monomial_one_one_eq_X]

theorem chartι_apply (chart : Fin 2) (point : Spec (CommRingCat.of (Polynomial baseField))) :
    chartι baseField chart point = Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
      (MvPolynomial.X chart) (X_mem 1 baseField chart) Nat.one_pos
      (Spec.map (chartCoord baseField chart).toCommRingCatIso.hom point) := rfl

theorem isLocalizationElem_mem_iff (chart index : Fin 2) (distinct : index ≠ chart)
    (point : Spec (CommRingCat.of (Polynomial baseField))) :
    HomogeneousLocalization.Away.isLocalizationElem (X_mem 1 baseField chart) (X_mem 1 baseField index) ∈
      (Spec.map (chartCoord baseField chart).toCommRingCatIso.hom point).asIdeal ↔ Polynomial.X ∈ point.asIdeal := by
  show chartCoord baseField chart _ ∈ point.asIdeal ↔ _
  rw [chartCoord_isLocalizationElem baseField chart index distinct]

theorem mem_range_chartι_zero_or_eq_inftyPoint (point : projectiveLine baseField) :
    (∃ preimage, chartι baseField 0 preimage = point) ∨ point = inftyPoint baseField := by
  by_cases firstCoordinate : MvPolynomial.X (0 : Fin 2) ∈ point.asHomogeneousIdeal
  · right
    have secondCoordinate : MvPolynomial.X (1 : Fin 2) ∉ point.asHomogeneousIdeal := by
      obtain ⟨chart, contains⟩ := exists_coordinateOpen baseField point
      fin_cases chart
      · exact absurd firstCoordinate contains
      · exact contains
    have contains : point ∈ (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
      (MvPolynomial.X 1) (X_mem 1 baseField 1) Nat.one_pos).opensRange := by
      rw [Proj.opensRange_awayι]
      exact secondCoordinate
    obtain ⟨localPoint, imageEquation⟩ := contains
    obtain ⟨polynomialPoint, coordinateEquation⟩ :=
      (Spec.map (chartCoord baseField 1).toCommRingCatIso.hom).homeomorph.surjective localPoint
    change Spec.map (chartCoord baseField 1).toCommRingCatIso.hom polynomialPoint = localPoint at coordinateEquation
    have outside : Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X 1)
        (X_mem 1 baseField 1) Nat.one_pos
        (Spec.map (chartCoord baseField 1).toCommRingCatIso.hom polynomialPoint) ∉
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X 0) := by
      rw [coordinateEquation, imageEquation]
      exact not_not.mpr firstCoordinate
    have preimageOutside : Spec.map (chartCoord baseField 1).toCommRingCatIso.hom polynomialPoint ∉
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X 1)
        (X_mem 1 baseField 1) Nat.one_pos ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X 0) := outside
    rw [Proj.awayι_preimage_basicOpen _ _ _ (X_mem 1 baseField 0) Nat.one_pos] at preimageOutside
    have coordinateMember : Polynomial.X ∈ polynomialPoint.asIdeal :=
      (isLocalizationElem_mem_iff baseField 1 0 zero_ne_one polynomialPoint).mp (not_not.mp preimageOutside)
    have pointEquation : polynomialPoint = originPoint baseField := by
      apply PrimeSpectrum.ext
      have subset : Ideal.span {(Polynomial.X : Polynomial baseField)} ≤ polynomialPoint.asIdeal :=
        (Ideal.span_singleton_le_iff_mem _).mpr coordinateMember
      have maximal : (Ideal.span {(Polynomial.X : Polynomial baseField)}).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
      exact (maximal.eq_of_le polynomialPoint.isPrime.ne_top subset).symm
    rw [← imageEquation, ← coordinateEquation, inftyPoint, chartι_apply, ← pointEquation]
  · left
    have contains : point ∈ (chartι baseField 0).opensRange := by
      rw [opensRange_chartι]
      exact firstCoordinate
    exact contains

theorem inftyPoint_not_mem_range_chartι_zero : inftyPoint baseField ∉ Set.range (chartι baseField 0) := by
  rintro ⟨preimage, equation⟩
  have contains : chartι baseField 0 preimage ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X 0) := by
    rw [← opensRange_chartι]
    exact ⟨preimage, rfl⟩
  rw [equation, inftyPoint, chartι_apply] at contains
  have preimageContains : Spec.map (chartCoord baseField 1).toCommRingCatIso.hom (originPoint baseField) ∈
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X 1)
        (X_mem 1 baseField 1) Nat.one_pos ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X 0) := contains
  rw [Proj.awayι_preimage_basicOpen _ _ _ (X_mem 1 baseField 0) Nat.one_pos] at preimageContains
  apply preimageContains
  rw [isLocalizationElem_mem_iff baseField 1 0 zero_ne_one]
  exact Ideal.mem_span_singleton_self _

instance nonempty_basicOpen (chart : Fin 2) :
    Nonempty (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)) := by
  refine ⟨⟨chartι baseField chart ⟨⊥, Ideal.isPrime_bot⟩, ?_⟩⟩
  rw [← opensRange_chartι]
  exact ⟨_, rfl⟩

theorem genericPoint_mem_basicOpen (chart : Fin 2) : genericPoint (projectiveLine baseField) ∈
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart) := by
  obtain ⟨point, contains⟩ := (inferInstance : Nonempty
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)))
  exact (genericPoint_specializes point).mem_open
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)).isOpen contains

theorem genericPoint_mem_basicOpen_mul : genericPoint (projectiveLine baseField) ∈
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [Proj.basicOpen_mul]
  exact ⟨genericPoint_mem_basicOpen baseField 0, genericPoint_mem_basicOpen baseField 1⟩

def chartSectionHom (chart : Fin 2) : Polynomial baseField →+* (projectiveLine baseField).functionField :=
  ((projectiveLine baseField).germToFunctionField
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart))).hom.comp
      (((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
        (MvPolynomial.X chart) (X_mem 1 baseField chart) Nat.one_pos).hom.hom).comp
          (chartCoord baseField chart).symm.toRingHom)

theorem chartι_eq (chart : Fin 2) :
    chartι baseField chart = Spec.map ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
        (MvPolynomial.X chart) (X_mem 1 baseField chart) Nat.one_pos).inv ≫
        (chartCoord baseField chart).toCommRingCatIso.hom) ≫
      (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)
        (X_mem 1 baseField chart) Nat.one_pos).fromSpec := by
  rw [chartι, awayι_eq_SpecMap_fromSpec, Spec.map_comp, Category.assoc]

def chartRingHom (chart : Fin 2) :
    Γ((projectiveLine baseField),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)) ⟶
      CommRingCat.of (Polynomial baseField) :=
  (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)
      (X_mem 1 baseField chart) Nat.one_pos).inv ≫ (chartCoord baseField chart).toCommRingCatIso.hom

def chartSection (chart : Fin 2) (polynomial : Polynomial baseField) :
    Γ((projectiveLine baseField),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)) :=
  (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)
    (X_mem 1 baseField chart) Nat.one_pos).hom ((chartCoord baseField chart).symm polynomial)

theorem chartRingHom_chartSection (chart : Fin 2) (polynomial : Polynomial baseField) :
    chartRingHom baseField chart (chartSection baseField chart polynomial) = polynomial := by
  rw [chartRingHom, chartSection]
  erw [CommRingCat.comp_apply, Iso.hom_inv_id_apply]
  exact (chartCoord baseField chart).apply_symm_apply polynomial

theorem chartι_eq' (chart : Fin 2) :
    chartι baseField chart = Spec.map (chartRingHom baseField chart) ≫
      (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)
        (X_mem 1 baseField chart) Nat.one_pos).fromSpec :=
  chartι_eq baseField chart

theorem chartSectionHom_apply (chart : Fin 2) (polynomial : Polynomial baseField) :
    chartSectionHom baseField chart polynomial = (projectiveLine baseField).presheaf.germ
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)) (genericPoint _)
      (genericPoint_mem_basicOpen baseField chart) (chartSection baseField chart polynomial) := rfl

theorem functionFieldMap_chartι_chartSectionHom (chart : Fin 2) (polynomial : Polynomial baseField) :
    OpenImmersionOrder.functionFieldMap (chartι baseField chart) (chartSectionHom baseField chart polynomial) =
      polyToFunctionField baseField polynomial := by
  rw [chartSectionHom_apply, polyToFunctionField_eq_germ]
  show ((projectiveLine baseField).presheaf.stalkSpecializes _ ≫
      (chartι baseField chart).stalkMap (genericPoint _)).hom _ = _
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
  erw [germ_app_of_eq_SpecMap_fromSpec _ (chartRingHom baseField chart) (chartι baseField chart) (chartι_eq' baseField chart)
    (chartSection baseField chart polynomial), chartRingHom_chartSection]

theorem chartSectionHom_eq_germ_mul (chart index : Fin 2)
    (coordinateEquation : MvPolynomial.X 0 * MvPolynomial.X 1 = (MvPolynomial.X chart : MvPolynomial (Fin 2) baseField) * MvPolynomial.X index)
    (polynomial : Polynomial baseField) :
    chartSectionHom baseField chart polynomial =
      (projectiveLine baseField).presheaf.germ
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X 0 * MvPolynomial.X 1))
        (genericPoint _) (genericPoint_mem_basicOpen_mul baseField)
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X 0 * MvPolynomial.X 1)
          (HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
            (X_mem 1 baseField index) coordinateEquation ((chartCoord baseField chart).symm polynomial))) := by
  show (projectiveLine baseField).presheaf.germ
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)) (genericPoint _) _
    ((Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (MvPolynomial.X chart)
      (X_mem 1 baseField chart) Nat.one_pos).hom ((chartCoord baseField chart).symm polynomial)) = _
  rw [Proj.basicOpenIsoAway_hom]
  have equality := congrArg (fun map => map.hom ((chartCoord baseField chart).symm polynomial))
    (Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (X_mem 1 baseField index) coordinateEquation)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at equality
  erw [equality]
  exact ((projectiveLine baseField).presheaf.germ_res_apply (homOfLE _) (genericPoint _) _ _).symm

theorem chartCoord_symm_C (chart : Fin 2) (scalar : baseField) :
    (chartCoord baseField chart).symm (Polynomial.C scalar) =
      HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) _
        (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0) scalar) := by
  rw [RingEquiv.symm_apply_eq]
  exact (chartCoord_algebraMap baseField chart scalar).symm

theorem chartCoord_symm_X (chart index : Fin 2) (coordinateEquation : index ≠ chart) :
    (chartCoord baseField chart).symm Polynomial.X =
      HomogeneousLocalization.Away.isLocalizationElem (X_mem 1 baseField chart) (X_mem 1 baseField index) := by
  rw [RingEquiv.symm_apply_eq]
  exact (chartCoord_isLocalizationElem baseField chart index coordinateEquation).symm

theorem chartSectionHom_C (scalar : baseField) :
    chartSectionHom baseField 0 (Polynomial.C scalar) = chartSectionHom baseField 1 (Polynomial.C scalar) := by
  rw [chartSectionHom_eq_germ_mul baseField 0 1 rfl, chartSectionHom_eq_germ_mul baseField 1 0 (mul_comm _ _),
    chartCoord_symm_C, chartCoord_symm_C, HomogeneousLocalization.awayMap_fromZeroRingHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom]

theorem awayMap_isLocalizationElem_mul :
    HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (X_mem 1 baseField 1)
        (rfl : MvPolynomial.X 0 * MvPolynomial.X 1 = (MvPolynomial.X 0 : MvPolynomial (Fin 2) baseField) * MvPolynomial.X 1)
        (HomogeneousLocalization.Away.isLocalizationElem (X_mem 1 baseField 0) (X_mem 1 baseField 1)) *
      HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) (X_mem 1 baseField 0)
        (mul_comm (MvPolynomial.X 0 : MvPolynomial (Fin 2) baseField) (MvPolynomial.X 1))
        (HomogeneousLocalization.Away.isLocalizationElem (X_mem 1 baseField 1) (X_mem 1 baseField 0)) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one, HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, Submonoid.coe_one, one_mul, mul_one]
  ring

theorem chartSectionHom_X_mul_chartSectionHom_X :
    chartSectionHom baseField 0 Polynomial.X * chartSectionHom baseField 1 Polynomial.X = 1 := by
  rw [chartSectionHom_eq_germ_mul baseField 0 1 rfl, chartSectionHom_eq_germ_mul baseField 1 0 (mul_comm _ _)]
  erw [← map_mul, ← map_mul]
  rw [chartCoord_symm_X baseField 0 1 one_ne_zero, chartCoord_symm_X baseField 1 0 zero_ne_one,
    awayMap_isLocalizationElem_mul, map_one, map_one]

theorem residueDegree_eq_one_of_isOpenImmersion {source target : Scheme.{u}} (morphism : source ⟶ target)
    [IsOpenImmersion morphism] (point : source) : morphism.residueDegree point = 1 := by
  let : Algebra (target.residueField (morphism.base point)) (source.residueField point) :=
    (morphism.residueFieldMap point).hom.toAlgebra
  change Module.finrank (target.residueField (morphism.base point)) (source.residueField point) = 1
  exact Module.finrank_of_bijective_algebraMap
    ((asIso (morphism.residueFieldMap point)).commRingCatIsoToRingEquiv.bijective)

theorem residueDegree_chartι (chart : Fin 2) (point : Spec (CommRingCat.of (Polynomial baseField))) :
    Scheme.Hom.residueDegree (ProjectiveLinePrincipalDegree.structureMap baseField) (chartι baseField chart point) =
      (AffineLinePrincipalOrder.structureMap baseField).residueDegree point := by
  have equality := Intersection.residueDegree_comp (chartι baseField chart)
    (ProjectiveLinePrincipalDegree.structureMap baseField) point
  rw [chartι_comp_structureMap, residueDegree_eq_one_of_isOpenImmersion (chartι baseField chart), mul_one] at equality
  exact equality.symm

theorem ord_chartι (chart : Fin 2) (rational : (projectiveLine baseField).functionField)
    (point : Spec (CommRingCat.of (Polynomial baseField))) :
    (projectiveLine baseField).ord rational (chartι baseField chart point) =
      (Spec (CommRingCat.of (Polynomial baseField))).ord
        (OpenImmersionOrder.functionFieldMap (chartι baseField chart) rational) point :=
  (OpenImmersionOrder.ord_functionFieldMap (chartι baseField chart) rational point).symm

theorem chartSectionHom_ne_zero (chart : Fin 2) {numerator : Polynomial baseField} (nonzero : numerator ≠ 0) :
    chartSectionHom baseField chart numerator ≠ 0 := by
  intro firstEvaluation
  apply nonzero
  apply polyToFunctionField_injective baseField
  rw [map_zero, ← functionFieldMap_chartι_chartSectionHom, firstEvaluation, map_zero]

theorem chartSectionHom_zero_eq (numerator : Polynomial baseField) :
    chartSectionHom baseField 0 numerator =
      chartSectionHom baseField 1 numerator.reverse * chartSectionHom baseField 0 Polynomial.X ^ numerator.natDegree := by
  let : Invertible (chartSectionHom baseField 0 Polynomial.X) := ⟨chartSectionHom baseField 1 Polynomial.X,
    by rw [mul_comm]; exact chartSectionHom_X_mul_chartSectionHom_X baseField,
    chartSectionHom_X_mul_chartSectionHom_X baseField⟩
  have inverseEquation : ⅟(chartSectionHom baseField 0 Polynomial.X) = chartSectionHom baseField 1 Polynomial.X := rfl
  have reverseEquation := Polynomial.eval₂_reverse_mul_pow ((chartSectionHom baseField 0).comp Polynomial.C)
    (chartSectionHom baseField 0 Polynomial.X) numerator
  have firstEvaluation : ∀ polynomial : Polynomial baseField, Polynomial.eval₂ ((chartSectionHom baseField 0).comp Polynomial.C)
      (chartSectionHom baseField 0 Polynomial.X) polynomial = chartSectionHom baseField 0 polynomial := fun polynomial => by
    conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq polynomial]
    simp only [Polynomial.eval₂_eq_sum, Polynomial.sum, map_sum, map_mul, map_pow,
      RingHom.comp_apply]
  have secondEvaluation : ∀ polynomial : Polynomial baseField, Polynomial.eval₂ ((chartSectionHom baseField 0).comp Polynomial.C)
      (⅟(chartSectionHom baseField 0 Polynomial.X)) polynomial = chartSectionHom baseField 1 polynomial := fun polynomial => by
    conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq polynomial]
    simp only [Polynomial.eval₂_eq_sum, Polynomial.sum, map_sum, map_mul, map_pow,
      RingHom.comp_apply, chartSectionHom_C, inverseEquation]
  rw [firstEvaluation, secondEvaluation] at reverseEquation
  exact reverseEquation.symm

theorem functionFieldMap_chartι_one_chartSectionHom_zero (numerator : Polynomial baseField) :
    OpenImmersionOrder.functionFieldMap (chartι baseField 1) (chartSectionHom baseField 0 numerator) =
      polyToFunctionField baseField numerator.reverse / polyToFunctionField baseField Polynomial.X ^ numerator.natDegree := by
  rw [chartSectionHom_zero_eq, map_mul, map_pow, functionFieldMap_chartι_chartSectionHom]
  have reciprocalEquation : OpenImmersionOrder.functionFieldMap (chartι baseField 1) (chartSectionHom baseField 0 Polynomial.X) *
      polyToFunctionField baseField Polynomial.X = 1 := by
    rw [← functionFieldMap_chartι_chartSectionHom baseField 1, ← map_mul,
      chartSectionHom_X_mul_chartSectionHom_X, map_one]
  rw [eq_inv_of_mul_eq_one_left reciprocalEquation, inv_pow, div_eq_mul_inv]

theorem finite_support_chartSectionHom_zero {numerator : Polynomial baseField} (nonzero : numerator ≠ 0) :
    (Function.support fun point : (projectiveLine baseField) => (projectiveLine baseField).ord (chartSectionHom baseField 0 numerator) point * ((Scheme.Hom.residueDegree (ProjectiveLinePrincipalDegree.structureMap baseField) point : ℕ) : ℤ)).Finite := by
  have affineSupport := finite_support_ord baseField numerator nonzero
  refine Set.Finite.subset ((affineSupport.image (chartι baseField 0)).insert (inftyPoint baseField)) ?_
  intro point nonzeroOrder
  rcases mem_range_chartι_zero_or_eq_inftyPoint baseField point with ⟨point, rfl⟩ | rfl
  · refine Set.mem_insert_of_mem _ ⟨point, ?_, rfl⟩
    intro zeroOrder
    apply nonzeroOrder
    show (projectiveLine baseField).ord (chartSectionHom baseField 0 numerator) (chartι baseField 0 point) * _ = 0
    rw [ord_chartι, functionFieldMap_chartι_chartSectionHom]
    simp only at zeroOrder
    rw [zeroOrder, zero_mul]
  · exact Set.mem_insert _ _

theorem finsum_ord_chartSectionHom_zero {numerator : Polynomial baseField} (nonzero : numerator ≠ 0) :
    ∑ᶠ point : (projectiveLine baseField), (projectiveLine baseField).ord (chartSectionHom baseField 0 numerator) point * ((Scheme.Hom.residueDegree (ProjectiveLinePrincipalDegree.structureMap baseField) point : ℕ) : ℤ) = 0 := by
  set weightedOrder : (projectiveLine baseField) → ℤ := fun point => (projectiveLine baseField).ord (chartSectionHom baseField 0 numerator) point * ((Scheme.Hom.residueDegree (ProjectiveLinePrincipalDegree.structureMap baseField) point : ℕ) : ℤ) with weightedOrderEquation
  have universeEquation : (Set.univ : Set (projectiveLine baseField)) = insert (inftyPoint baseField) (Set.range (chartι baseField 0)) := by
    ext point
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_range, true_iff]
    rcases mem_range_chartι_zero_or_eq_inftyPoint baseField point with rational | rational
    · exact Or.inr rational
    · exact Or.inl rational
  have finiteSupport := finite_support_chartSectionHom_zero baseField nonzero
  calc ∑ᶠ point : (projectiveLine baseField), weightedOrder point = ∑ᶠ point ∈ (Set.univ : Set (projectiveLine baseField)), weightedOrder point := (finsum_mem_univ weightedOrder).symm
    _ = ∑ᶠ point ∈ insert (inftyPoint baseField) (Set.range (chartι baseField 0)), weightedOrder point := by rw [universeEquation]
    _ = weightedOrder (inftyPoint baseField) + ∑ᶠ point ∈ Set.range (chartι baseField 0), weightedOrder point :=
        finsum_mem_insert' weightedOrder (inftyPoint_not_mem_range_chartι_zero baseField) (finiteSupport.subset Set.inter_subset_right)
    _ = weightedOrder (inftyPoint baseField) + ∑ᶠ point : Spec (CommRingCat.of (Polynomial baseField)), weightedOrder (chartι baseField 0 point) := by
        rw [finsum_mem_range (chartι baseField 0).isOpenEmbedding.injective]
    _ = -(numerator.natDegree : ℤ) + numerator.natDegree := by
        congr 1
        · simp only [weightedOrderEquation, inftyPoint, ord_chartι, residueDegree_chartι,
            functionFieldMap_chartι_one_chartSectionHom_zero, reciprocal_polynomial_ord_originPoint baseField numerator nonzero,
            residueDegree_originPoint, Nat.cast_one, mul_one]
        · simp only [weightedOrderEquation, ord_chartι, residueDegree_chartι, functionFieldMap_chartι_chartSectionHom]
          exact finsum_ord_mul_residueDegree baseField numerator nonzero
    _ = 0 := by ring

theorem sum_ord_mul_residueDegree_eq_zero_proj
    (rational : (projectiveLine baseField).functionFieldˣ) :
    ∑ᶠ point : (projectiveLine baseField),
      Scheme.ord (rational : (projectiveLine baseField).functionField) point *
        ((Scheme.Hom.residueDegree
          (ProjectiveLinePrincipalDegree.structureMap baseField) point : ℕ) : ℤ) = 0 := by
  let _ := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Polynomial baseField))
  have _ := AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of (Polynomial baseField))
  set chartMap := OpenImmersionOrder.functionFieldMap (chartι baseField 0) with chartMapEquation
  obtain ⟨numerator, denominator, denominatorRegular, fractionEquation⟩ := IsFractionRing.div_surjective (A := CommRingCat.of (Polynomial baseField))
    (chartMap (rational : (projectiveLine baseField).functionField))
  have denominatorNonzero : denominator ≠ 0 := nonZeroDivisors.ne_zero denominatorRegular
  have mappedNonzero : chartMap (rational : (projectiveLine baseField).functionField) ≠ 0 := by
    rw [map_ne_zero_iff chartMap chartMap.injective]
    exact rational.ne_zero
  have numeratorNonzero : numerator ≠ 0 := by
    rintro rfl
    apply mappedNonzero
    rw [← fractionEquation, map_zero, zero_div]
  have rationalEquation : (rational : (projectiveLine baseField).functionField) = chartSectionHom baseField 0 numerator / chartSectionHom baseField 0 denominator := by
    apply chartMap.injective
    rw [map_div₀, chartMapEquation, functionFieldMap_chartι_chartSectionHom, functionFieldMap_chartι_chartSectionHom]
    exact fractionEquation.symm
  have numeratorSupport := finite_support_chartSectionHom_zero baseField numeratorNonzero
  have denominatorSupport := finite_support_chartSectionHom_zero baseField denominatorNonzero
  have pointwise : ∀ point : (projectiveLine baseField), (projectiveLine baseField).ord (rational : (projectiveLine baseField).functionField) point * ((Scheme.Hom.residueDegree (ProjectiveLinePrincipalDegree.structureMap baseField) point : ℕ) : ℤ) =
      (projectiveLine baseField).ord (chartSectionHom baseField 0 numerator) point * ((Scheme.Hom.residueDegree (ProjectiveLinePrincipalDegree.structureMap baseField) point : ℕ) : ℤ) - (projectiveLine baseField).ord (chartSectionHom baseField 0 denominator) point * ((Scheme.Hom.residueDegree (ProjectiveLinePrincipalDegree.structureMap baseField) point : ℕ) : ℤ) := by
    intro point
    rw [rationalEquation, Scheme.ord_div_eq_sub (chartSectionHom_ne_zero baseField 0 numeratorNonzero) (chartSectionHom_ne_zero baseField 0 denominatorNonzero),
      sub_mul]
  rw [finsum_congr pointwise, finsum_sub_distrib numeratorSupport denominatorSupport, finsum_ord_chartSectionHom_zero baseField numeratorNonzero,
    finsum_ord_chartSectionHom_zero baseField denominatorNonzero, sub_zero]

theorem principal_weighted_degree_eq_zero (rational : (projectiveLine baseField).functionField)
    (nonzero : rational ≠ 0) :
    ∑ᶠ point : projectiveLine baseField,
      (projectiveLine baseField).ord rational point *
        ((ProjectiveLinePrincipalDegree.structureMap baseField).residueDegree point : ℤ) = 0 :=
  sum_ord_mul_residueDegree_eq_zero_proj baseField (Units.mk0 rational nonzero)

end AlgebraicGeometry.ProjectiveLinePrincipalDegree
