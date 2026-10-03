module

public import BondalThomsen.Toric.Scheme.ValuationConeSelection
public import BondalThomsen.DeepFan.StarDeep
public import BondalThomsen.Toric.Positivity.StrictSupportProjectivity
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.Pullback
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Topology.Sheaves.LocalPredicate

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

attribute [local instance] MvPolynomial.gradedAlgebra

variable (Index : Type)

noncomputable section

abbrev polynomialDegreeOneProj :=
  Proj (MvPolynomial.homogeneousSubmodule Index 𝕜)

abbrev polynomialDegreeOnePointLocalization (point : polynomialDegreeOneProj 𝕜 Index) :=
  Localization point.asHomogeneousIdeal.toIdeal.primeCompl

def polynomialDegreeOneIsFraction {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (section_value : ∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) : Prop :=
  ∃ (degree : ℕ) (numerator : MvPolynomial.homogeneousSubmodule Index 𝕜 (degree + 1))
    (denominator : MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (denominator_nonzero : ∀ point : open_set, denominator.val ∉ point.val.asHomogeneousIdeal),
    ∀ point : open_set, section_value point =
      Localization.mk numerator.val ⟨denominator.val, denominator_nonzero point⟩

def polynomialDegreeOneFractionPrelocal :
    PrelocalPredicate (fun point : polynomialDegreeOneProj 𝕜 Index =>
      polynomialDegreeOnePointLocalization 𝕜 Index point) where
  pred := polynomialDegreeOneIsFraction 𝕜 Index
  res := by
    rintro smaller larger inclusion section_value
      ⟨degree, numerator, denominator, denominator_nonzero, equal⟩
    exact ⟨degree, numerator, denominator, fun point => denominator_nonzero (inclusion point),
      fun point => equal (inclusion point)⟩

def polynomialDegreeOneLocallyFraction :
    LocalPredicate (fun point : polynomialDegreeOneProj 𝕜 Index =>
      polynomialDegreeOnePointLocalization 𝕜 Index point) :=
  (polynomialDegreeOneFractionPrelocal 𝕜 Index).sheafify

noncomputable def polynomialDegreeOneTypeSheaf :
    TopCat.Sheaf (Type) (polynomialDegreeOneProj 𝕜 Index).toTopCat :=
  subsheafToTypes (polynomialDegreeOneLocallyFraction 𝕜 Index)

theorem polynomialDegreeOneLocallyFraction_zero
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    (polynomialDegreeOneLocallyFraction 𝕜 Index).pred
      (0 : ∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) := by
  apply PrelocalPredicate.sheafifyOf
  refine ⟨0, ⟨0, Submodule.zero_mem _⟩, ⟨1, SetLike.one_mem_graded _⟩,
    fun point => point.val.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, ?_⟩
  intro point
  exact (Localization.mk_zero _).symm

theorem polynomialDegreeOneLocallyFraction_add
    {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (first second : ∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val)
    (first_regular : (polynomialDegreeOneLocallyFraction 𝕜 Index).pred first)
    (second_regular : (polynomialDegreeOneLocallyFraction 𝕜 Index).pred second) :
    (polynomialDegreeOneLocallyFraction 𝕜 Index).pred (first + second) := by
  apply (polynomialDegreeOneFractionPrelocal 𝕜 Index).sheafify_inductionOn₂'
    (polynomialDegreeOneFractionPrelocal 𝕜 Index) (polynomialDegreeOneFractionPrelocal 𝕜 Index)
    (fun first_value second_value => first_value + second_value) _ first_regular second_regular
  rintro first_open second_open first_value second_value
    ⟨first_degree, first_num, first_den, first_nonzero, first_equal⟩
    ⟨second_degree, second_num, second_den, second_nonzero, second_equal⟩
  refine ⟨first_degree + second_degree,
    ⟨first_den.val * second_num.val + second_den.val * first_num.val, ?_⟩,
    ⟨first_den.val * second_den.val, SetLike.mul_mem_graded first_den.property second_den.property⟩,
    fun point => point.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (first_nonzero ⟨point.val, point.property.1⟩) (second_nonzero ⟨point.val, point.property.2⟩), ?_⟩
  · apply Submodule.add_mem
    · simpa only [Nat.add_assoc] using
        (SetLike.mul_mem_graded first_den.property second_num.property)
    · simpa only [← Nat.add_assoc, Nat.add_comm second_degree first_degree] using
        (SetLike.mul_mem_graded second_den.property first_num.property)
  · intro point
    dsimp only
    rw [first_equal, second_equal, Localization.add_mk]
    rfl

theorem polynomialDegreeOneLocallyFraction_neg
    {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (section_value : ∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val)
    (regular : (polynomialDegreeOneLocallyFraction 𝕜 Index).pred section_value) :
    (polynomialDegreeOneLocallyFraction 𝕜 Index).pred (-section_value) := by
  apply (polynomialDegreeOneFractionPrelocal 𝕜 Index).sheafify_inductionOn'
    (fun value => -value) _ regular
  rintro local_open local_value ⟨degree, numerator, denominator, denominator_nonzero, equal⟩
  refine ⟨degree, -numerator, denominator, denominator_nonzero, ?_⟩
  intro point
  simp only [equal, Localization.neg_mk, Submodule.coe_neg]

noncomputable def polynomialDegreeOneSectionAddSubgroup
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    AddSubgroup (∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) where
  carrier := {section_value | (polynomialDegreeOneLocallyFraction 𝕜 Index).pred section_value}
  zero_mem' := polynomialDegreeOneLocallyFraction_zero 𝕜 Index open_set
  add_mem' := polynomialDegreeOneLocallyFraction_add 𝕜 Index _ _
  neg_mem' := polynomialDegreeOneLocallyFraction_neg 𝕜 Index _

noncomputable def polynomialDegreeOneScalarEvaluation
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    Γ(polynomialDegreeOneProj 𝕜 Index, open_set) →+*
      (∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) where
  toFun scalar point := (scalar.val point).val
  map_zero' := by funext point; exact HomogeneousLocalization.val_zero
  map_one' := by funext point; exact HomogeneousLocalization.val_one
  map_add' first second := by funext point; exact HomogeneousLocalization.val_add _ _
  map_mul' first second := by funext point; exact HomogeneousLocalization.val_mul _ _

variable {𝕜} in
noncomputable instance polynomialDegreeOnePointwiseModule
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    Module Γ(polynomialDegreeOneProj 𝕜 Index, open_set)
      (∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) :=
  Module.compHom _ (polynomialDegreeOneScalarEvaluation 𝕜 Index open_set)

theorem polynomialDegreeOneLocallyFraction_smul
    {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (scalar : Γ(polynomialDegreeOneProj 𝕜 Index, open_set))
    (section_value : ∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val)
    (regular : (polynomialDegreeOneLocallyFraction 𝕜 Index).pred section_value) :
    (polynomialDegreeOneLocallyFraction 𝕜 Index).pred (scalar • section_value) := by
  apply (ProjectiveSpectrum.StructureSheaf.isFractionPrelocal
    (MvPolynomial.homogeneousSubmodule Index 𝕜)).sheafify_inductionOn₂'
    (polynomialDegreeOneFractionPrelocal 𝕜 Index) (polynomialDegreeOneFractionPrelocal 𝕜 Index)
    (fun scalar_value section_value => scalar_value.val * section_value) _ scalar.property regular
  rintro scalar_open section_open scalar_value section_value
    ⟨scalar_degree, scalar_num, scalar_den, scalar_nonzero, scalar_equal⟩
    ⟨section_degree, section_num, section_den, section_nonzero, section_equal⟩
  refine ⟨scalar_degree + section_degree,
    ⟨scalar_num.val * section_num.val, ?_⟩,
    ⟨scalar_den.val * section_den.val, SetLike.mul_mem_graded scalar_den.property section_den.property⟩,
    fun point => point.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (scalar_nonzero ⟨point.val, point.property.1⟩) (section_nonzero ⟨point.val, point.property.2⟩), ?_⟩
  · simpa only [Nat.add_assoc] using
      (SetLike.mul_mem_graded scalar_num.property section_num.property)
  · intro point
    dsimp only
    rw [scalar_equal, section_equal, HomogeneousLocalization.val_mk, Localization.mk_mul]
    rfl

noncomputable def polynomialDegreeOneSectionSubmodule
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    Submodule Γ(polynomialDegreeOneProj 𝕜 Index, open_set)
      (∀ point : open_set, polynomialDegreeOnePointLocalization 𝕜 Index point.val) where
  toAddSubmonoid := (polynomialDegreeOneSectionAddSubgroup 𝕜 Index open_set).toAddSubmonoid
  smul_mem' scalar section_value regular :=
    polynomialDegreeOneLocallyFraction_smul 𝕜 Index scalar section_value regular

noncomputable def polynomialDegreeOnePresheaf :
    (polynomialDegreeOneProj 𝕜 Index).PresheafOfModules where
  obj open_set := ModuleCat.of _ (polynomialDegreeOneSectionSubmodule 𝕜 Index open_set.unop)
  map {larger smaller} inclusion := ModuleCat.semilinearMapAddEquiv _ _ _
    (show polynomialDegreeOneSectionSubmodule 𝕜 Index larger.unop →ₛₗ[
      ((polynomialDegreeOneProj 𝕜 Index).ringCatSheaf.obj.map inclusion).hom]
        (polynomialDegreeOneSectionSubmodule 𝕜) Index smaller.unop from
    { toFun section_value := ⟨fun point => section_value.val (inclusion.unop point),
        (polynomialDegreeOneLocallyFraction 𝕜 Index).res inclusion.unop section_value.val section_value.property⟩
      map_add' first second := rfl
      map_smul' scalar section_value := rfl })
  map_id open_set := by ext section_value; rfl
  map_comp first second := by ext section_value; rfl

noncomputable def polynomialDegreeOnePresheafForgetIso :
    (polynomialDegreeOnePresheaf 𝕜 Index).presheaf ⋙ forget AddCommGrpCat ≅
      (polynomialDegreeOneTypeSheaf 𝕜 Index).obj :=
  NatIso.ofComponents (fun open_set => Iso.refl _) (by intros; rfl)

theorem polynomialDegreeOnePresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (polynomialDegreeOnePresheaf 𝕜 Index).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  exact TopCat.Presheaf.isSheaf_of_iso
    (polynomialDegreeOnePresheafForgetIso 𝕜 Index).symm (polynomialDegreeOneTypeSheaf 𝕜 Index).property

noncomputable def polynomialProjDegreeOneSheaf :
    (polynomialDegreeOneProj 𝕜 Index).Modules :=
  ⟨polynomialDegreeOnePresheaf 𝕜 Index, polynomialDegreeOnePresheaf_isSheaf 𝕜 Index⟩

abbrev polynomialDegreeOneCoordinateOpen (coordinate : Index) :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X coordinate)

abbrev polynomialDegreeZeroPointLocalization (point : polynomialDegreeOneProj 𝕜 Index) :=
  HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule Index 𝕜)
    point.asHomogeneousIdeal.toIdeal

noncomputable def polynomialDegreeOnePointCoefficient
    (point : polynomialDegreeOneProj 𝕜 Index) (coordinate : Index)
    (coordinate_nonzero : MvPolynomial.X coordinate ∉ point.asHomogeneousIdeal)
    (degree : ℕ) (numerator : MvPolynomial.homogeneousSubmodule Index 𝕜 (degree + 1))
    (denominator : MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (denominator_nonzero : denominator.val ∉ point.asHomogeneousIdeal) :
    polynomialDegreeZeroPointLocalization 𝕜 Index point :=
  HomogeneousLocalization.mk
    ⟨degree + 1, numerator,
      ⟨denominator.val * MvPolynomial.X coordinate,
        SetLike.mul_mem_graded denominator.property (MvPolynomial.isHomogeneous_X 𝕜 coordinate)⟩,
      point.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem denominator_nonzero coordinate_nonzero⟩

theorem polynomialDegreeOnePointCoefficient_mul_coordinate
    (point : polynomialDegreeOneProj 𝕜 Index) (coordinate : Index)
    (coordinate_nonzero : MvPolynomial.X coordinate ∉ point.asHomogeneousIdeal)
    (degree : ℕ) (numerator : MvPolynomial.homogeneousSubmodule Index 𝕜 (degree + 1))
    (denominator : MvPolynomial.homogeneousSubmodule Index 𝕜 degree)
    (denominator_nonzero : denominator.val ∉ point.asHomogeneousIdeal) :
    (polynomialDegreeOnePointCoefficient 𝕜 Index point coordinate coordinate_nonzero degree
        numerator denominator denominator_nonzero).val *
      algebraMap (MvPolynomial Index 𝕜) (polynomialDegreeOnePointLocalization 𝕜 Index point)
        (MvPolynomial.X coordinate) =
      Localization.mk numerator.val ⟨denominator.val, denominator_nonzero⟩ := by
  rw [polynomialDegreeOnePointCoefficient, HomogeneousLocalization.val_mk,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, mul_one]
  ring

theorem polynomialDegreeOneCoordinate_isUnit
    (point : polynomialDegreeOneProj 𝕜 Index) (coordinate : Index)
    (coordinate_nonzero : MvPolynomial.X coordinate ∉ point.asHomogeneousIdeal) :
    IsUnit (algebraMap (MvPolynomial Index 𝕜) (polynomialDegreeOnePointLocalization 𝕜 Index point)
      (MvPolynomial.X coordinate)) :=
  IsLocalization.map_units (M := point.asHomogeneousIdeal.toIdeal.primeCompl)
    (polynomialDegreeOnePointLocalization 𝕜 Index point) ⟨MvPolynomial.X coordinate, coordinate_nonzero⟩

theorem polynomialDegreeOneChartCoefficient_exists
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)
    (section_value : Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set)) (point : open_set) :
    ∃ coefficient : polynomialDegreeZeroPointLocalization 𝕜 Index point.val,
      coefficient.val * algebraMap (MvPolynomial Index 𝕜)
        (polynomialDegreeOnePointLocalization 𝕜 Index point.val) (MvPolynomial.X coordinate) =
          section_value.val point := by
  obtain ⟨local_open, point_member, local_inclusion, degree, numerator, denominator,
    denominator_nonzero, equal⟩ := section_value.property point
  refine ⟨polynomialDegreeOnePointCoefficient 𝕜 Index point.val coordinate (inclusion point.property)
    degree numerator denominator (denominator_nonzero ⟨point.val, point_member⟩), ?_⟩
  rw [polynomialDegreeOnePointCoefficient_mul_coordinate]
  exact (equal ⟨point.val, point_member⟩).symm

noncomputable def polynomialDegreeOneChartCoefficientValue
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)
    (section_value : Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set)) (point : open_set) :
    polynomialDegreeZeroPointLocalization 𝕜 Index point.val :=
  (polynomialDegreeOneChartCoefficient_exists 𝕜 Index coordinate inclusion section_value point).choose

theorem polynomialDegreeOneChartCoefficientValue_spec
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)
    (section_value : Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set)) (point : open_set) :
    (polynomialDegreeOneChartCoefficientValue 𝕜 Index coordinate inclusion section_value point).val *
        algebraMap (MvPolynomial Index 𝕜) (polynomialDegreeOnePointLocalization 𝕜 Index point.val)
          (MvPolynomial.X coordinate) = section_value.val point :=
  (polynomialDegreeOneChartCoefficient_exists 𝕜 Index coordinate inclusion section_value point).choose_spec

theorem polynomialDegreeOneChartCoefficientValue_locallyFraction
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)
    (section_value : Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set)) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction
      (MvPolynomial.homogeneousSubmodule Index 𝕜)).pred
        (polynomialDegreeOneChartCoefficientValue 𝕜 Index coordinate inclusion section_value) := by
  intro point
  obtain ⟨local_open, point_member, local_inclusion, degree, numerator, denominator,
    denominator_nonzero, equal⟩ := section_value.property point
  refine ⟨local_open, point_member, local_inclusion, degree + 1, numerator,
    ⟨denominator.val * MvPolynomial.X coordinate,
      SetLike.mul_mem_graded denominator.property (MvPolynomial.isHomogeneous_X 𝕜 coordinate)⟩,
    fun local_point => local_point.val.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (denominator_nonzero local_point) (inclusion (local_inclusion local_point).property), ?_⟩
  intro local_point
  apply HomogeneousLocalization.val_injective _
  apply (polynomialDegreeOneCoordinate_isUnit 𝕜 Index local_point.val coordinate
    (inclusion (local_inclusion local_point).property)).mul_right_cancel
  dsimp only
  erw [polynomialDegreeOneChartCoefficientValue_spec]
  change section_value.val (local_inclusion local_point) =
    (polynomialDegreeOnePointCoefficient 𝕜 Index local_point.val coordinate
      (inclusion (local_inclusion local_point).property) degree
      numerator denominator (denominator_nonzero local_point)).val * _
  rw [polynomialDegreeOnePointCoefficient_mul_coordinate]
  exact equal local_point

noncomputable def polynomialDegreeOneChartCoefficient
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)
    (section_value : Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set)) :
    Γ(polynomialDegreeOneProj 𝕜 Index, open_set) :=
  ⟨polynomialDegreeOneChartCoefficientValue 𝕜 Index coordinate inclusion section_value,
    polynomialDegreeOneChartCoefficientValue_locallyFraction 𝕜 Index coordinate inclusion section_value⟩

theorem polynomialDegreeOneChartFrame_locallyFraction
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (scalar : Γ(polynomialDegreeOneProj 𝕜 Index, open_set)) :
    (polynomialDegreeOneLocallyFraction 𝕜 Index).pred (fun point : open_set =>
      (scalar.val point).val * algebraMap (MvPolynomial Index 𝕜)
        (polynomialDegreeOnePointLocalization 𝕜 Index point.val) (MvPolynomial.X coordinate)) := by
  intro point
  obtain ⟨local_open, point_member, local_inclusion, degree, numerator, denominator,
    denominator_nonzero, equal⟩ := scalar.property point
  refine ⟨local_open, point_member, local_inclusion, degree,
    ⟨numerator.val * MvPolynomial.X coordinate,
      SetLike.mul_mem_graded numerator.property (MvPolynomial.isHomogeneous_X 𝕜 coordinate)⟩,
    denominator, denominator_nonzero, ?_⟩
  intro local_point
  dsimp only
  have scalar_equal := equal local_point
  dsimp only at scalar_equal
  erw [scalar_equal, HomogeneousLocalization.val_mk, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul]
  simp only [mul_one]

noncomputable def polynomialDegreeOneChartFrame
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (scalar : Γ(polynomialDegreeOneProj 𝕜 Index, open_set)) :
    Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set) :=
  ⟨fun point => (scalar.val point).val * algebraMap (MvPolynomial Index 𝕜)
      (polynomialDegreeOnePointLocalization 𝕜 Index point.val) (MvPolynomial.X coordinate),
    polynomialDegreeOneChartFrame_locallyFraction 𝕜 Index coordinate scalar⟩

noncomputable def polynomialDegreeOneChartSectionsLinearEquiv
    (coordinate : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate) :
    Γ(polynomialDegreeOneProj 𝕜 Index, open_set) ≃ₗ[Γ(polynomialDegreeOneProj 𝕜 Index, open_set)]
      Γ(polynomialProjDegreeOneSheaf 𝕜 Index, open_set) where
  toFun := polynomialDegreeOneChartFrame 𝕜 Index coordinate
  invFun := polynomialDegreeOneChartCoefficient 𝕜 Index coordinate inclusion
  map_add' first second := by
    apply Subtype.ext
    funext point
    dsimp [polynomialDegreeOneChartFrame]
    erw [Proj.add_apply, HomogeneousLocalization.val_add]
    change _ = (first.val point).val * _ + (second.val point).val * _
    exact add_mul _ _ _
  map_smul' scalar coefficient := by
    apply Subtype.ext
    funext point
    dsimp [polynomialDegreeOneChartFrame, polynomialDegreeOnePointwiseModule,
      Module.compHom, polynomialDegreeOneScalarEvaluation]
    erw [Proj.mul_apply, HomogeneousLocalization.val_mul]
    change _ = (scalar.val point).val * ((coefficient.val point).val * _)
    exact mul_assoc _ _ _
  left_inv coefficient := by
    apply Subtype.ext
    funext point
    apply HomogeneousLocalization.val_injective _
    apply (polynomialDegreeOneCoordinate_isUnit 𝕜 Index point.val coordinate
      (inclusion point.property)).mul_right_cancel
    exact polynomialDegreeOneChartCoefficientValue_spec 𝕜 Index coordinate inclusion _ point
  right_inv section_value := by
    apply Subtype.ext
    funext point
    exact polynomialDegreeOneChartCoefficientValue_spec 𝕜 Index coordinate inclusion section_value point

noncomputable def polynomialDegreeOneCoordinateOpenSheafFrame (coordinate : Index) :
    SheafOfModules.unit ((polynomialDegreeOneProj 𝕜 Index).ringCatSheaf.over
      (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)) ≅
    (polynomialProjDegreeOneSheaf 𝕜 Index).over (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun local_open =>
    (polynomialDegreeOneChartSectionsLinearEquiv 𝕜 Index coordinate
      local_open.unop.hom.le).toModuleIso) ?_
  intro larger smaller inclusion
  ext
  apply Subtype.ext
  funext point
  rfl

theorem polynomialDegreeOneCoordinateOpen_cover :
    IsOpenCover (polynomialDegreeOneCoordinateOpen 𝕜 Index) := by
  apply IsOpenCover.mk
  apply Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule Index 𝕜)
    (MvPolynomial.X : Index → MvPolynomial Index 𝕜)
    (fun coordinate => ⟨1, MvPolynomial.isHomogeneous_X 𝕜 coordinate⟩)
  apply top_unique
  intro polynomial
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
      intro _
      exact Subalgebra.algebraMap_mem
        (Algebra.adjoin (MvPolynomial.homogeneousSubmodule Index 𝕜 0) (Set.range MvPolynomial.X))
        (⟨MvPolynomial.C scalar, MvPolynomial.isHomogeneous_C Index scalar⟩ :
          MvPolynomial.homogeneousSubmodule Index 𝕜 0)
  | add first second first_member second_member =>
      intro _
      exact Subalgebra.add_mem _ (first_member trivial) (second_member trivial)
  | mul_X polynomial coordinate polynomial_member =>
      intro _
      exact Subalgebra.mul_mem _ (polynomial_member trivial) (Algebra.subset_adjoin ⟨coordinate, rfl⟩)

noncomputable def polynomialProjDegreeOneLocalTrivializations :
    TauCeti.SheafOfModules.LocalTrivializations (polynomialProjDegreeOneSheaf 𝕜 Index) :=
  TauCeti.AlgebraicGeometry.SheafOfModules.LocalTrivializations.ofIsOpenCover
    (polynomialDegreeOneProj 𝕜 Index) (polynomialDegreeOneCoordinateOpen 𝕜 Index)
      (polynomialDegreeOneCoordinateOpen_cover 𝕜 Index)
        (polynomialDegreeOneCoordinateOpenSheafFrame 𝕜 Index)

variable {𝕜} in
instance polynomialProjDegreeOneSheaf_isInvertible :
    TauCeti.SheafOfModules.IsInvertible (polynomialProjDegreeOneSheaf 𝕜 Index) :=
  (polynomialProjDegreeOneLocalTrivializations 𝕜 Index).isInvertible

noncomputable def polynomialProjDegreeOneGlobalCoordinate (coordinate : Index) :
    Γ(polynomialProjDegreeOneSheaf 𝕜 Index, ⊤) :=
  polynomialDegreeOneChartFrame 𝕜 Index coordinate 1

theorem polynomialProjDegreeOneGlobalCoordinate_restrict (coordinate : Index)
    (open_set : (polynomialDegreeOneProj 𝕜 Index).Opens) :
    (polynomialProjDegreeOneSheaf 𝕜 Index).presheaf.map (homOfLE le_top).op
        (polynomialProjDegreeOneGlobalCoordinate 𝕜 Index coordinate) =
      polynomialDegreeOneChartFrame 𝕜 Index coordinate
        (1 : Γ(polynomialDegreeOneProj 𝕜 Index, open_set)) := by
  apply Subtype.ext
  funext point
  rfl

noncomputable def polynomialDegreeOneChartRatio
    (first second : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index first) :
    Γ(polynomialDegreeOneProj 𝕜 Index, open_set) := by
  let fraction : ∀ point : open_set, polynomialDegreeZeroPointLocalization 𝕜 Index point.val :=
    fun point => HomogeneousLocalization.mk
    (𝒜 := MvPolynomial.homogeneousSubmodule Index 𝕜)
    ⟨1, ⟨MvPolynomial.X second, MvPolynomial.isHomogeneous_X 𝕜 second⟩,
      ⟨MvPolynomial.X first, MvPolynomial.isHomogeneous_X 𝕜 first⟩, inclusion point.property⟩
  refine ⟨fraction, PrelocalPredicate.sheafifyOf ?_⟩
  exact ⟨1, ⟨MvPolynomial.X second, MvPolynomial.isHomogeneous_X 𝕜 second⟩,
    ⟨MvPolynomial.X first, MvPolynomial.isHomogeneous_X 𝕜 first⟩,
    fun point => inclusion point.property, fun point => rfl⟩

theorem polynomialDegreeOneChartRatio_mul_coordinate
    (first second : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index first) (point : open_set) :
    ((polynomialDegreeOneChartRatio 𝕜 Index first second inclusion).val point).val *
        algebraMap (MvPolynomial Index 𝕜) (polynomialDegreeOnePointLocalization 𝕜 Index point.val)
          (MvPolynomial.X first) =
      algebraMap (MvPolynomial Index 𝕜) (polynomialDegreeOnePointLocalization 𝕜 Index point.val)
        (MvPolynomial.X second) := by
  change (HomogeneousLocalization.mk
    (𝒜 := MvPolynomial.homogeneousSubmodule Index 𝕜) _).val * _ = _
  rw [HomogeneousLocalization.val_mk, ← Localization.mk_one_eq_algebraMap,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, mul_one]
  ring

theorem polynomialDegreeOneChartRatio_frame
    (first second : Index) {open_set : (polynomialDegreeOneProj 𝕜 Index).Opens}
    (inclusion : open_set ≤ polynomialDegreeOneCoordinateOpen 𝕜 Index first) :
    polynomialDegreeOneChartFrame 𝕜 Index first (polynomialDegreeOneChartRatio 𝕜 Index first second inclusion) =
      polynomialDegreeOneChartFrame 𝕜 Index second (1 : Γ(polynomialDegreeOneProj 𝕜 Index, open_set)) := by
  apply Subtype.ext
  funext point
  change _ = HomogeneousLocalization.val (1 : polynomialDegreeZeroPointLocalization 𝕜 Index point.val) * _
  rw [HomogeneousLocalization.val_one, one_mul]
  exact polynomialDegreeOneChartRatio_mul_coordinate 𝕜 Index first second inclusion point

theorem polynomialDegreeOneChartRatio_eq_awayToSection (chart coordinate : Index) :
    polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl =
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart))
        (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule Index 𝕜)
          (MvPolynomial.isHomogeneous_X 𝕜 chart) 1 (MvPolynomial.X coordinate)
            (by simpa using MvPolynomial.isHomogeneous_X 𝕜 coordinate)) := by
  apply Subtype.ext
  funext point
  change HomogeneousLocalization.mk
      (𝒜 := MvPolynomial.homogeneousSubmodule Index 𝕜) _ =
    HomogeneousLocalization.mapId (MvPolynomial.homogeneousSubmodule Index 𝕜)
      (Submonoid.powers_le.mpr point.property)
      (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule Index 𝕜)
        (MvPolynomial.isHomogeneous_X 𝕜 chart) 1 (MvPolynomial.X coordinate) _)
  rw [HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId,
    HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective _
  simp [HomogeneousLocalization.val_mk]

end

end BondalThomsen

namespace TauCeti.Toric.Fan

attribute [local instance] MvPolynomial.gradedAlgebra

end TauCeti.Toric.Fan
