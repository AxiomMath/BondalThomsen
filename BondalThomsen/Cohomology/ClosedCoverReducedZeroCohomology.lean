module

public import BondalThomsen.Ports.LeanPool.ClosedCoverConnectedness
public import BondalThomsen.Toric.Cohomology.NegativeSupportRelativeCohomology

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open BondalThomsen.ToricNefCechAcyclicity
open scoped Classical Simplicial

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ClosedCoverReducedZeroCohomology

variable {Space : Type*} {Chart : Type} [TopologicalSpace Space] [Finite Chart]

theorem compatible_values_eq_of_closed_connected_cover
    (patches : Chart → Set Space) (connected : IsPreconnected (⋃ chart, patches chart))
    (closed : ∀ chart, IsClosed (patches chart)) {Value : Type*} (values : Chart → Value)
    (compatible : ∀ first second, (patches first ∩ patches second).Nonempty → values first = values second)
    (first second : Chart) (firstNonempty : (patches first).Nonempty)
    (secondNonempty : (patches second).Nonempty) : values first = values second := by
  have chain := connected.transGen_of_finite_iUnion closed first second firstNonempty secondNonempty
  induction chain with
  | single adjacent => exact compatible _ _ adjacent
  | tail _chain adjacent equal =>
    have lastEquality := compatible _ _ adjacent
    obtain ⟨point, onPrevious, _onNext⟩ := adjacent
    exact (equal ⟨point, onPrevious⟩).trans lastEquality

omit [Finite Chart] in
theorem negativeComplex_d_apply {Ray : Type*} (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ)
    (cochain : (negativeComplex 𝕜 incidence negative).X degree)
    (tuple : forbiddenTuple incidence negative (degree + 1)) :
    (negativeComplex 𝕜 incidence negative).d degree (degree + 1) cochain tuple =
      ∑ deleted : Fin (degree + 2), ((-1 : ℤ) ^ deleted.val) •
        cochain ⟨tuple.val ∘ deleted.succAbove,
          tupleForbidden_precomp incidence negative deleted.succAbove tuple.val tuple.property⟩ := by
  let evaluation : ((negativeComplex 𝕜 incidence negative).X degree ⟶
      (negativeComplex 𝕜 incidence negative).X (degree + 1)) →+ 𝕜 :=
    (Pi.evalAddMonoidHom (fun _tuple : forbiddenTuple incidence negative (degree + 1) => 𝕜) tuple).comp
      ((AddMonoidHom.eval cochain).comp AddCommGrpCat.homAddEquiv.toAddMonoidHom)
  change evaluation ((negativeComplex 𝕜 incidence negative).d degree (degree + 1)) = _
  have differential : (negativeComplex 𝕜 incidence negative).d degree (degree + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD (negativeCosimplicial 𝕜 incidence negative) degree := by
    simp only [negativeComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  rw [differential, AlgebraicTopology.AlternatingCofaceMapComplex.objD, map_sum]
  apply Finset.sum_congr rfl
  intro deleted _present
  rw [map_zsmul]
  rfl

theorem negativeDegreeZeroCycle_values_eq_of_cover_incidence {Ray : Type*}
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (patches : Chart → Set Space) (connected : IsPreconnected (⋃ chart, patches chart))
    (closed : ∀ chart, IsClosed (patches chart))
    (comparison : ∀ degree (tuple : Fin (degree + 1) → Chart),
      tupleForbidden incidence negative degree tuple ↔ ∃ point, ∀ index, point ∈ patches (tuple index))
    (cochain : (negativeComplex 𝕜 incidence negative).X 0)
    (cycle : (negativeComplex 𝕜 incidence negative).d 0 1 cochain = 0)
    (first second : forbiddenTuple incidence negative 0) :
    cochain first = cochain second := by
  let vertexTuple := fun chart : {chart : Chart // (patches chart).Nonempty} =>
    (⟨fun _index => chart.val, by
      obtain ⟨point, contains⟩ := chart.property
      exact (comparison 0 _).mpr ⟨point, fun _index => contains⟩⟩ :
      forbiddenTuple incidence negative 0)
  let values := fun chart : Chart =>
    if nonempty : (patches chart).Nonempty then cochain (vertexTuple ⟨chart, nonempty⟩) else 0
  have compatible : ∀ source target, (patches source ∩ patches target).Nonempty → values source = values target := by
    intro source target intersects
    obtain ⟨point, onSource, onTarget⟩ := intersects
    have sourceNonempty : (patches source).Nonempty := ⟨point, onSource⟩
    have targetNonempty : (patches target).Nonempty := ⟨point, onTarget⟩
    let pair : forbiddenTuple incidence negative 1 :=
      ⟨Fin.cons source (fun _index => target), (comparison 1 _).mpr ⟨point, by
        intro index
        fin_cases index <;> assumption⟩⟩
    have evaluated := congrFun cycle pair
    change (negativeComplex 𝕜 _ _).d 0 1 cochain pair = (0 : 𝕜) at evaluated
    rw [negativeComplex_d_apply] at evaluated
    change (∑ deleted : Fin 2, ((-1 : ℤ) ^ deleted.val) •
      cochain ⟨pair.val ∘ deleted.succAbove, _⟩) = 0 at evaluated
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      one_zsmul, neg_zsmul] at evaluated
    have firstFace : (⟨pair.val ∘ (0 : Fin 2).succAbove,
        tupleForbidden_precomp _ _ (0 : Fin 2).succAbove pair.val pair.property⟩ :
        forbiddenTuple incidence negative 0) =
        vertexTuple ⟨target, targetNonempty⟩ := by
      apply Subtype.ext
      funext index
      change Fin 1 at index
      have indexZero : index = 0 := Subsingleton.elim _ _
      subst index
      rfl
    have secondFace : (⟨pair.val ∘ (1 : Fin 2).succAbove,
        tupleForbidden_precomp _ _ (1 : Fin 2).succAbove pair.val pair.property⟩ :
        forbiddenTuple incidence negative 0) =
        vertexTuple ⟨source, sourceNonempty⟩ := by
      apply Subtype.ext
      funext index
      change Fin 1 at index
      have indexZero : index = 0 := Subsingleton.elim _ _
      subst index
      rfl
    rw [firstFace, secondFace, ← sub_eq_add_neg] at evaluated
    simp only [values, dite_eq_left sourceNonempty, dite_eq_left targetNonempty]
    exact (sub_eq_zero.mp evaluated).symm
  have tupleNonempty : ∀ tuple : forbiddenTuple incidence negative 0,
      (patches (tuple.val 0)).Nonempty := by
    intro tuple
    obtain ⟨point, contains⟩ := (comparison 0 tuple.val).mp tuple.property
    exact ⟨point, contains 0⟩
  have tupleSame : ∀ tuple : forbiddenTuple incidence negative 0,
      vertexTuple ⟨tuple.val 0, tupleNonempty tuple⟩ = tuple := by
    intro tuple
    apply Subtype.ext
    funext index
    change Fin 1 at index
    have indexZero : index = (0 : Fin 1) := Subsingleton.elim _ _
    subst index
    rfl
  have equality := compatible_values_eq_of_closed_connected_cover patches connected closed values compatible
    (first.val 0) (second.val 0) (tupleNonempty first) (tupleNonempty second)
  simpa only [values, dite_eq_left (tupleNonempty first), dite_eq_left (tupleNonempty second), tupleSame] using equality

omit [Finite Chart] in
theorem negativeConstantAugmentation_epi_of_degreeZeroCycles_constant
    {Ray : Type*} (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (constant : ∀ cochain : (negativeComplex 𝕜 incidence negative).X 0,
      (negativeComplex 𝕜 incidence negative).d 0 1 cochain = 0 →
        ∀ first second, cochain first = cochain second) (anchor : Chart) :
    Epi (negativeConstantAugmentation 𝕜 incidence negative anchor) := by
  let restriction := negativeComplexRestriction 𝕜 incidence negative
  let constants := (fullCyclesDegreeZeroIso 𝕜 anchor).hom ≫ HomologicalComplex.cyclesMap restriction 0
  have constants_epi : Epi constants := by
    apply (AddCommGrpCat.epi_iff_surjective constants).mpr
    intro cycle
    let cochain := (negativeComplex 𝕜 incidence negative).iCycles 0 cycle
    have closedCochain := ConcreteCategory.congr_hom
      ((negativeComplex 𝕜 incidence negative).iCycles_d 0 1) cycle
    have constantValues : ∀ first second, cochain first = cochain second :=
      constant cochain closedCochain
    have image (scalar : 𝕜) (tuple : forbiddenTuple incidence negative 0) :
        (negativeComplex 𝕜 incidence negative).iCycles 0 (constants scalar) tuple = scalar := by
      have equality := ConcreteCategory.congr_hom
        (show constants ≫ (negativeComplex 𝕜 incidence negative).iCycles 0 =
          AddCommGrpCat.ofHom (fullDegreeZeroConstant 𝕜) ≫ restriction.f 0 by
            dsimp only [constants]
            rw [Category.assoc, HomologicalComplex.cyclesMap_i,
              ← Category.assoc]
            dsimp only [fullCyclesDegreeZeroIso]
            rw [HomologicalComplex.liftCycles_i]) scalar
      exact congrFun equality tuple
    rcases isEmpty_or_nonempty (forbiddenTuple incidence negative 0) with empty | nonempty
    · let := empty
      refine ⟨0, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective
        ((negativeComplex 𝕜 incidence negative).iCycles 0)).mp inferInstance
      funext tuple
      exact isEmptyElim tuple
    · obtain ⟨first⟩ := nonempty
      refine ⟨cochain first, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective
        ((negativeComplex 𝕜 incidence negative).iCycles 0)).mp inferInstance
      funext tuple
      rw [image]
      exact constantValues first tuple
  have augmentation : negativeConstantAugmentation 𝕜 incidence negative anchor =
      constants ≫ (negativeComplex 𝕜 incidence negative).homologyπ 0 := by
    dsimp only [negativeConstantAugmentation, fullHomologyDegreeZeroIso]
    simp only [Iso.trans_hom, asIso_hom, Category.assoc, HomologicalComplex.homologyπ_naturality]
    rfl
  rw [augmentation]
  let := constants_epi
  infer_instance

end BondalThomsen.ClosedCoverReducedZeroCohomology
