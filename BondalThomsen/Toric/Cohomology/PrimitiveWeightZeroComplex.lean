module

public import BondalThomsen.Toric.Cohomology.PrimitiveWeightZeroCech

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Preadditive
open BondalThomsen.FiniteAffineCechHigherComparison
open Multiplicative
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ToricPrimitiveWeightZeroComplex

universe u

noncomputable def transportSectionEnd (scheme : Scheme.{u}) (coefficient : scheme.Modules)
    {actual chart : scheme.Opens} (identification : actual = chart)
    (projector : coefficient.presheaf.obj (op chart) ⟶ coefficient.presheaf.obj (op chart)) :
    coefficient.presheaf.obj (op actual) ⟶ coefficient.presheaf.obj (op actual) :=
  eqToHom (congrArg (fun open_set => coefficient.presheaf.obj (op open_set)) identification) ≫
    projector ≫
      eqToHom (congrArg (fun open_set => coefficient.presheaf.obj (op open_set)) identification.symm)

theorem transportSectionEnd_restrict (scheme : Scheme.{u}) (coefficient : scheme.Modules)
    {actualLarger actualSmaller chartLarger chartSmaller : scheme.Opens}
    (largerEq : actualLarger = chartLarger) (smallerEq : actualSmaller = chartSmaller)
    (actualContainment : actualSmaller ≤ actualLarger) (chartContainment : chartSmaller ≤ chartLarger)
    (largerProjector : coefficient.presheaf.obj (op chartLarger) ⟶ coefficient.presheaf.obj (op chartLarger))
    (smallerProjector : coefficient.presheaf.obj (op chartSmaller) ⟶ coefficient.presheaf.obj (op chartSmaller))
    (compatible : largerProjector ≫ coefficient.presheaf.map (homOfLE chartContainment).op =
      coefficient.presheaf.map (homOfLE chartContainment).op ≫ smallerProjector) :
    transportSectionEnd scheme coefficient largerEq largerProjector ≫
        coefficient.presheaf.map (homOfLE actualContainment).op =
      coefficient.presheaf.map (homOfLE actualContainment).op ≫
        transportSectionEnd scheme coefficient smallerEq smallerProjector := by
  subst actualLarger
  subst actualSmaller
  simpa [transportSectionEnd] using compatible

theorem productProjectors_compatible {Index Tuple : Type u}
    (source : Index → AddCommGrpCat.{u}) (target : Tuple → AddCommGrpCat.{u})
    (sourceProjector : ∀ index, source index ⟶ source index)
    (targetProjector : ∀ tuple, target tuple ⟶ target tuple)
    (selection : Tuple → Index) (restriction : ∀ tuple, source (selection tuple) ⟶ target tuple)
    (compatible : ∀ tuple, sourceProjector (selection tuple) ≫ restriction tuple =
      restriction tuple ≫ targetProjector tuple) :
    Limits.Pi.map sourceProjector ≫
        Limits.Pi.lift (fun tuple => Limits.Pi.π source (selection tuple) ≫ restriction tuple) =
      Limits.Pi.lift (fun tuple => Limits.Pi.π source (selection tuple) ≫ restriction tuple) ≫
        Limits.Pi.map targetProjector := by
  apply Limits.Pi.hom_ext (f := target)
  intro tuple
  simp only [Category.assoc, Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc,
    Limits.Pi.map_π, Limits.Pi.map_π_assoc]
  rw [compatible]

theorem productMaps_restriction {Index Tuple : Type u}
    (source target : Index → AddCommGrpCat.{u})
    (nextSource nextTarget : Tuple → AddCommGrpCat.{u})
    (maps : ∀ index, source index ⟶ target index)
    (nextMaps : ∀ tuple, nextSource tuple ⟶ nextTarget tuple)
    (selection : Tuple → Index)
    (sourceRestriction : ∀ tuple, source (selection tuple) ⟶ nextSource tuple)
    (targetRestriction : ∀ tuple, target (selection tuple) ⟶ nextTarget tuple)
    (compatible : ∀ tuple, maps (selection tuple) ≫ targetRestriction tuple =
      sourceRestriction tuple ≫ nextMaps tuple) :
    Limits.Pi.map maps ≫
        Limits.Pi.lift (fun tuple => Limits.Pi.π target (selection tuple) ≫ targetRestriction tuple) =
      Limits.Pi.lift (fun tuple => Limits.Pi.π source (selection tuple) ≫ sourceRestriction tuple) ≫
        Limits.Pi.map nextMaps := by
  apply Limits.Pi.hom_ext (f := nextTarget)
  intro tuple
  simp only [Category.assoc, Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc,
    Limits.Pi.map_π, Limits.Pi.map_π_assoc]
  rw [compatible]

theorem productMaps_comp {Index : Type u} (first middle last : Index → AddCommGrpCat.{u})
    (firstMap : ∀ index, first index ⟶ middle index)
    (secondMap : ∀ index, middle index ⟶ last index)
    (composite : ∀ index, first index ⟶ last index)
    (same : ∀ index, firstMap index ≫ secondMap index = composite index) :
    Limits.Pi.map firstMap ≫ Limits.Pi.map secondMap = Limits.Pi.map composite := by
  rw [Limits.Pi.map_comp_map]
  congr 1
  funext index
  exact same index

theorem splitRetraction_compatible {TargetCategory : Type*} [CategoryTheory.Category TargetCategory]
    {source target summandSource summandTarget : TargetCategory}
    (inclusion : summandSource ⟶ source) (nextInclusion : summandTarget ⟶ target)
    (retraction : source ⟶ summandSource) (nextRetraction : target ⟶ summandTarget)
    (differential : source ⟶ target) (summandDifferential : summandSource ⟶ summandTarget)
    (nextSplit : nextInclusion ≫ nextRetraction = 𝟙 summandTarget)
    (inclusionCompatible : inclusion ≫ differential = summandDifferential ≫ nextInclusion)
    (projectorCompatible : (retraction ≫ inclusion) ≫ differential =
      differential ≫ (nextRetraction ≫ nextInclusion)) :
    retraction ≫ summandDifferential = differential ≫ nextRetraction := by
  calc
    retraction ≫ summandDifferential =
        (retraction ≫ summandDifferential) ≫ (nextInclusion ≫ nextRetraction) := by
      rw [nextSplit, Category.comp_id]
    _ = ((retraction ≫ inclusion) ≫ differential) ≫ nextRetraction := by
      simp only [Category.assoc]
      rw [← Category.assoc summandDifferential nextInclusion nextRetraction, ← inclusionCompatible]
      simp only [Category.assoc]
    _ = (differential ≫ (nextRetraction ≫ nextInclusion)) ≫ nextRetraction := by
      rw [projectorCompatible]
    _ = differential ≫ nextRetraction := by
      simp only [Category.assoc]
      rw [nextSplit, Category.comp_id]

noncomputable def projectorImageGroup (complex : CochainComplex AddCommGrpCat.{u} ℕ)
    (projector : complex ⟶ complex) (degree : ℕ) : AddSubgroup (complex.X degree) :=
  (projector.f degree).hom.range

noncomputable def sectionOpenEquiv (scheme : Scheme.{u}) (coefficient : scheme.Modules)
    {actual chart : scheme.Opens} (identification : actual = chart) :
    coefficient.presheaf.obj (op actual) ≃+ coefficient.presheaf.obj (op chart) :=
  (eqToIso (congrArg (fun open_set => coefficient.presheaf.obj (op open_set)) identification)).addCommGroupIsoToAddEquiv

theorem sectionOpenEquiv_projector (scheme : Scheme.{u}) (coefficient : scheme.Modules)
    {actual chart : scheme.Opens} (identification : actual = chart)
    (projector : coefficient.presheaf.obj (op chart) ⟶ coefficient.presheaf.obj (op chart))
    (element : coefficient.presheaf.obj (op actual)) :
    sectionOpenEquiv scheme coefficient identification
        (transportSectionEnd scheme coefficient identification projector element) =
      projector (sectionOpenEquiv scheme coefficient identification element) := by
  subst actual
  rfl

theorem sectionOpenEquiv_restrict (scheme : Scheme.{u}) (coefficient : scheme.Modules)
    {actualLarger actualSmaller chartLarger chartSmaller : scheme.Opens}
    (largerEq : actualLarger = chartLarger) (smallerEq : actualSmaller = chartSmaller)
    (actualContainment : actualSmaller ≤ actualLarger) (chartContainment : chartSmaller ≤ chartLarger)
    (element : coefficient.presheaf.obj (op actualLarger)) :
    sectionOpenEquiv scheme coefficient smallerEq
        (coefficient.presheaf.map (homOfLE actualContainment).op element) =
      coefficient.presheaf.map (homOfLE chartContainment).op
        (sectionOpenEquiv scheme coefficient largerEq element) := by
  subst actualLarger
  subst actualSmaller
  rfl

noncomputable def supportedScalarGroup (available : Prop) : AddSubgroup 𝕜 where
  carrier := {scalar | ¬available → scalar = 0}
  zero_mem' := fun _unavailable => rfl
  add_mem' := fun first second unavailable => by rw [first unavailable, second unavailable, zero_add]
  neg_mem' := fun member unavailable => by rw [member unavailable, neg_zero]

end BondalThomsen.ToricPrimitiveWeightZeroComplex

namespace TauCeti.Toric.Fan

open BondalThomsen.ToricPrimitiveWeightZeroComplex

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def primitiveWeightZeroCechComplex (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    CochainComplex AddCommGrpCat ℕ :=
  schemeCechComplex (fan.primitiveCechChartOpen 𝕜 complete regular)
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj

noncomputable def primitiveCechCoefficient (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) : AddCommGrpCat :=
  (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.obj
    (op (cechIntersection (fan.primitiveCechChartOpen 𝕜 complete regular) degree tuple))

noncomputable def primitiveCechCoefficientProjector (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple ⟶
      fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple :=
  transportSectionEnd (fan.algebraicRealization 𝕜 regular)
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
    (fan.primitiveCechIntersection_eq_chart 𝕜 complete regular degree tuple)
    (AddCommGrpCat.ofHom (fan.primitiveCechWeightZeroProjection 𝕜 complete regular divisor degree tuple))

noncomputable def primitiveCechFaceRestriction (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones)) (deleted : Fin (degree + 2)) :
    fan.primitiveCechCoefficient 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove) ⟶
      fan.primitiveCechCoefficient 𝕜 complete regular divisor (degree + 1) tuple :=
  (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.map
    (Limits.Pi.lift (fun index : Fin (degree + 1) =>
      Limits.Pi.π (fan.primitiveCechChartOpen 𝕜 complete regular ∘ tuple) (deleted.succAbove index))).op

theorem primitiveCechCoefficientProjector_face (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones)) (deleted : Fin (degree + 2)) :
    fan.primitiveCechCoefficientProjector 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove) ≫
        fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted =
      fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted ≫
        fan.primitiveCechCoefficientProjector 𝕜 complete regular divisor (degree + 1) tuple := by
  let chartContainment := fan.primitiveCechCone_opensRange_mono 𝕜 regular
    (fan.primitiveCechCone_le_face 𝕜 complete regular degree tuple deleted)
  let actualContainment :
      cechIntersection (fan.primitiveCechChartOpen 𝕜 complete regular) (degree + 1) tuple ≤
        cechIntersection (fan.primitiveCechChartOpen 𝕜 complete regular) degree (tuple ∘ deleted.succAbove) :=
    (Limits.Pi.lift (fun index : Fin (degree + 1) =>
      Limits.Pi.π (fan.primitiveCechChartOpen 𝕜 complete regular ∘ tuple) (deleted.succAbove index))).le
  unfold primitiveCechCoefficientProjector primitiveCechFaceRestriction
  apply transportSectionEnd_restrict _ _ _ _ actualContainment chartContainment
  ext section_value
  exact fan.primitiveCechWeightZeroProjection_face 𝕜 complete regular divisor degree tuple deleted section_value

noncomputable def primitiveCechDegreeProjector (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree ⟶
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree :=
  Limits.Pi.map (fan.primitiveCechCoefficientProjector 𝕜 complete regular divisor degree)

noncomputable def primitiveCechCoface (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (deleted : Fin (degree + 2)) :
    (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree ⟶
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X (degree + 1) :=
  Limits.Pi.lift (fun tuple : Fin (degree + 2) → Fin (Nat.card fan.cones) =>
    Limits.Pi.π (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree)
      (tuple ∘ deleted.succAbove) ≫
        fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted)

theorem primitiveCechDegreeProjector_coface (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (deleted : Fin (degree + 2)) :
    fan.primitiveCechDegreeProjector 𝕜 complete regular divisor degree ≫
        fan.primitiveCechCoface 𝕜 complete regular divisor degree deleted =
      fan.primitiveCechCoface 𝕜 complete regular divisor degree deleted ≫
        fan.primitiveCechDegreeProjector 𝕜 complete regular divisor (degree + 1) := by
  exact productProjectors_compatible
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree)
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor (degree + 1))
    (fan.primitiveCechCoefficientProjector 𝕜 complete regular divisor degree)
    (fan.primitiveCechCoefficientProjector 𝕜 complete regular divisor (degree + 1))
    (fun tuple => tuple ∘ deleted.succAbove)
    (fun tuple => fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted)
    (fun tuple => fan.primitiveCechCoefficientProjector_face 𝕜 complete regular divisor degree tuple deleted)

theorem primitiveWeightZeroCechComplex_d (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).d degree (degree + 1) =
      ∑ deleted : Fin (degree + 2), (-1 : ℤ) ^ deleted.val •
        fan.primitiveCechCoface 𝕜 complete regular divisor degree deleted := by
  change (AlgebraicTopology.AlternatingCofaceMapComplex.obj _).d degree (degree + 1) = _
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [CochainComplex.of_d]
  rfl

theorem primitiveCechDegreeProjector_d (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    fan.primitiveCechDegreeProjector 𝕜 complete regular divisor degree ≫
        (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).d degree (degree + 1) =
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).d degree (degree + 1) ≫
        fan.primitiveCechDegreeProjector 𝕜 complete regular divisor (degree + 1) := by
  rw [fan.primitiveWeightZeroCechComplex_d 𝕜, comp_sum, sum_comp]
  apply Finset.sum_congr rfl
  intro deleted _member
  rw [comp_zsmul, zsmul_comp, fan.primitiveCechDegreeProjector_coface 𝕜]

noncomputable def primitiveCechCoefficientLaurentEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple ≃+
      fan.divisorLaurentSectionSpace 𝕜 (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor :=
  (sectionOpenEquiv (fan.algebraicRealization 𝕜 regular)
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
    (fan.primitiveCechIntersection_eq_chart 𝕜 complete regular degree tuple)).trans
      (fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree tuple).symm

theorem primitiveCechCoefficientLaurentEquiv_projector (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (element : fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple) :
    fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple
        (fan.primitiveCechCoefficientProjector 𝕜 complete regular divisor degree tuple element) =
      fan.divisorLaurentWeightZeroProjection 𝕜 (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor
        (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple element) := by
  have transport := sectionOpenEquiv_projector (fan.algebraicRealization 𝕜 regular)
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
    (fan.primitiveCechIntersection_eq_chart 𝕜 complete regular degree tuple)
    (AddCommGrpCat.ofHom (fan.primitiveCechWeightZeroProjection 𝕜 complete regular divisor degree tuple)) element
  have equality := congrArg
    (fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree tuple).symm transport
  exact equality.trans (by
    change (fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree tuple).symm
        ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree tuple)
          (fan.divisorLaurentWeightZeroProjection 𝕜 _ divisor
            ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree tuple).symm _))) = _
    rw [AddEquiv.symm_apply_apply]
    rfl)

theorem primitiveCechCoefficientLaurentEquiv_face (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones)) (deleted : Fin (degree + 2))
    (element : fan.primitiveCechCoefficient 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove)) :
    (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor (degree + 1) tuple
      (fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted element)).val =
    (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree
      (tuple ∘ deleted.succAbove) element).val := by
  let chartContainment := fan.primitiveCechCone_opensRange_mono 𝕜 regular
    (fan.primitiveCechCone_le_face 𝕜 complete regular degree tuple deleted)
  have actualContainment :=
    (Limits.Pi.lift (fun index : Fin (degree + 1) =>
      Limits.Pi.π (fan.primitiveCechChartOpen 𝕜 complete regular ∘ tuple) (deleted.succAbove index))).le
  let chartElement := sectionOpenEquiv (fan.algebraicRealization 𝕜 regular)
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
    (fan.primitiveCechIntersection_eq_chart 𝕜 complete regular degree (tuple ∘ deleted.succAbove)) element
  obtain ⟨polynomial, polynomial_eq⟩ := fan.primitiveCechLaurentToSheafSections_surjective 𝕜
    complete regular divisor degree (tuple ∘ deleted.succAbove) chartElement
  have transport := sectionOpenEquiv_restrict (fan.algebraicRealization 𝕜 regular)
    (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj
    (fan.primitiveCechIntersection_eq_chart 𝕜 complete regular degree (tuple ∘ deleted.succAbove))
    (fan.primitiveCechIntersection_eq_chart 𝕜 complete regular (degree + 1) tuple)
    actualContainment chartContainment element
  change ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor (degree + 1) tuple).symm
      (sectionOpenEquiv _ _ _ (fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted element))).val =
    ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree
      (tuple ∘ deleted.succAbove)).symm chartElement).val
  have comparison := fan.primitiveCechLaurentToSheafSections_restrict 𝕜 complete regular divisor degree (degree + 1)
    (tuple ∘ deleted.succAbove) tuple (fan.primitiveCechCone_le_face 𝕜 complete regular degree tuple deleted)
    chartContainment polynomial
  have same := (congrArg
    ((fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj.presheaf.map
      (homOfLE chartContainment).op) polynomial_eq).symm.trans comparison
  refine (congrArg (fun section_value =>
    ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor (degree + 1) tuple).symm section_value).val)
      transport).trans ?_
  refine (congrArg (fun section_value =>
    ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor (degree + 1) tuple).symm section_value).val)
      same).trans ?_
  have source_eq := congrArg (fun section_value =>
    ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree
      (tuple ∘ deleted.succAbove)).symm section_value).val) polynomial_eq
  change ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor (degree + 1) tuple).symm
      ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor (degree + 1) tuple) _)).val = _
  rw [AddEquiv.symm_apply_apply]
  change ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree
      (tuple ∘ deleted.succAbove)).symm
      ((fan.primitiveCechSheafSectionsEquiv 𝕜 complete regular divisor degree
        (tuple ∘ deleted.succAbove)) polynomial)).val = _ at source_eq
  simpa only [AddEquiv.symm_apply_apply] using source_eq

def primitiveCechTupleAvailable (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) : Prop :=
  ∀ ray : fan.Ray, embedding ray.val ∈ (fan.primitiveCechCone 𝕜 complete regular degree tuple).val → 0 ≤ divisor ray

theorem primitiveCechTupleAvailable_negativeIndicator (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (negative : Finset fan.Ray)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechTupleAvailable 𝕜 complete regular
        (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ negative then -1 else 0)) degree tuple ↔
      ∀ ray ∈ negative, embedding ray.val ∉ (fan.primitiveCechCone 𝕜 complete regular degree tuple).val := by
  constructor
  · intro available ray member contains
    have nonnegative := available ray contains
    simp [invariantDivisorOfCoefficients, member] at nonnegative
  · intro avoids ray contains
    have absent : ray ∉ negative := fun member => avoids ray member contains
    simp [invariantDivisorOfCoefficients, absent]

omit [FiniteDimensional ℝ Ambient] in
theorem constantLaurent_mem_iff (fan : Fan embedding) (cone : PointedCone ℝ Ambient)
    (divisor : fan.InvariantRayDivisor) (scalar : 𝕜) :
    MonoidAlgebra.single (ofAdd (0 : Lattice →+ ℤ)) scalar ∈ fan.divisorLaurentSectionSpace 𝕜 cone divisor ↔
      (¬(∀ ray : fan.Ray, embedding ray.val ∈ cone → 0 ≤ divisor ray) → scalar = 0) := by
  classical
  by_cases scalar_zero : scalar = 0
  · subst scalar
    simp [MonoidAlgebra.single_zero]
  · rw [fan.mem_divisorLaurentSectionSpace_iff 𝕜]
    simp only [MonoidAlgebra.coeff_single, Finsupp.support_single _ scalar_zero,
      Finset.mem_singleton, forall_eq, toAdd_ofAdd, AddMonoidHom.zero_apply, neg_nonpos]
    tauto

noncomputable def primitiveCechScalarCoefficient (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) : AddSubgroup 𝕜 :=
  supportedScalarGroup 𝕜 (fan.primitiveCechTupleAvailable 𝕜 complete regular divisor degree tuple)

noncomputable def primitiveCechScalarToLaurent (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechScalarCoefficient 𝕜 complete regular divisor degree tuple →+
      fan.divisorLaurentSectionSpace 𝕜 (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor where
  toFun scalar := ⟨MonoidAlgebra.single (ofAdd 0) scalar.val,
    (fan.constantLaurent_mem_iff 𝕜 _ divisor scalar.val).mpr scalar.property⟩
  map_zero' := by apply Subtype.ext; exact MonoidAlgebra.single_zero _
  map_add' first second := by apply Subtype.ext; exact MonoidAlgebra.single_add _ _ _

noncomputable def primitiveCechScalarToCoefficient (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechScalarCoefficient 𝕜 complete regular divisor degree tuple →+
      fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple :=
  (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple).symm.toAddMonoidHom.comp
    (fan.primitiveCechScalarToLaurent 𝕜 complete regular divisor degree tuple)

noncomputable def primitiveCechCoefficientToScalar (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple →+
      fan.primitiveCechScalarCoefficient 𝕜 complete regular divisor degree tuple := by
  refine {
    toFun := fun element => ⟨
      (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple element).val.coeff (ofAdd 0), ?_⟩
    map_zero' := ?_
    map_add' := fun first second => ?_ }
  · apply (fan.constantLaurent_mem_iff 𝕜 _ divisor _).mp
    exact (fan.divisorLaurentWeightZeroProjection 𝕜
      (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor
      (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple element)).property
  · apply Subtype.ext
    simp only [map_zero, Submodule.coe_zero, MonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      AddSubgroup.coe_zero]
  · apply Subtype.ext
    simp only [map_add, Submodule.coe_add, MonoidAlgebra.coeff_add, Finsupp.add_apply,
      AddSubgroup.coe_add]

theorem primitiveCechCoefficientToScalar_toCoefficient (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (scalar : fan.primitiveCechScalarCoefficient 𝕜 complete regular divisor degree tuple) :
    fan.primitiveCechCoefficientToScalar 𝕜 complete regular divisor degree tuple
        (fan.primitiveCechScalarToCoefficient 𝕜 complete regular divisor degree tuple scalar) = scalar := by
  apply Subtype.ext
  change (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple
      ((fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple).symm
        (fan.primitiveCechScalarToLaurent 𝕜 complete regular divisor degree tuple scalar))).val.coeff (ofAdd 0) = _
  rw [AddEquiv.apply_symm_apply]
  simp [primitiveCechScalarToLaurent, MonoidAlgebra.coeff_single]

theorem primitiveCechScalarToCoefficient_toScalar (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (element : fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple) :
    fan.primitiveCechScalarToCoefficient 𝕜 complete regular divisor degree tuple
        (fan.primitiveCechCoefficientToScalar 𝕜 complete regular divisor degree tuple element) =
      fan.primitiveCechCoefficientProjector 𝕜 complete regular divisor degree tuple element := by
  apply (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple).injective
  change (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple)
      ((fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple).symm _) = _
  rw [AddEquiv.apply_symm_apply, fan.primitiveCechCoefficientLaurentEquiv_projector 𝕜]
  apply Subtype.ext
  rfl

theorem primitiveCechTupleAvailable_face (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones)) (deleted : Fin (degree + 2)) :
    fan.primitiveCechTupleAvailable 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove) →
      fan.primitiveCechTupleAvailable 𝕜 complete regular divisor (degree + 1) tuple :=
  fun available ray contains => available ray
    (fan.primitiveCechCone_le_face 𝕜 complete regular degree tuple deleted contains)

noncomputable def primitiveCechScalarFaceRestriction (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones)) (deleted : Fin (degree + 2)) :
    fan.primitiveCechScalarCoefficient 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove) →+
      fan.primitiveCechScalarCoefficient 𝕜 complete regular divisor (degree + 1) tuple where
  toFun scalar := ⟨scalar.val, fun unavailable => scalar.property
    (fun available => unavailable (fan.primitiveCechTupleAvailable_face 𝕜 complete regular divisor degree tuple deleted available))⟩
  map_zero' := rfl
  map_add' _first _second := rfl

theorem primitiveCechScalarToCoefficient_face (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones)) (deleted : Fin (degree + 2))
    (scalar : fan.primitiveCechScalarCoefficient 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove)) :
    fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted
        (fan.primitiveCechScalarToCoefficient 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove) scalar) =
      fan.primitiveCechScalarToCoefficient 𝕜 complete regular divisor (degree + 1) tuple
        (fan.primitiveCechScalarFaceRestriction 𝕜 complete regular divisor degree tuple deleted scalar) := by
  apply (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor (degree + 1) tuple).injective
  apply Subtype.ext
  refine (fan.primitiveCechCoefficientLaurentEquiv_face 𝕜 complete regular divisor degree tuple deleted _).trans ?_
  change ((fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove))
      ((fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove)).symm
        (fan.primitiveCechScalarToLaurent 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove) scalar))).val =
    ((fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor (degree + 1) tuple)
      ((fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor (degree + 1) tuple).symm _)).val
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

noncomputable def primitiveComplementCoefficient (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) : AddCommGrpCat :=
  AddCommGrpCat.of (fan.primitiveCechScalarCoefficient 𝕜 complete regular divisor degree tuple)

noncomputable def primitiveComplementDegree (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) : AddCommGrpCat :=
  ∏ᶜ (fan.primitiveComplementCoefficient 𝕜 complete regular divisor degree)

noncomputable def primitiveComplementDegreeInclusion (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) : fan.primitiveComplementDegree 𝕜 complete regular divisor degree ⟶
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree :=
  Limits.Pi.map (fun tuple => AddCommGrpCat.ofHom
    (fan.primitiveCechScalarToCoefficient 𝕜 complete regular divisor degree tuple))

noncomputable def primitiveComplementDegreeRetraction (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) : (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree ⟶
      fan.primitiveComplementDegree 𝕜 complete regular divisor degree :=
  Limits.Pi.map (fun tuple => AddCommGrpCat.ofHom
    (fan.primitiveCechCoefficientToScalar 𝕜 complete regular divisor degree tuple))

theorem primitiveComplementDegree_split (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor degree ≫
        fan.primitiveComplementDegreeRetraction 𝕜 complete regular divisor degree =
      𝟙 (fan.primitiveComplementDegree 𝕜 complete regular divisor degree) := by
  have comparison := productMaps_comp
    (fan.primitiveComplementCoefficient 𝕜 complete regular divisor degree)
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree)
    (fan.primitiveComplementCoefficient 𝕜 complete regular divisor degree)
    (fun tuple => AddCommGrpCat.ofHom (fan.primitiveCechScalarToCoefficient 𝕜 complete regular divisor degree tuple))
    (fun tuple => AddCommGrpCat.ofHom (fan.primitiveCechCoefficientToScalar 𝕜 complete regular divisor degree tuple))
    (fun tuple => 𝟙 _) (fun tuple => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact fan.primitiveCechCoefficientToScalar_toCoefficient 𝕜 complete regular divisor degree tuple)
  exact comparison.trans Limits.Pi.map_id

theorem primitiveComplementDegree_projector (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    fan.primitiveComplementDegreeRetraction 𝕜 complete regular divisor degree ≫
        fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor degree =
      fan.primitiveCechDegreeProjector 𝕜 complete regular divisor degree := by
  exact productMaps_comp
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree)
    (fan.primitiveComplementCoefficient 𝕜 complete regular divisor degree)
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree)
    (fun tuple => AddCommGrpCat.ofHom (fan.primitiveCechCoefficientToScalar 𝕜 complete regular divisor degree tuple))
    (fun tuple => AddCommGrpCat.ofHom (fan.primitiveCechScalarToCoefficient 𝕜 complete regular divisor degree tuple))
    (fan.primitiveCechCoefficientProjector 𝕜 complete regular divisor degree) (fun tuple => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact fan.primitiveCechScalarToCoefficient_toScalar 𝕜 complete regular divisor degree tuple)

noncomputable def primitiveComplementCoface (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (deleted : Fin (degree + 2)) :
    fan.primitiveComplementDegree 𝕜 complete regular divisor degree ⟶
      fan.primitiveComplementDegree 𝕜 complete regular divisor (degree + 1) :=
  Limits.Pi.lift (fun tuple =>
    Limits.Pi.π (fan.primitiveComplementCoefficient 𝕜 complete regular divisor degree) (tuple ∘ deleted.succAbove) ≫
      AddCommGrpCat.ofHom (fan.primitiveCechScalarFaceRestriction 𝕜 complete regular divisor degree tuple deleted))

theorem primitiveComplementCoface_inclusion (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (deleted : Fin (degree + 2)) :
    fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor degree ≫
        fan.primitiveCechCoface 𝕜 complete regular divisor degree deleted =
      fan.primitiveComplementCoface 𝕜 complete regular divisor degree deleted ≫
        fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor (degree + 1) := by
  exact productMaps_restriction
    (fan.primitiveComplementCoefficient 𝕜 complete regular divisor degree)
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree)
    (fan.primitiveComplementCoefficient 𝕜 complete regular divisor (degree + 1))
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor (degree + 1))
    (fun tuple => AddCommGrpCat.ofHom (fan.primitiveCechScalarToCoefficient 𝕜 complete regular divisor degree tuple))
    (fun tuple => AddCommGrpCat.ofHom
      (fan.primitiveCechScalarToCoefficient 𝕜 complete regular divisor (degree + 1) tuple))
    (fun tuple => tuple ∘ deleted.succAbove)
    (fun tuple => AddCommGrpCat.ofHom (fan.primitiveCechScalarFaceRestriction 𝕜 complete regular divisor degree tuple deleted))
    (fun tuple => fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted)
    (fun tuple => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact fan.primitiveCechScalarToCoefficient_face 𝕜 complete regular divisor degree tuple deleted)

noncomputable def primitiveComplementDifferential (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) : fan.primitiveComplementDegree 𝕜 complete regular divisor degree ⟶
      fan.primitiveComplementDegree 𝕜 complete regular divisor (degree + 1) :=
  ∑ deleted : Fin (degree + 2), (-1 : ℤ) ^ deleted.val •
    fan.primitiveComplementCoface 𝕜 complete regular divisor degree deleted

theorem primitiveComplementDifferential_inclusion (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor degree ≫
        (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).d degree (degree + 1) =
      fan.primitiveComplementDifferential 𝕜 complete regular divisor degree ≫
        fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor (degree + 1) := by
  rw [fan.primitiveWeightZeroCechComplex_d 𝕜, primitiveComplementDifferential, comp_sum, sum_comp]
  apply Finset.sum_congr rfl
  intro deleted _member
  rw [comp_zsmul, zsmul_comp, fan.primitiveComplementCoface_inclusion 𝕜]

theorem primitiveComplementDifferential_squared (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    fan.primitiveComplementDifferential 𝕜 complete regular divisor degree ≫
      fan.primitiveComplementDifferential 𝕜 complete regular divisor (degree + 1) = 0 := by
  have inclusion_comparison := fan.primitiveComplementDifferential_inclusion 𝕜 complete regular divisor degree
  have next_comparison := fan.primitiveComplementDifferential_inclusion 𝕜 complete regular divisor (degree + 1)
  have zero_after : fan.primitiveComplementDifferential 𝕜 complete regular divisor degree ≫
      fan.primitiveComplementDifferential 𝕜 complete regular divisor (degree + 1) ≫
        fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor (degree + 2) = 0 := by
    rw [← next_comparison, ← Category.assoc, ← inclusion_comparison, Category.assoc,
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).d_comp_d, comp_zero]
  calc
    _ = (fan.primitiveComplementDifferential 𝕜 complete regular divisor degree ≫
      fan.primitiveComplementDifferential 𝕜 complete regular divisor (degree + 1)) ≫
        (fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor (degree + 2) ≫
          fan.primitiveComplementDegreeRetraction 𝕜 complete regular divisor (degree + 2)) := by
      rw [fan.primitiveComplementDegree_split 𝕜, Category.comp_id]
    _ = 0 := by
      have postcompose := congrArg (fun morphism => morphism ≫
        fan.primitiveComplementDegreeRetraction 𝕜 complete regular divisor (degree + 2)) zero_after
      simpa only [Category.assoc, zero_comp] using postcompose

noncomputable def primitiveComplementComplex (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (fan.primitiveComplementDegree 𝕜 complete regular divisor)
    (fan.primitiveComplementDifferential 𝕜 complete regular divisor)
    (fan.primitiveComplementDifferential_squared 𝕜 complete regular divisor)

noncomputable def primitiveComplementInclusion (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    fan.primitiveComplementComplex 𝕜 complete regular divisor ⟶
      fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor :=
  CochainComplex.ofHom (fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor)
    (fun degree => by
      simpa only [primitiveComplementComplex, CochainComplex.of_d] using
        fan.primitiveComplementDifferential_inclusion 𝕜 complete regular divisor degree)

theorem primitiveComplementDifferential_retraction (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    fan.primitiveComplementDegreeRetraction 𝕜 complete regular divisor degree ≫
        fan.primitiveComplementDifferential 𝕜 complete regular divisor degree =
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).d degree (degree + 1) ≫
        fan.primitiveComplementDegreeRetraction 𝕜 complete regular divisor (degree + 1) := by
  apply splitRetraction_compatible
    (fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor degree)
    (fan.primitiveComplementDegreeInclusion 𝕜 complete regular divisor (degree + 1))
    _ _ _ _ (fan.primitiveComplementDegree_split 𝕜 complete regular divisor (degree + 1))
    (fan.primitiveComplementDifferential_inclusion 𝕜 complete regular divisor degree)
  rw [fan.primitiveComplementDegree_projector 𝕜, fan.primitiveComplementDegree_projector 𝕜]
  exact fan.primitiveCechDegreeProjector_d 𝕜 complete regular divisor degree

noncomputable def primitiveComplementRetraction (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor ⟶
      fan.primitiveComplementComplex 𝕜 complete regular divisor :=
  CochainComplex.ofHom (fan.primitiveComplementDegreeRetraction 𝕜 complete regular divisor)
    (fun degree => by
      simpa only [primitiveComplementComplex, CochainComplex.of_d] using
        fan.primitiveComplementDifferential_retraction 𝕜 complete regular divisor degree)

theorem primitiveComplementComplex_split (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    fan.primitiveComplementInclusion 𝕜 complete regular divisor ≫
        fan.primitiveComplementRetraction 𝕜 complete regular divisor =
      𝟙 (fan.primitiveComplementComplex 𝕜 complete regular divisor) := by
  apply HomologicalComplex.hom_ext
  intro degree
  exact fan.primitiveComplementDegree_split 𝕜 complete regular divisor degree

noncomputable def primitiveNegativeIndicatorComplementComplex (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (negative : Finset fan.Ray) :
    CochainComplex AddCommGrpCat ℕ :=
  fan.primitiveComplementComplex 𝕜 complete regular
    (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ negative then -1 else 0))

theorem primitiveComplementHomology_split (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).map
        (fan.primitiveComplementInclusion 𝕜 complete regular divisor) ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).map
        (fan.primitiveComplementRetraction 𝕜 complete regular divisor) =
      𝟙 ((fan.primitiveComplementComplex 𝕜 complete regular divisor).homology degree) := by
  rw [← CategoryTheory.Functor.map_comp, fan.primitiveComplementComplex_split 𝕜]
  exact CategoryTheory.Functor.map_id _ _

theorem primitiveComplementHomology_inclusion_injective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    Function.Injective
      ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).map
        (fan.primitiveComplementInclusion 𝕜 complete regular divisor)) := by
  apply Function.LeftInverse.injective (g :=
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).map
      (fan.primitiveComplementRetraction 𝕜 complete regular divisor))
  intro element
  exact ConcreteCategory.congr_hom
    (fan.primitiveComplementHomology_split 𝕜 complete regular divisor degree) element

theorem primitiveWeightZeroCechHomology_nontrivial_of_complement (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) [Nontrivial ((fan.primitiveComplementComplex 𝕜 complete regular divisor).homology degree)] :
    Nontrivial ((fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).homology degree) := by
  have injective := fan.primitiveComplementHomology_inclusion_injective 𝕜 complete regular divisor degree
  change Function.Injective (HomologicalComplex.homologyMap
    (fan.primitiveComplementInclusion 𝕜 complete regular divisor) degree) at injective
  exact injective.nontrivial

end TauCeti.Toric.Fan
