module

public import BondalThomsen.Toric.Cohomology.PrimitiveWeightZeroComplex
public import BondalThomsen.Fan.PrimitiveRelationExistence
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Preadditive
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.ToricPrimitiveWeightZeroComplex
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ToricPrimitiveBoundaryCechNonvanishing

noncomputable def labelDeterminant {Index : Type*} (size : ℕ)
    (labels : Index → Fin size) (tuple : Fin size → Index) : 𝕜 :=
  Matrix.det (fun row column => if labels (tuple column) = row then 1 else 0 : Matrix (Fin size) (Fin size) 𝕜)

theorem labelDeterminant_zero_of_missing {Index : Type*} (size : ℕ)
    (labels : Index → Fin size) (tuple : Fin size → Index)
    (missing : Fin size) (absent : ∀ column, labels (tuple column) ≠ missing) :
    labelDeterminant 𝕜 size labels tuple = 0 := by
  unfold labelDeterminant
  apply Matrix.det_eq_zero_of_row_eq_zero missing
  intro column
  simp [absent column]

theorem labelDeterminant_identity {Index : Type*} (size : ℕ)
    (labels : Index → Fin size) (tuple : Fin size → Index)
    (identity : ∀ column, labels (tuple column) = column) :
    labelDeterminant 𝕜 size labels tuple = 1 := by
  have matrix_eq : (fun row column => if labels (tuple column) = row then 1 else 0 : Matrix (Fin size) (Fin size) 𝕜) =
      (1 : Matrix (Fin size) (Fin size) 𝕜) := by
    ext row column
    simp only [Matrix.one_apply, identity, eq_comm]
  unfold labelDeterminant
  exact (congrArg Matrix.det matrix_eq).trans Matrix.det_one

theorem labelDeterminant_cocycle {Index : Type*} (size : ℕ)
    (labels : Index → Fin size) (tuple : Fin (size + 1) → Index) :
    ∑ deleted : Fin (size + 1), (-1 : 𝕜) ^ deleted.val *
      labelDeterminant 𝕜 size labels (tuple ∘ deleted.succAbove) = 0 := by
  let augmented : Matrix (Fin (size + 1)) (Fin (size + 1)) 𝕜 :=
    fun row column => Fin.cases 1
      (fun label => if labels (tuple column) = label then 1 else 0) row
  let coefficients : Fin (size + 1) → 𝕜 := Fin.cases 0 (fun _label => 1)
  have sum_eq : (∑ row, coefficients row • augmented row) = augmented 0 := by
    funext column
    simp [coefficients, augmented, Fin.sum_univ_succ, Finset.sum_apply]
  have zero_det := Matrix.det_updateRow_sum augmented 0 coefficients
  rw [sum_eq, Matrix.updateRow_eq_self] at zero_det
  have determinant_zero : augmented.det = 0 := by simpa [coefficients] using zero_det
  rw [Matrix.det_succ_row_zero] at determinant_zero
  calc
    _ = ∑ deleted : Fin (size + 1), (-1 : 𝕜) ^ deleted.val * augmented 0 deleted *
        (augmented.submatrix Fin.succ deleted.succAbove).det := by
      apply Finset.sum_congr rfl
      intro deleted _member
      have minor_eq : augmented.submatrix Fin.succ deleted.succAbove =
          (fun row column => if labels (tuple (deleted.succAbove column)) = row then 1 else 0 :
            Matrix (Fin size) (Fin size) 𝕜) := by
        ext row column
        simp [augmented, Matrix.submatrix_apply]
      rw [minor_eq]
      simp only [augmented, Fin.cases_zero, mul_one, labelDeterminant, Function.comp_apply]
    _ = 0 := determinant_zero

theorem sumHom_scalar_apply {Index : Type*} (source : AddCommGrpCat.{0})
    (coefficient : AddSubgroup 𝕜) (finite : Finset Index)
    (maps : Index → (source ⟶ AddCommGrpCat.of coefficient)) (element : source) :
    ((AddCommGrpCat.Hom.hom
      (∑ index ∈ finite, maps index : source ⟶ AddCommGrpCat.of coefficient)) element).val =
      ∑ index ∈ finite, ((AddCommGrpCat.Hom.hom (maps index)) element).val := by
  classical
  induction finite using Finset.induction_on with
  | empty => simp [AddCommGrpCat.hom_zero]
  | @insert index rest absent induction =>
    simp only [Finset.sum_insert absent, AddCommGrpCat.hom_add, AddMonoidHom.add_apply,
      AddSubgroup.coe_add, induction]

end BondalThomsen.ToricPrimitiveBoundaryCechNonvanishing

namespace TauCeti.Toric.Fan

open BondalThomsen.ToricPrimitiveBoundaryCechNonvanishing

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem exists_primitiveRay_not_mem_cone (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {rays : Finset fan.Ray} (primitive : fan.IsPrimitiveCollection rays)
    (cone : fan.cones) : ∃ ray ∈ rays, embedding ray.val ∉ cone.val := by
  by_contra no_missing
  push Not at no_missing
  let basisData := fan.divisorChartBasis complete regular cone
  apply primitive.2.1
  apply fan.finiteRayHull_mem_of_basis_generators regular basisData.val.2 basisData.property.1 rays
  intro ray member
  exact fan.ray_eq_basis_of_mem_coneBasis basisData.val.2 basisData.property.1 ray
    (basisData.property.2.le (no_missing ray member))

theorem divisorLocalCone_contains_cone (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (cone : fan.cones) :
    cone ≤ fan.divisorLocalCone 𝕜 complete regular ((Finite.equivFin fan.cones) cone) := by
  change cone.val ≤ (fan.divisorChartCone complete regular
    ((Finite.equivFin fan.cones).symm ((Finite.equivFin fan.cones) cone))).val
  rw [Equiv.symm_apply_apply]
  exact (fan.divisorChartBasis complete regular cone).property.2.le

noncomputable def primitiveBoundaryFacetChart (fan : Fan embedding)
    (_complete : fan.IsComplete) (_regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) (ray : rays) : Fin (Nat.card fan.cones) :=
  (Finite.equivFin fan.cones) ⟨fan.finiteRayHull (rays.erase ray.val),
    primitive.proper_subset_hull_mem (Finset.erase_ssubset ray.property)⟩

theorem primitiveBoundaryFacetChart_contains (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) (deleted : rays)
    (ray : fan.Ray) (member : ray ∈ rays) (different : ray ≠ deleted.val) :
    embedding ray.val ∈ (fan.divisorLocalCone 𝕜 complete regular
      (fan.primitiveBoundaryFacetChart complete regular rays primitive deleted)).val := by
  apply fan.divisorLocalCone_contains_cone 𝕜 complete regular _
  exact PointedCone.subset_hull ⟨ray, Finset.mem_erase.mpr ⟨different, member⟩, rfl⟩

noncomputable def primitiveBoundaryEnumeration (fan : Fan embedding)
    (rays : Finset fan.Ray) {size : ℕ} (cardinality : rays.card = size) : Fin size ≃ rays :=
  (Finset.equivFinOfCardEq cardinality).symm

noncomputable def primitiveBoundaryOmittedLabel (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) {size : ℕ} (cardinality : rays.card = size)
    (index : Fin (Nat.card fan.cones)) : Fin size :=
  (fan.primitiveBoundaryEnumeration rays cardinality).symm
    ⟨(fan.exists_primitiveRay_not_mem_cone complete regular primitive
      (fan.divisorLocalCone 𝕜 complete regular index)).choose,
      (fan.exists_primitiveRay_not_mem_cone complete regular primitive
        (fan.divisorLocalCone 𝕜 complete regular index)).choose_spec.1⟩

theorem primitiveBoundaryOmittedLabel_absent (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) {size : ℕ} (cardinality : rays.card = size)
    (index : Fin (Nat.card fan.cones)) :
    embedding ((fan.primitiveBoundaryEnumeration rays cardinality)
      (fan.primitiveBoundaryOmittedLabel 𝕜 complete regular rays primitive cardinality index)).val.val ∉
        (fan.divisorLocalCone 𝕜 complete regular index).val := by
  unfold primitiveBoundaryOmittedLabel
  rw [Equiv.apply_symm_apply]
  exact (fan.exists_primitiveRay_not_mem_cone complete regular primitive
    (fan.divisorLocalCone 𝕜 complete regular index)).choose_spec.2

theorem primitiveBoundaryOmittedLabel_facet (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) {size : ℕ} (cardinality : rays.card = size)
    (label : Fin size) :
    fan.primitiveBoundaryOmittedLabel 𝕜 complete regular rays primitive cardinality
        (fan.primitiveBoundaryFacetChart complete regular rays primitive
          ((fan.primitiveBoundaryEnumeration rays cardinality) label)) = label := by
  apply (fan.primitiveBoundaryEnumeration rays cardinality).injective
  apply Subtype.ext
  by_contra different
  exact fan.primitiveBoundaryOmittedLabel_absent 𝕜 complete regular rays primitive cardinality _
    (fan.primitiveBoundaryFacetChart_contains 𝕜 complete regular rays primitive _ _
      ((fan.primitiveBoundaryEnumeration rays cardinality) _).property different)

theorem primitiveBoundaryTupleAvailable_of_surjective_labels (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) {size degree : ℕ} (cardinality : rays.card = size)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (surjective : Function.Surjective
      (fan.primitiveBoundaryOmittedLabel 𝕜 complete regular rays primitive cardinality ∘ tuple)) :
    fan.primitiveCechTupleAvailable 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) degree tuple := by
  apply (fan.primitiveCechTupleAvailable_negativeIndicator 𝕜 complete regular rays degree tuple).mpr
  intro ray member contains
  let label := (fan.primitiveBoundaryEnumeration rays cardinality).symm ⟨ray, member⟩
  obtain ⟨column, same⟩ := surjective label
  have ray_eq : (fan.primitiveBoundaryEnumeration rays cardinality)
      (fan.primitiveBoundaryOmittedLabel 𝕜 complete regular rays primitive cardinality (tuple column)) =
      (⟨ray, member⟩ : rays) := by
    rw [show fan.primitiveBoundaryOmittedLabel 𝕜 complete regular rays primitive cardinality (tuple column) = label from same]
    exact Equiv.apply_symm_apply _ _
  have absent := fan.primitiveBoundaryOmittedLabel_absent 𝕜 complete regular rays primitive cardinality (tuple column)
  rw [ray_eq] at absent
  exact absent (fan.primitiveCechCone_le_chart 𝕜 complete regular degree tuple column contains)

noncomputable def primitiveBoundaryCocycleCoefficient (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) (degree : ℕ) (cardinality : rays.card = degree + 1)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechScalarCoefficient 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) degree tuple := by
  refine ⟨labelDeterminant 𝕜 (degree + 1)
    (fan.primitiveBoundaryOmittedLabel 𝕜 complete regular rays primitive cardinality) tuple, ?_⟩
  intro unavailable
  by_cases surjective : Function.Surjective
      (fan.primitiveBoundaryOmittedLabel 𝕜 complete regular rays primitive cardinality ∘ tuple)
  · exact (unavailable (fan.primitiveBoundaryTupleAvailable_of_surjective_labels 𝕜 complete regular
      rays primitive cardinality tuple surjective)).elim
  · unfold Function.Surjective at surjective
    push Not at surjective
    obtain ⟨missing, absent⟩ := surjective
    exact labelDeterminant_zero_of_missing 𝕜 _ _ _ missing absent

noncomputable def primitiveBoundaryCocycle (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) (degree : ℕ) (cardinality : rays.card = degree + 1) :
    (fan.primitiveNegativeIndicatorComplementComplex 𝕜 complete regular rays).X degree :=
  (productElementsEquiv (fan.primitiveComplementCoefficient 𝕜 complete regular
    (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) degree)).symm
      (fan.primitiveBoundaryCocycleCoefficient 𝕜 complete regular rays primitive degree cardinality)

theorem primitiveComplementDifferential_scalar_component (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (element : fan.primitiveComplementDegree 𝕜 complete regular divisor degree)
    (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones)) :
    (productElementsEquiv (fan.primitiveComplementCoefficient 𝕜 complete regular divisor (degree + 1))
      (fan.primitiveComplementDifferential 𝕜 complete regular divisor degree element) tuple).val =
      ∑ deleted : Fin (degree + 2), (-1 : 𝕜) ^ deleted.val *
        (productElementsEquiv (fan.primitiveComplementCoefficient 𝕜 complete regular divisor degree)
          element (tuple ∘ deleted.succAbove)).val := by
  rw [productElementsEquiv_apply]
  change ((AddCommGrpCat.Hom.hom
    (fan.primitiveComplementDifferential 𝕜 complete regular divisor degree ≫
      Limits.Pi.π (fan.primitiveComplementCoefficient 𝕜 complete regular divisor (degree + 1)) tuple)) element).val = _
  unfold primitiveComplementDifferential
  rw [sum_comp]
  refine (sumHom_scalar_apply 𝕜 _
    (fan.primitiveCechScalarCoefficient 𝕜 complete regular divisor (degree + 1) tuple) Finset.univ
    (fun deleted : Fin (degree + 2) =>
      ((-1 : ℤ) ^ deleted.val • fan.primitiveComplementCoface 𝕜 complete regular divisor degree deleted) ≫
        Limits.Pi.π (fan.primitiveComplementCoefficient 𝕜 complete regular divisor (degree + 1)) tuple) element).trans ?_
  apply Finset.sum_congr rfl
  intro deleted _member
  simp only [zsmul_comp, AddCommGrpCat.hom_zsmul,
    AddMonoidHom.zsmul_apply, AddSubgroup.coe_zsmul]
  rw [primitiveComplementCoface, Limits.Pi.lift_comp_π]
  change ((-1 : ℤ) ^ deleted.val) •
      (Limits.Pi.π (fan.primitiveComplementCoefficient 𝕜 complete regular divisor degree)
        (tuple ∘ deleted.succAbove) element).val = _
  rw [← productElementsEquiv_apply]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

theorem primitiveBoundaryCocycle_closed (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) (degree : ℕ) (cardinality : rays.card = degree + 1) :
    (fan.primitiveNegativeIndicatorComplementComplex 𝕜 complete regular rays).d degree (degree + 1)
        (fan.primitiveBoundaryCocycle 𝕜 complete regular rays primitive degree cardinality) = 0 := by
  apply (productElementsEquiv (fan.primitiveComplementCoefficient 𝕜 complete regular
    (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) (degree + 1))).injective
  funext tuple
  apply Subtype.ext
  simp only [primitiveNegativeIndicatorComplementComplex, primitiveComplementComplex,
    CochainComplex.of_d, map_zero, Pi.zero_apply, AddSubgroup.coe_zero]
  change (productElementsEquiv _ (fan.primitiveComplementDifferential 𝕜 complete regular _ degree
      (fan.primitiveBoundaryCocycle 𝕜 complete regular rays primitive degree cardinality)) tuple).val = 0
  rw [fan.primitiveComplementDifferential_scalar_component 𝕜]
  have coefficients : ∀ faceTuple : Fin (degree + 1) → Fin (Nat.card fan.cones),
      (productElementsEquiv (fan.primitiveComplementCoefficient 𝕜 complete regular
        (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) degree)
        (fan.primitiveBoundaryCocycle 𝕜 complete regular rays primitive degree cardinality) faceTuple).val =
      labelDeterminant 𝕜 (degree + 1)
        (fan.primitiveBoundaryOmittedLabel 𝕜 complete regular rays primitive cardinality) faceTuple := by
    intro faceTuple
    change (productElementsEquiv (fan.primitiveComplementCoefficient 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) degree)
      ((productElementsEquiv (fan.primitiveComplementCoefficient 𝕜 complete regular
        (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) degree)).symm
        (fan.primitiveBoundaryCocycleCoefficient 𝕜 complete regular rays primitive degree cardinality)) faceTuple).val = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  simp only [coefficients]
  exact labelDeterminant_cocycle 𝕜 _ _ tuple

noncomputable def primitiveBoundaryFacetTuple (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) {size : ℕ} (cardinality : rays.card = size) :
    Fin size → Fin (Nat.card fan.cones) :=
  fun label => fan.primitiveBoundaryFacetChart complete regular rays primitive
    ((fan.primitiveBoundaryEnumeration rays cardinality) label)

theorem primitiveBoundaryCocycle_facet_value (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) (degree : ℕ) (cardinality : rays.card = degree + 1) :
    (productElementsEquiv (fan.primitiveComplementCoefficient 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) degree)
      (fan.primitiveBoundaryCocycle 𝕜 complete regular rays primitive degree cardinality)
      (fan.primitiveBoundaryFacetTuple complete regular rays primitive cardinality)).val = 1 := by
  change (productElementsEquiv _ ((productElementsEquiv
    (fan.primitiveComplementCoefficient 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) degree)).symm
      (fan.primitiveBoundaryCocycleCoefficient 𝕜 complete regular rays primitive degree cardinality)) _).val = 1
  rw [AddEquiv.apply_symm_apply]
  exact labelDeterminant_identity 𝕜 _ _ _
    (fan.primitiveBoundaryOmittedLabel_facet 𝕜 complete regular rays primitive cardinality)

theorem primitiveBoundaryFacetTuple_face_unavailable (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) (previous : ℕ) (cardinality : rays.card = previous + 2)
    (deleted : Fin (previous + 2)) :
    ¬fan.primitiveCechTupleAvailable 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) previous
      (fan.primitiveBoundaryFacetTuple complete regular rays primitive cardinality ∘ deleted.succAbove) := by
  intro available
  let omitted := (fan.primitiveBoundaryEnumeration rays cardinality) deleted
  have contains : embedding omitted.val.val ∈
      (fan.primitiveCechCone 𝕜 complete regular previous
        (fan.primitiveBoundaryFacetTuple complete regular rays primitive cardinality ∘ deleted.succAbove)).val := by
    have all_contain : ∀ index : Fin (previous + 1),
        embedding omitted.val.val ∈ (fan.divisorLocalCone 𝕜 complete regular
          (fan.primitiveBoundaryFacetTuple complete regular rays primitive cardinality (deleted.succAbove index))).val := by
      intro index
      apply fan.primitiveBoundaryFacetChart_contains 𝕜 complete regular rays primitive _ _ omitted.property
      intro same
      have subtype_same : omitted = (fan.primitiveBoundaryEnumeration rays cardinality) (deleted.succAbove index) :=
        Subtype.ext same
      have label_same := (fan.primitiveBoundaryEnumeration rays cardinality).injective subtype_same
      exact Fin.succAbove_ne deleted index label_same.symm
    have hull_le := (fan.le_primitiveCechCone_iff 𝕜 complete regular
      ⟨ℝ ∙₊ embedding omitted.val.val, omitted.val.property.2⟩ previous
      (fan.primitiveBoundaryFacetTuple complete regular rays primitive cardinality ∘ deleted.succAbove)).mpr
        (fun index => Submodule.span_le.mpr (by
          intro vector member
          have same := Set.mem_singleton_iff.mp member
          subst vector
          exact all_contain index))
    exact hull_le (PointedCone.subset_hull (Set.mem_singleton _))
  exact (fan.primitiveCechTupleAvailable_negativeIndicator 𝕜 complete regular rays previous _).mp available
    omitted.val omitted.property contains

theorem primitiveBoundaryCoboundary_facet_value (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) (previous : ℕ) (cardinality : rays.card = previous + 2)
    (element : (fan.primitiveNegativeIndicatorComplementComplex 𝕜 complete regular rays).X previous) :
    (productElementsEquiv (fan.primitiveComplementCoefficient 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) (previous + 1))
      ((fan.primitiveNegativeIndicatorComplementComplex 𝕜 complete regular rays).d previous (previous + 1) element)
      (fan.primitiveBoundaryFacetTuple complete regular rays primitive cardinality)).val = 0 := by
  simp only [primitiveNegativeIndicatorComplementComplex, primitiveComplementComplex, CochainComplex.of_d]
  change (productElementsEquiv _ (fan.primitiveComplementDifferential 𝕜 complete regular _ previous element) _).val = 0
  rw [fan.primitiveComplementDifferential_scalar_component 𝕜]
  apply Finset.sum_eq_zero
  intro deleted _member
  have zero_coefficient := (productElementsEquiv (fan.primitiveComplementCoefficient 𝕜 complete regular
    (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0)) previous) element
      (fan.primitiveBoundaryFacetTuple complete regular rays primitive cardinality ∘ deleted.succAbove)).property
    (fan.primitiveBoundaryFacetTuple_face_unavailable 𝕜 complete regular rays primitive previous cardinality deleted)
  rw [zero_coefficient, mul_zero]

theorem primitiveBoundaryCocycle_not_coboundary (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) (previous : ℕ) (cardinality : rays.card = previous + 2) :
    ¬∃ element : (fan.primitiveNegativeIndicatorComplementComplex 𝕜 complete regular rays).X previous,
      (fan.primitiveNegativeIndicatorComplementComplex 𝕜 complete regular rays).d previous (previous + 1) element =
        fan.primitiveBoundaryCocycle 𝕜 complete regular rays primitive (previous + 1) cardinality := by
  rintro ⟨element, same⟩
  have zero_value := fan.primitiveBoundaryCoboundary_facet_value 𝕜 complete regular rays primitive previous cardinality element
  rw [same, fan.primitiveBoundaryCocycle_facet_value 𝕜] at zero_value
  exact one_ne_zero zero_value

theorem primitiveBoundaryComplementHomology_nontrivial (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) (previous : ℕ) (cardinality : rays.card = previous + 2) :
    Nontrivial ((fan.primitiveNegativeIndicatorComplementComplex 𝕜 complete regular rays).homology (previous + 1)) := by
  by_contra trivial
  let complex := fan.primitiveNegativeIndicatorComplementComplex 𝕜 complete regular rays
  let : Subsingleton (complex.homology (previous + 1)) := not_nontrivial_iff_subsingleton.mp trivial
  have exact_at : complex.ExactAt (previous + 1) :=
    (complex.exactAt_iff_isZero_homology (previous + 1)).mpr (AddCommGrpCat.isZero_of_subsingleton _)
  have exact_sequence : (complex.sc' previous (previous + 1) (previous + 2)).Exact :=
    (complex.exactAt_iff' previous (previous + 1) (previous + 2)
      ((ComplexShape.up ℕ).prev_eq' (ComplexShape.up_mk _ _ rfl))
      ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk _ _ rfl))).mp exact_at
  have coboundary := (ShortComplex.ab_exact_iff _).mp exact_sequence
    (fan.primitiveBoundaryCocycle 𝕜 complete regular rays primitive (previous + 1) cardinality)
    (fan.primitiveBoundaryCocycle_closed 𝕜 complete regular rays primitive (previous + 1) cardinality)
  exact fan.primitiveBoundaryCocycle_not_coboundary 𝕜 complete regular rays primitive previous cardinality coboundary

theorem primitiveBoundaryComplementHomology_card_nontrivial (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) :
    Nontrivial ((fan.primitiveNegativeIndicatorComplementComplex 𝕜 complete regular rays).homology (rays.card - 1)) := by
  have size := primitive.two_le_card regular
  have cardinality : rays.card = (rays.card - 2) + 2 := by omega
  have degree_eq : (rays.card - 2) + 1 = rays.card - 1 := by omega
  have nontrivial := fan.primitiveBoundaryComplementHomology_nontrivial 𝕜 complete regular rays primitive
    (rays.card - 2) cardinality
  rwa [degree_eq] at nontrivial

theorem primitiveBoundaryActualCechHomology_nontrivial (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) :
    Nontrivial ((fan.primitiveWeightZeroCechComplex 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0))).homology (rays.card - 1)) := by
  let : Nontrivial ((fan.primitiveComplementComplex 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0))).homology
        (rays.card - 1)) := by
    have nontrivial := fan.primitiveBoundaryComplementHomology_card_nontrivial 𝕜 complete regular rays primitive
    change Nontrivial ((fan.primitiveComplementComplex 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0))).homology
        (rays.card - 1)) at nontrivial
    exact nontrivial
  exact fan.primitiveWeightZeroCechHomology_nontrivial_of_complement 𝕜 complete regular _ (rays.card - 1)

end TauCeti.Toric.Fan
