module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LatticeDistance
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Quotient.Pi

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

noncomputable section

namespace Submodule

variable (baseRing : Type*) [CommRing baseRing] [IsDomain baseRing] [IsNoetherianRing baseRing] [Ring.KrullDimLE 1 baseRing]
variable (baseField : Type*) [Field baseField] [Algebra baseRing baseField] [IsFractionRing baseRing baseField]
variable (indices : Type*) [Fintype indices] [DecidableEq indices]

def stdEmb : (indices → baseRing) →ₗ[baseRing] (indices → baseField) := (Algebra.linearMap baseRing baseField).compLeft indices

lemma stdEmb_apply (element : indices → baseRing) (row : indices) : stdEmb baseRing baseField indices element row = algebraMap baseRing baseField (element row) := rfl

lemma stdEmb_injective : Function.Injective (stdEmb baseRing baseField indices) := by
  intro element coefficients nonzero
  ext row
  exact IsFractionRing.injective baseRing baseField (congrFun nonzero row)

def stdLattice : Submodule baseRing (indices → baseField) := (⊤ : Submodule baseRing (indices → baseRing)).map (stdEmb baseRing baseField indices)

theorem stdLattice_isLattice : IsLattice baseField (stdLattice baseRing baseField indices) where
  fg := (Module.Finite.fg_top (R := baseRing) (M := indices → baseRing)).map _
  span_eq_top := by
    rw [eq_top_iff]
    intro vector _
    rw [pi_eq_sum_univ' vector]
    refine Submodule.sum_mem _ fun row _ => ?_
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨Pi.single row 1, trivial, ?_⟩
    ext index
    rw [stdEmb_apply]
    by_cases nonzero : index = row
    · subst nonzero; simp
    · simp [Pi.single_eq_of_ne nonzero]

variable {baseRing baseField indices}

abbrev matImage (matrix : Matrix indices indices baseField) : Submodule baseRing (indices → baseField) :=
  (stdLattice baseRing baseField indices).map ((Matrix.toLin' matrix).restrictScalars baseRing)

lemma relLength_top {moduleSpace : Type*} [AddCommGroup moduleSpace] [Module baseRing moduleSpace] (submodule : Submodule baseRing moduleSpace) :
    relLength ⊤ submodule = Module.length baseRing (moduleSpace ⧸ submodule) := by
  unfold relLength
  refine (Submodule.Quotient.equiv _ _ (Submodule.topEquiv (R := baseRing) (M := moduleSpace)) ?_).length_eq
  ext element
  simp [Submodule.submoduleOf]

def diagMul (coefficients : indices → baseRing) : (indices → baseRing) →ₗ[baseRing] (indices → baseRing) :=
  LinearMap.pi fun row => (coefficients row) • LinearMap.proj row

lemma diagMul_apply (coefficients : indices → baseRing) (element : indices → baseRing) (row : indices) : diagMul coefficients element row = coefficients row * element row := rfl

lemma range_diagMul (coefficients : indices → baseRing) :
    LinearMap.range (diagMul coefficients) = Submodule.pi Set.univ fun row => (Ideal.span {coefficients row} : Ideal baseRing) := by
  ext vector
  simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_true_left,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨preimage, rfl⟩ row
    exact ⟨preimage row, by rw [diagMul_apply, mul_comm]⟩
  · intro nonzero
    choose preimage hw using nonzero
    exact ⟨preimage, by ext row; rw [diagMul_apply, mul_comm]; exact hw row⟩

lemma matImage_diagonal (coefficients : indices → baseRing) :
    (matImage (Matrix.diagonal fun row => algebraMap baseRing baseField (coefficients row)) : Submodule baseRing (indices → baseField)) =
      (LinearMap.range (diagMul coefficients)).map (stdEmb baseRing baseField indices) := by
  unfold matImage stdLattice
  rw [← Submodule.map_comp, LinearMap.range_eq_map, ← Submodule.map_comp]
  congr 1
  ext element row
  simp [stdEmb_apply, diagMul_apply, Matrix.mulVec_diagonal]

lemma matImage_diagonal_le (coefficients : indices → baseRing) :
    (matImage (Matrix.diagonal fun row => algebraMap baseRing baseField (coefficients row)) : Submodule baseRing (indices → baseField)) ≤
      stdLattice baseRing baseField indices := by
  rw [matImage_diagonal]
  exact Submodule.map_mono le_top

theorem relLength_matImage_diagonal (coefficients : indices → baseRing) :
    relLength (stdLattice baseRing baseField indices) (matImage (Matrix.diagonal fun row => algebraMap baseRing baseField (coefficients row))) =
      ∑ row, Ring.ord baseRing (coefficients row) := by
  rw [matImage_diagonal, stdLattice, relLength_map _ (stdEmb_injective baseRing baseField indices), relLength_top,
    range_diagMul]
  have quotientComparison := (Submodule.quotientPi
    (fun row : indices => (Ideal.span {coefficients row} : Ideal baseRing))).length_eq
  rw [quotientComparison, Module.length_pi_of_fintype]
  rfl

lemma ordFrac_algebraMap {element : baseRing} (hx : element ≠ 0) :
    Ring.ordFrac baseRing (algebraMap baseRing baseField element) = WithZero.exp ((Ring.ord baseRing element).toNat : ℤ) := by
  rw [Ring.ordFrac_eq_ord baseRing hx]
  exact Ring.ordMonoidWithZeroHom_eq_coe baseRing (mem_nonZeroDivisors_of_ne_zero hx)
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hx))).symm

lemma exp_sum_int {indexType : Type*} (finiteSet : Finset indexType) (summand : indexType → ℤ) :
    (WithZero.exp (∑ row ∈ finiteSet, summand row) : WithZero (Multiplicative ℤ)) = ∏ row ∈ finiteSet, WithZero.exp (summand row) := by
  classical
  induction finiteSet using Finset.induction_on with
  | empty => simp
  | insert element transvection hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, WithZero.exp_add, ih]

lemma toLin'_bijective {matrix : Matrix indices indices baseField} (nonzero : matrix.det ≠ 0) :
    Function.Bijective (Matrix.toLin' matrix) := by
  have hu : IsUnit matrix.det := isUnit_iff_ne_zero.mpr nonzero
  refine Function.bijective_iff_has_inverse.mpr ⟨Matrix.toLin' matrix⁻¹, fun vector => ?_, fun vector => ?_⟩
  · rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hu,
      Matrix.toLin'_one, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hu,
      Matrix.toLin'_one, LinearMap.id_apply]

def DetOrdProp (matrix : Matrix indices indices baseField) : Prop :=
  Ring.ordFrac baseRing matrix.det =
    WithZero.exp (latDist (stdLattice baseRing baseField indices) (matImage (baseRing := baseRing) matrix))

theorem detOrdProp_mul {matrix secondMatrix : Matrix indices indices baseField} (nonzero : matrix.det ≠ 0) (otherNonzero : secondMatrix.det ≠ 0)
    (hN : DetOrdProp (baseRing := baseRing) matrix) (hN' : DetOrdProp (baseRing := baseRing) secondMatrix) :
    DetOrdProp (baseRing := baseRing) (matrix * secondMatrix) := by
  have := stdLattice_isLattice baseRing baseField indices
  unfold DetOrdProp at *
  have hc : (matImage (baseRing := baseRing) (matrix * secondMatrix) : Submodule baseRing (indices → baseField)) =
      (stdLattice baseRing baseField indices).map ((Matrix.toLin' matrix ∘ₗ Matrix.toLin' secondMatrix).restrictScalars baseRing) := by
    unfold matImage; rw [Matrix.toLin'_mul]
  rw [Matrix.det_mul, map_mul, hN, hN', hc,
    latDist_map_comp (baseField := baseField) _ _ (toLin'_bijective nonzero) (toLin'_bijective otherNonzero), WithZero.exp_add]

theorem detOrdProp_diagonal_int (coefficients : indices → baseRing) (hb : ∀ row, coefficients row ≠ 0) :
    DetOrdProp (baseRing := baseRing) (Matrix.diagonal fun row => algebraMap baseRing baseField (coefficients row)) := by
  unfold DetOrdProp
  rw [latDist_of_le (matImage_diagonal_le coefficients), relLength_matImage_diagonal, Matrix.det_diagonal,
    map_prod]
  have h1 : ∀ row, Ring.ord baseRing (coefficients row) = (((Ring.ord baseRing (coefficients row)).toNat : ℕ) : ℕ∞) := fun row =>
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero (hb row)))).symm
  rw [Finset.sum_congr rfl fun row _ => h1 row, ← Nat.cast_sum, ENat.toNat_natCast, Nat.cast_sum,
    exp_sum_int]
  exact Finset.prod_congr rfl fun row _ => ordFrac_algebraMap (hb row)

theorem detOrdProp_diagonal (diagonal : indices → baseField) (hd : (Matrix.diagonal diagonal).det ≠ 0) :
    DetOrdProp (baseRing := baseRing) (Matrix.diagonal diagonal) := by
  have hd' : ∀ row, diagonal row ≠ 0 := by
    rw [Matrix.det_diagonal] at hd
    exact fun row => (Finset.prod_ne_zero_iff.mp hd) row (Finset.mem_univ row)
  have hex : ∀ row, ∃ coefficients scalar : baseRing, coefficients ≠ 0 ∧ scalar ≠ 0 ∧ diagonal row * algebraMap baseRing baseField scalar = algebraMap baseRing baseField coefficients := by
    intro row
    obtain ⟨coefficients, scalar, hc, hbc⟩ := IsFractionRing.div_surjective (A := baseRing) (diagonal row)
    have hc0 : algebraMap baseRing baseField scalar ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective baseRing baseField)).mpr (nonZeroDivisors.ne_zero hc)
    refine ⟨coefficients, scalar, ?_, nonZeroDivisors.ne_zero hc, ?_⟩
    · rintro rfl
      rw [map_zero, zero_div] at hbc
      exact hd' row hbc.symm
    · rw [← hbc, div_mul_cancel₀ _ hc0]
  choose coefficients scalar hb hc hbc using hex
  have hmul : Matrix.diagonal diagonal * Matrix.diagonal (fun row => algebraMap baseRing baseField (scalar row)) =
      Matrix.diagonal fun row => algebraMap baseRing baseField (coefficients row) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext row
    exact hbc row
  have hcdet : (Matrix.diagonal fun row => algebraMap baseRing baseField (scalar row)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun row _ =>
      (map_ne_zero_iff _ (IsFractionRing.injective baseRing baseField)).mpr (hc row)
  have hB := detOrdProp_diagonal_int (baseField := baseField) coefficients hb
  have hC := detOrdProp_diagonal_int (baseField := baseField) scalar hc
  have := stdLattice_isLattice baseRing baseField indices
  unfold DetOrdProp at *
  have hcomp : (matImage (baseRing := baseRing) (Matrix.diagonal fun row => algebraMap baseRing baseField (coefficients row)) :
      Submodule baseRing (indices → baseField)) = (stdLattice baseRing baseField indices).map ((Matrix.toLin' (Matrix.diagonal diagonal) ∘ₗ
        Matrix.toLin' (Matrix.diagonal fun row => algebraMap baseRing baseField (scalar row))).restrictScalars baseRing) := by
    unfold matImage; rw [← hmul, Matrix.toLin'_mul]
  rw [hcomp, latDist_map_comp (baseField := baseField) _ _ (toLin'_bijective hd) (toLin'_bijective hcdet),
    WithZero.exp_add, ← hC, ← hmul, Matrix.det_mul, map_mul] at hB
  have hne : Ring.ordFrac baseRing (Matrix.diagonal fun row => algebraMap baseRing baseField (scalar row)).det ≠ 0 :=
    (map_ne_zero _).mpr hcdet
  exact mul_right_cancel₀ hne hB

lemma transvection_mulVec (row column : indices) (scalar : baseField) (vector : indices → baseField) :
    (Matrix.transvection row column scalar).mulVec vector = vector + Pi.single row (scalar * vector column) := by
  ext index
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  congr 1
  by_cases nonzero : index = row
  · subst nonzero
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Ne.symm nonzero]

def auxLattice (column : indices) (denominator : baseRing) : Submodule baseRing (indices → baseField) :=
  matImage (baseRing := baseRing) (Matrix.diagonal fun index => if index = column then algebraMap baseRing baseField denominator else 1)

lemma transvection_auxLattice_le (row column : indices) (hij : row ≠ column) (numerator denominator : baseRing)
    (hq : algebraMap baseRing baseField denominator ≠ 0) :
    (auxLattice (baseField := baseField) column denominator).map ((Matrix.toLin' (Matrix.transvection row column
      (algebraMap baseRing baseField numerator / algebraMap baseRing baseField denominator))).restrictScalars baseRing) ≤ auxLattice (baseField := baseField) column denominator := by
  rintro _ ⟨_, ⟨_, ⟨element, -, rfl⟩, rfl⟩, rfl⟩
  refine ⟨stdEmb baseRing baseField indices (element + Pi.single row (numerator * element column)), ⟨_, trivial, rfl⟩, ?_⟩
  simp only [LinearMap.coe_restrictScalars, Matrix.toLin'_apply, transvection_mulVec]
  ext index
  simp only [Pi.add_apply, Matrix.mulVec_diagonal, stdEmb_apply, ite_true, map_add]
  by_cases hk : index = row
  · subst hk
    simp only [Pi.single_eq_same, ite_eq_right hij, one_mul, map_mul]
    field_simp
  · simp [Pi.single_eq_of_ne hk]

theorem detOrdProp_transvection (transvection : Matrix.TransvectionStruct indices baseField) :
    DetOrdProp (baseRing := baseRing) transvection.toMatrix := by
  obtain ⟨row, column, hij, scalar⟩ := transvection
  obtain ⟨numerator, denominator, hq, rfl⟩ := IsFractionRing.div_surjective (A := baseRing) scalar
  have hq0 : algebraMap baseRing baseField denominator ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective baseRing baseField)).mpr (nonZeroDivisors.ne_zero hq)
  have hM₀ := stdLattice_isLattice baseRing baseField indices
  set scalar := algebraMap baseRing baseField numerator / algebraMap baseRing baseField denominator with hc
  have hdet : (Matrix.transvection row column scalar).det = 1 := Matrix.det_transvection_of_ne row column hij scalar
  have hbij : Function.Bijective (Matrix.toLin' (Matrix.transvection row column scalar)) :=
    toLin'_bijective (by rw [hdet]; exact one_ne_zero)
  have hDq : (Matrix.diagonal fun index => if index = column then algebraMap baseRing baseField denominator else 1).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun index _ => ?_
    split_ifs
    · exact hq0
    · exact one_ne_zero
  have hMq : IsLattice baseField (auxLattice (baseField := baseField) column denominator) :=
    IsLattice.map' _ (toLin'_bijective hDq).2 _
  have hle := transvection_auxLattice_le (baseField := baseField) row column hij numerator denominator hq0
  have hle' := transvection_auxLattice_le (baseField := baseField) row column hij (-numerator) denominator hq0
  have hneg : algebraMap baseRing baseField (-numerator) / algebraMap baseRing baseField denominator = -scalar := by rw [map_neg, neg_div]
  rw [hneg] at hle'
  have hcomp : Matrix.toLin' (Matrix.transvection row column scalar) ∘ₗ
      Matrix.toLin' (Matrix.transvection row column (-scalar)) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, Matrix.transvection_mul_transvection_same _ _ hij, add_neg_cancel,
      Matrix.transvection_zero, Matrix.toLin'_one]
  have heq : (auxLattice (baseField := baseField) column denominator).map
      ((Matrix.toLin' (Matrix.transvection row column scalar)).restrictScalars baseRing) = auxLattice (baseField := baseField) column denominator := by
    refine le_antisymm hle ?_
    calc auxLattice (baseField := baseField) column denominator
        = (auxLattice (baseField := baseField) column denominator).map ((Matrix.toLin' (Matrix.transvection row column scalar) ∘ₗ
            Matrix.toLin' (Matrix.transvection row column (-scalar))).restrictScalars baseRing) := by
          rw [hcomp]; exact (Submodule.map_id _).symm
      _ = ((auxLattice (baseField := baseField) column denominator).map ((Matrix.toLin'
            (Matrix.transvection row column (-scalar))).restrictScalars baseRing)).map
              ((Matrix.toLin' (Matrix.transvection row column scalar)).restrictScalars baseRing) := by
          rw [← Submodule.map_comp]; rfl
      _ ≤ _ := Submodule.map_mono hle'
  unfold DetOrdProp
  show Ring.ordFrac baseRing (Matrix.transvection row column scalar).det = _
  rw [hdet, map_one]
  show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (latDist (stdLattice baseRing baseField indices)
    ((stdLattice baseRing baseField indices).map ((Matrix.toLin' (Matrix.transvection row column scalar)).restrictScalars baseRing)))
  rw [latDist_map_indep (baseField := baseField) _ hbij (stdLattice baseRing baseField indices) (auxLattice (baseField := baseField) column denominator), heq,
    latDist_self, WithZero.exp_zero]

theorem detOrdProp_of_det_ne_zero (matrix : Matrix indices indices baseField) (nonzero : matrix.det ≠ 0) : DetOrdProp (baseRing := baseRing) matrix :=
  Matrix.diagonal_transvection_induction_of_det_ne_zero (DetOrdProp (baseRing := baseRing)) matrix nonzero
    (fun diagonal hd => detOrdProp_diagonal diagonal hd) detOrdProp_transvection
    (fun _ _ hA hB PA PB => detOrdProp_mul hA hB PA PB)

variable {ambient : Type*} [AddCommGroup ambient] [Module baseRing ambient] [Module baseField ambient] [IsScalarTower baseRing baseField ambient]
  [Module.Finite baseField ambient]

theorem ordFrac_det_eq_exp_latDist (lattice : Submodule baseRing ambient) [IsLattice baseField lattice] (linearMap : ambient →ₗ[baseField] ambient)
    (hφ : LinearMap.det linearMap ≠ 0) :
    Ring.ordFrac baseRing (LinearMap.det linearMap) =
      WithZero.exp (latDist lattice (lattice.map (linearMap.restrictScalars baseRing))) := by
  classical
  let coefficients := Module.finBasis baseField ambient
  let equivalence : ambient ≃ₗ[baseField] (Fin (Module.finrank baseField ambient) → baseField) := coefficients.equivFun
  let equivalenceMap : ambient →ₗ[baseField] (Fin (Module.finrank baseField ambient) → baseField) := equivalence.toLinearMap
  let conjugateMap : (Fin (Module.finrank baseField ambient) → baseField) →ₗ[baseField] (Fin (Module.finrank baseField ambient) → baseField) :=
    equivalenceMap ∘ₗ linearMap ∘ₗ equivalence.symm.toLinearMap
  let matrix := LinearMap.toMatrix' conjugateMap
  have hN : Matrix.toLin' matrix = conjugateMap := Matrix.toLin'_toMatrix' conjugateMap
  have hdet : matrix.det = LinearMap.det linearMap := by
    rw [← LinearMap.det_toLin', hN]
    exact LinearMap.det_conj linearMap equivalence
  have hP := detOrdProp_of_det_ne_zero (baseRing := baseRing) matrix (by rw [hdet]; exact hφ)
  unfold DetOrdProp matImage at hP
  rw [hdet, hN] at hP
  rw [hP]
  congr 1
  have hM₀ := stdLattice_isLattice baseRing baseField (Fin (Module.finrank baseField ambient))
  have hbij : Function.Bijective conjugateMap := by
    rw [← hN]; exact toLin'_bijective (by rw [hdet]; exact hφ)
  have heM : IsLattice baseField (lattice.map (equivalenceMap.restrictScalars baseRing)) :=
    IsLattice.map' _ equivalence.surjective lattice
  rw [latDist_map_indep (baseField := baseField) conjugateMap hbij _ (lattice.map (equivalenceMap.restrictScalars baseRing)),
    ← latDist_map (baseRing := baseRing) equivalenceMap equivalence.injective lattice (lattice.map (linearMap.restrictScalars baseRing))]
  congr 1
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext vector
  simp [conjugateMap, equivalenceMap]

theorem ordFrac_det_eq_exp_relLength (lattice : Submodule baseRing ambient) [IsLattice baseField lattice] (linearMap : ambient →ₗ[baseField] ambient)
    (hφ : LinearMap.det linearMap ≠ 0) (hle : lattice.map (linearMap.restrictScalars baseRing) ≤ lattice) :
    Ring.ordFrac baseRing (LinearMap.det linearMap) =
      WithZero.exp (((relLength lattice (lattice.map (linearMap.restrictScalars baseRing))).toNat : ℕ) : ℤ) := by
  rw [ordFrac_det_eq_exp_latDist lattice linearMap hφ, latDist_of_le hle]

end Submodule

end
