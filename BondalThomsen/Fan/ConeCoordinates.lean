module

public import BondalThomsen.Fan.Completeness
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace BondalThomsen

open Set Module Matrix

variable {Index Ambient : Type*} [Fintype Index] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient]

theorem mem_basisCone_iff (basis : Basis Index ℝ Ambient) (point : Ambient) :
    point ∈ PointedCone.hull ℝ (Set.range basis) ↔
      ∀ index, 0 ≤ basis.repr point index := by
  classical
  constructor
  · intro member
    induction member using Submodule.span_induction with
    | mem vector member =>
      obtain ⟨index, rfl⟩ := member
      intro row
      simp only [Basis.repr_self_apply]
      split_ifs <;> norm_num
    | zero => intro index; simp
    | add first second _ _ first_nonnegative second_nonnegative =>
      intro index
      simpa only [map_add, Finsupp.add_apply] using
        add_nonneg (first_nonnegative index) (second_nonnegative index)
    | smul scalar vector _ nonnegative =>
      intro index
      change 0 ≤ basis.repr ((scalar : ℝ) • vector) index
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
        mul_nonneg scalar.property (nonnegative index)
  · intro nonnegative
    rw [← basis.sum_repr point]
    exact Submodule.sum_mem _ fun index _ =>
      PointedCone.smul_mem _ (nonnegative index) (PointedCone.subset_hull ⟨index, rfl⟩)

theorem isOpen_positive_basisCoordinates (basis : Basis Index ℝ Ambient) :
    IsOpen {point : Ambient | ∀ index, 0 < basis.repr point index} := by
  let := Module.Finite.of_basis basis
  have locus_eq : {point : Ambient | ∀ index, 0 < basis.repr point index} =
      ⋂ index, {point : Ambient | 0 < basis.coord index point} := by ext point; simp
  rw [locus_eq]
  exact isOpen_iInter_of_finite fun index =>
    isOpen_lt continuous_const (basis.coord index).continuous_of_finiteDimensional

theorem mem_interior_basisCone_of_positive (basis : Basis Index ℝ Ambient)
    (point : Ambient) (positive : ∀ index, 0 < basis.repr point index) :
    point ∈ interior (PointedCone.hull ℝ (Set.range basis) : Set Ambient) := by
  have positive_interior :
      point ∈ interior {point : Ambient | ∀ index, 0 < basis.repr point index} := by
    rw [(isOpen_positive_basisCoordinates basis).interior_eq]
    exact positive
  exact interior_mono (fun vector member => (mem_basisCone_iff basis vector).mpr
    (fun index => (member index).le)) positive_interior

end BondalThomsen

namespace TauCeti.Toric.Fan

open Set Module Matrix

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem linearIndependent_real_of_integer (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (vectors : Fin dimension → Lattice) (independent : LinearIndependent ℤ vectors) :
    LinearIndependent ℝ (fun index => embedding (vectors index)) := by
  classical
  let matrix := basis.toMatrix vectors
  have integer_columns : LinearIndependent ℤ matrix.col := by
    have mapped := independent.map' basis.equivFun.toLinearMap
      (LinearMap.ker_eq_bot_of_injective basis.equivFun.injective)
    convert mapped using 1
    ext column row
    simp [matrix, Matrix.col_apply, Basis.toMatrix_apply, Basis.equivFun_apply]
  have determinant_nonzero : matrix.det ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp
      (Matrix.linearIndependent_col_iff.mp integer_columns)
  let real_basis := fan.lattice.isBaseChange.basis basis
  have coordinate_matrix : real_basis.toMatrix (fun index => embedding (vectors index)) =
      matrix.map (fun entry => (entry : ℝ)) := by
    ext row column
    change real_basis.repr (embedding.toIntLinearMap (vectors column)) row =
      (basis.repr (vectors column) row : ℝ)
    exact fan.lattice.isBaseChange.basis_repr_comp_apply basis (vectors column) row
  have real_determinant_nonzero :
      (real_basis.toMatrix (fun index => embedding (vectors index))).det ≠ 0 := by
    have cast_determinant : (matrix.det : ℝ) =
        (matrix.map (fun entry => (entry : ℝ))).det :=
      (Int.castRingHom ℝ).map_det matrix
    rw [coordinate_matrix, ← cast_determinant]
    exact_mod_cast determinant_nonzero
  apply LinearIndependent.of_comp real_basis.equivFun.toLinearMap
  have columns := Matrix.linearIndependent_cols_of_det_ne_zero real_determinant_nonzero
  convert columns using 1
  ext column row
  simp [Matrix.col_apply, Basis.toMatrix_apply, Basis.equivFun_apply]

end TauCeti.Toric.Fan
