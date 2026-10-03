module

public import BondalThomsen.Toric.Divisor.DivisorArithmetic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace BondalThomsen

open Finset

variable {Index Lattice Scalar : Type*} [Fintype Index] [AddCommGroup Lattice]
    [Field Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar] [FloorRing Scalar]

omit [Fintype Index] in

theorem exists_integral_translate_basis_Ico (basis : Module.Basis Index ℤ Lattice)
    (pairing : Lattice →+ Scalar) :
    ∃ character : Lattice →+ ℤ, ∀ index,
      (pairing + (Int.castAddHom Scalar).comp character) (basis index) ∈ Set.Ico 0 1 := by
  let character : Lattice →+ ℤ :=
    (basis.constr ℤ (fun index => -⌊pairing (basis index)⌋)).toAddMonoidHom
  refine ⟨character, ?_⟩
  intro index
  have translated :
      (pairing + (Int.castAddHom Scalar).comp character) (basis index) =
        Int.fract (pairing (basis index)) := by
    change pairing (basis index) +
      (((basis.constr ℤ (fun chosen => -⌊pairing (basis chosen)⌋)) (basis index) : ℤ) :
        Scalar) = Int.fract (pairing (basis index))
    rw [Module.Basis.constr_basis]
    simp only [Int.cast_neg, Int.fract, sub_eq_add_neg]
  rw [translated]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

omit [LinearOrder Scalar] [IsStrictOrderedRing Scalar] [FloorRing Scalar] in

theorem pairing_eq_sum_basis_coordinates (basis : Module.Basis Index ℤ Lattice)
    (pairing : Lattice →+ Scalar) (vector : Lattice) :
    pairing vector = ∑ index, (basis.repr vector index : Scalar) * pairing (basis index) := by
  have paired := congrArg pairing (basis.sum_repr vector)
  simpa only [map_sum, map_zsmul, zsmul_eq_mul] using paired.symm

omit [FloorRing Scalar] in

theorem abs_pairing_le_sum_abs_coordinates (basis : Module.Basis Index ℤ Lattice)
    (pairing : Lattice →+ Scalar)
    (normalized : ∀ index, pairing (basis index) ∈ Set.Ico 0 1) (vector : Lattice) :
    |pairing vector| ≤ ((∑ index, |basis.repr vector index| : ℤ) : Scalar) := by
  rw [pairing_eq_sum_basis_coordinates basis pairing vector]
  calc
    |∑ index, (basis.repr vector index : Scalar) * pairing (basis index)| ≤
        ∑ index, |(basis.repr vector index : Scalar) * pairing (basis index)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ index, |(basis.repr vector index : Scalar)| := by
      apply Finset.sum_le_sum
      intro index _
      rw [abs_mul, abs_of_nonneg (normalized index).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (normalized index).2.le
    _ = ((∑ index, |basis.repr vector index| : ℤ) : Scalar) := by
      push_cast
      rfl

theorem floor_pairing_mem_coordinate_interval (basis : Module.Basis Index ℤ Lattice)
    (pairing : Lattice →+ Scalar)
    (normalized : ∀ index, pairing (basis index) ∈ Set.Ico 0 1) (vector : Lattice) :
    ⌊pairing vector⌋ ∈ Set.Icc (-(∑ index, |basis.repr vector index|))
      (∑ index, |basis.repr vector index|) := by
  have bounded := abs_le.mp (abs_pairing_le_sum_abs_coordinates basis pairing normalized vector)
  constructor
  · have lower := Int.floor_mono bounded.1
    simpa only [← Int.cast_neg, Int.floor_intCast] using lower
  · have upper := Int.floor_mono bounded.2
    simpa only [Int.floor_intCast] using upper

theorem normalized_floor_coefficients_image_finite {Ray : Type*} [Finite Ray]
    (basis : Module.Basis Index ℤ Lattice) (vectors : Ray → Lattice) :
    ((fun pairing : Lattice →+ Scalar => fun ray => ⌊pairing (vectors ray)⌋) ''
      {pairing | ∀ index, pairing (basis index) ∈ Set.Ico 0 1}).Finite := by
  let intervals : Ray → Set ℤ := fun ray =>
    Set.Icc (-(∑ index, |basis.repr (vectors ray) index|))
      (∑ index, |basis.repr (vectors ray) index|)
  have finite_product : {coefficients : Ray → ℤ |
      ∀ ray, coefficients ray ∈ intervals ray}.Finite :=
    Set.Finite.pi' (fun ray => Set.finite_Icc _ _)
  apply finite_product.subset
  rintro coefficients ⟨pairing, normalized, rfl⟩ ray
  exact floor_pairing_mem_coordinate_interval basis pairing normalized (vectors ray)

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice Ambient Index : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient} [Fintype Index]

theorem normalized_floorRayDivisor_image_finite (fan : TauCeti.Toric.Fan embedding)
    (basis : Module.Basis Index ℤ Lattice) :
    (fan.floorRayDivisor ''
      {pairing | ∀ index, pairing (basis index) ∈ Set.Ico (0 : ℚ) 1}).Finite := by
  have coefficients := BondalThomsen.normalized_floor_coefficients_image_finite
    (Scalar := ℚ) basis (fun ray : fan.Ray => ray.val)
  have divisors := coefficients.image fan.invariantDivisorOfCoefficients
  apply divisors.subset
  rintro divisor ⟨pairing, normalized, rfl⟩
  exact ⟨fun ray : fan.Ray => ⌊pairing ray.val⌋, ⟨pairing, normalized, rfl⟩, rfl⟩

theorem floorRayDivisorClass_range_finite (fan : TauCeti.Toric.Fan embedding)
    (basis : Module.Basis Index ℤ Lattice) :
    (Set.range fan.floorRayDivisorClass).Finite := by
  have finite_classes := (fan.normalized_floorRayDivisor_image_finite basis).image
    fan.invariantRayDivisorClass
  apply finite_classes.subset
  rintro divisor_class ⟨pairing, rfl⟩
  obtain ⟨character, normalized⟩ :=
    BondalThomsen.exists_integral_translate_basis_Ico basis pairing
  refine ⟨fan.floorRayDivisor (pairing + (Int.castAddHom ℚ).comp character), ?_, ?_⟩
  · exact ⟨pairing + (Int.castAddHom ℚ).comp character, normalized, rfl⟩
  · exact fan.floorRayDivisorClass_add_integral pairing character

end TauCeti.Toric.Fan
