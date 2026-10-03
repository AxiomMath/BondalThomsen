module

public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryCechNonvanishing
public import BondalThomsen.Toric.Cohomology.PrimitivePairCohomology
public import BondalThomsen.Toric.Divisor.EffectiveSections
public import BondalThomsen.Cohomology.FiniteAffineCechAllDegreeComparison

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Preadditive
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.ToricPrimitiveWeightZeroComplex
open BondalThomsen.FiniteAffineCechAllDegreeComparison
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable section

theorem primitiveCechTupleAvailable_iff_of_same_nonnegative (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechTupleAvailable 𝕜 complete regular first degree tuple ↔
      fan.primitiveCechTupleAvailable 𝕜 complete regular second degree tuple := by
  constructor
  · intro available ray contains
    exact (same ray).mp (available ray contains)
  · intro available ray contains
    exact (same ray).mpr (available ray contains)

def primitiveCechScalarCoefficientEquiv_of_same_nonnegative (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechScalarCoefficient 𝕜 complete regular first degree tuple ≃+
      fan.primitiveCechScalarCoefficient 𝕜 complete regular second degree tuple where
  toFun scalar := ⟨scalar.val, fun unavailable => scalar.property
    (fun available => unavailable ((fan.primitiveCechTupleAvailable_iff_of_same_nonnegative 𝕜
      complete regular first second same degree tuple).mp available))⟩
  invFun scalar := ⟨scalar.val, fun unavailable => scalar.property
    (fun available => unavailable ((fan.primitiveCechTupleAvailable_iff_of_same_nonnegative 𝕜
      complete regular first second same degree tuple).mpr available))⟩
  left_inv _scalar := rfl
  right_inv _scalar := rfl
  map_add' _first _second := rfl

theorem primitiveCechScalarCoefficientEquiv_of_same_nonnegative_face (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray)
    (degree : ℕ) (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones))
    (deleted : Fin (degree + 2))
    (scalar : fan.primitiveCechScalarCoefficient 𝕜 complete regular first degree
      (tuple ∘ deleted.succAbove)) :
    fan.primitiveCechScalarFaceRestriction 𝕜 complete regular second degree tuple deleted
        (fan.primitiveCechScalarCoefficientEquiv_of_same_nonnegative 𝕜 complete regular first
          second same degree (tuple ∘ deleted.succAbove) scalar) =
      fan.primitiveCechScalarCoefficientEquiv_of_same_nonnegative 𝕜 complete regular first
        second same (degree + 1) tuple
          (fan.primitiveCechScalarFaceRestriction 𝕜 complete regular first degree tuple deleted scalar) := rfl

def primitiveComplementCoefficientIso_of_same_nonnegative (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveComplementCoefficient 𝕜 complete regular first degree tuple ≅
      fan.primitiveComplementCoefficient 𝕜 complete regular second degree tuple :=
  (fan.primitiveCechScalarCoefficientEquiv_of_same_nonnegative 𝕜
    complete regular first second same degree tuple).toAddCommGrpIso

def primitiveComplementDegreeMap_of_same_nonnegative (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray) (degree : ℕ) :
    fan.primitiveComplementDegree 𝕜 complete regular first degree ⟶
      fan.primitiveComplementDegree 𝕜 complete regular second degree :=
  Limits.Pi.map (fun tuple =>
    (fan.primitiveComplementCoefficientIso_of_same_nonnegative 𝕜
      complete regular first second same degree tuple).hom)

variable {𝕜} in
instance primitiveComplementDegreeMap_of_same_nonnegative_isIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray) (degree : ℕ) :
    IsIso (fan.primitiveComplementDegreeMap_of_same_nonnegative 𝕜
      complete regular first second same degree) := by
  unfold primitiveComplementDegreeMap_of_same_nonnegative
  infer_instance

theorem primitiveComplementDegreeMap_of_same_nonnegative_coface (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray)
    (degree : ℕ) (deleted : Fin (degree + 2)) :
    fan.primitiveComplementDegreeMap_of_same_nonnegative 𝕜 complete regular first second same degree ≫
        fan.primitiveComplementCoface 𝕜 complete regular second degree deleted =
      fan.primitiveComplementCoface 𝕜 complete regular first degree deleted ≫
        fan.primitiveComplementDegreeMap_of_same_nonnegative 𝕜
          complete regular first second same (degree + 1) := by
  exact productMaps_restriction
    (fan.primitiveComplementCoefficient 𝕜 complete regular first degree)
    (fan.primitiveComplementCoefficient 𝕜 complete regular second degree)
    (fan.primitiveComplementCoefficient 𝕜 complete regular first (degree + 1))
    (fan.primitiveComplementCoefficient 𝕜 complete regular second (degree + 1))
    (fun tuple => (fan.primitiveComplementCoefficientIso_of_same_nonnegative 𝕜
      complete regular first second same degree tuple).hom)
    (fun tuple => (fan.primitiveComplementCoefficientIso_of_same_nonnegative 𝕜
      complete regular first second same (degree + 1) tuple).hom)
    (fun tuple => tuple ∘ deleted.succAbove)
    (fun tuple => AddCommGrpCat.ofHom
      (fan.primitiveCechScalarFaceRestriction 𝕜 complete regular first degree tuple deleted))
    (fun tuple => AddCommGrpCat.ofHom
      (fan.primitiveCechScalarFaceRestriction 𝕜 complete regular second degree tuple deleted))
    (fun tuple => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact fan.primitiveCechScalarCoefficientEquiv_of_same_nonnegative_face 𝕜
        complete regular first second same degree tuple deleted)

theorem primitiveComplementDegreeMap_of_same_nonnegative_d (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray) (degree : ℕ) :
    fan.primitiveComplementDegreeMap_of_same_nonnegative 𝕜 complete regular first second same degree ≫
        fan.primitiveComplementDifferential 𝕜 complete regular second degree =
      fan.primitiveComplementDifferential 𝕜 complete regular first degree ≫
        fan.primitiveComplementDegreeMap_of_same_nonnegative 𝕜
          complete regular first second same (degree + 1) := by
  rw [primitiveComplementDifferential, primitiveComplementDifferential, comp_sum, sum_comp]
  apply Finset.sum_congr rfl
  intro deleted _member
  rw [comp_zsmul, zsmul_comp,
    fan.primitiveComplementDegreeMap_of_same_nonnegative_coface 𝕜]

def primitiveComplementMap_of_same_nonnegative (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray) :
    fan.primitiveComplementComplex 𝕜 complete regular first ⟶
      fan.primitiveComplementComplex 𝕜 complete regular second :=
  CochainComplex.ofHom
    (fan.primitiveComplementDegreeMap_of_same_nonnegative 𝕜 complete regular first second same)
    (fun degree => by
      simpa only [primitiveComplementComplex, CochainComplex.of_d] using
        fan.primitiveComplementDegreeMap_of_same_nonnegative_d 𝕜
          complete regular first second same degree)

variable {𝕜} in
instance primitiveComplementMap_of_same_nonnegative_isIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray) :
    IsIso (fan.primitiveComplementMap_of_same_nonnegative 𝕜 complete regular first second same) := by
  let : ∀ degree, IsIso
      ((fan.primitiveComplementMap_of_same_nonnegative 𝕜 complete regular first second same).f degree) :=
    fun degree => by
      change IsIso (fan.primitiveComplementDegreeMap_of_same_nonnegative 𝕜
        complete regular first second same degree)
      infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

def primitiveComplementIso_of_same_nonnegative (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (first second : fan.InvariantRayDivisor)
    (same : ∀ ray, 0 ≤ first ray ↔ 0 ≤ second ray) :
    fan.primitiveComplementComplex 𝕜 complete regular first ≅
      fan.primitiveComplementComplex 𝕜 complete regular second :=
  asIso (fan.primitiveComplementMap_of_same_nonnegative 𝕜 complete regular first second same)

def primitiveWeightZeroCechCohomologyIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (degree : ℕ) :
    AddCommGrpCat.of (Cohomology
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj degree) ≅
        (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).homology degree := by
  letI := fan.algebraicRealization_isNoetherian 𝕜 regular
  letI := fan.algebraicRealization_isSeparated 𝕜 regular
  exact cechSchemeCohomologyIso (fan.primitiveCechChartOpen 𝕜 complete regular)
    (fan.primitiveCechChartOpen_covers 𝕜 complete regular).iSup_eq_top
    (fun index => isAffineOpen_opensRange
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular index))) _ degree

def primitiveWeightZeroCechCohomologyEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (degree : ℕ) :
    Cohomology (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj degree ≃+
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).homology degree :=
  (fan.primitiveWeightZeroCechCohomologyIso 𝕜 complete regular divisor degree).addCommGroupIsoToAddEquiv

theorem primitiveBoundary_actualCohomology_nontrivial (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (rays : Finset fan.Ray)
    (primitive : fan.IsPrimitiveCollection rays) :
    Nontrivial (Cohomology (fan.invariantDivisorLineBundle 𝕜 complete regular
      (fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ rays then -1 else 0))).obj
        (rays.card - 1)) :=
  (fan.primitiveWeightZeroCechCohomologyEquiv 𝕜 complete regular _
    (rays.card - 1)).toEquiv.nontrivial_congr.mpr
      (fan.primitiveBoundaryActualCechHomology_nontrivial 𝕜 complete regular rays primitive)

theorem primitiveBoundaryCohomologyNonvanishing_proved (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    fan.PrimitiveBoundaryCohomologyNonvanishing 𝕜 complete regular :=
  fun rays primitive => fan.primitiveBoundary_actualCohomology_nontrivial 𝕜
    complete regular rays primitive

theorem primitiveFloorPairSheafComparison_proved (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    BondalThomsen.PrimitiveFloorPairSheafComparison fan (fan.algebraicRealization 𝕜 regular)
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular) :=
  fan.primitiveFloorPairSheafComparison_of_boundaryCohomology 𝕜 complete regular
    (fan.primitiveBoundaryCohomologyNonvanishing_proved 𝕜 complete regular)

end

end TauCeti.Toric.Fan
