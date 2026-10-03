module

public import BondalThomsen.Toric.Cohomology.PrimitiveWeightZeroComplex

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Preadditive Multiplicative
open BondalThomsen.ToricPrimitiveWeightZeroComplex
open BondalThomsen.FiniteAffineCechHigherComparison
open scoped Classical

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable section

omit [FiniteDimensional ℝ Ambient] in
theorem divisorLaurentMonomial_mem_iff (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (scalar : 𝕜) :
    MonoidAlgebra.single (ofAdd character) scalar ∈ fan.divisorLaurentSectionSpace 𝕜 cone divisor ↔
      (¬(∀ ray : fan.Ray, embedding ray.val ∈ cone →
        0 ≤ (divisor + fan.principalRayDivisor character) ray) → scalar = 0) := by
  by_cases scalar_zero : scalar = 0
  · subst scalar
    simp [MonoidAlgebra.single_zero]
  · rw [fan.mem_divisorLaurentSectionSpace_iff 𝕜]
    simp only [MonoidAlgebra.coeff_single, Finsupp.support_single _ scalar_zero,
      Finset.mem_singleton, forall_eq, toAdd_ofAdd, Finsupp.add_apply,
      principalRayDivisor_apply, neg_le_iff_add_nonneg, add_comm]
    tauto

def cechCharacterTupleAvailable (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) : Prop :=
  fan.primitiveCechTupleAvailable 𝕜 complete regular
    (divisor + fan.principalRayDivisor character) degree tuple

theorem cechCharacterTupleAvailable_iff_avoids_negative (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.cechCharacterTupleAvailable 𝕜 complete regular divisor character degree tuple ↔
      ∀ ray : fan.Ray, divisor ray + character ray.val < 0 →
        embedding ray.val ∉ (fan.primitiveCechCone 𝕜 complete regular degree tuple).val := by
  constructor
  · intro available ray negative contains
    have nonnegative := available ray contains
    simp only [Finsupp.add_apply, principalRayDivisor_apply] at nonnegative
    exact (not_lt.mpr nonnegative) negative
  · intro avoids ray contains
    simp only [Finsupp.add_apply, principalRayDivisor_apply]
    exact le_of_not_gt (fun negative => avoids ray negative contains)

def divisorLaurentCharacterProjection (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) :
    fan.divisorLaurentSectionSpace 𝕜 cone divisor →ₗ[𝕜]
      (fan.divisorLaurentSectionSpace 𝕜) cone divisor := by
  refine {
    toFun := fun polynomial => ⟨MonoidAlgebra.single (ofAdd character)
      (polynomial.val.coeff (ofAdd character)), ?_⟩
    map_add' := fun first second => ?_
    map_smul' := fun scalar polynomial => ?_ }
  · rw [fan.mem_divisorLaurentSectionSpace_iff 𝕜]
    intro exponent supported ray contains
    have exponent_eq : exponent = ofAdd character := Finset.mem_singleton.mp
      (Finsupp.support_single_subset supported)
    have nonzero : polynomial.val.coeff (ofAdd character) ≠ 0 := by
      intro coefficient_zero
      change exponent ∈ (Finsupp.single (ofAdd character)
        (polynomial.val.coeff (ofAdd character))).support at supported
      rw [coefficient_zero] at supported
      simp at supported
    subst exponent
    exact (fan.mem_divisorLaurentSectionSpace_iff 𝕜 cone divisor polynomial.val).mp polynomial.property
      (ofAdd character) (Finsupp.mem_support_iff.mpr nonzero) ray contains
  · apply Subtype.ext
    simp only [Submodule.coe_add, MonoidAlgebra.coeff_add, Finsupp.add_apply,
      MonoidAlgebra.single_add]
  · apply Subtype.ext
    simp only [Submodule.coe_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      MonoidAlgebra.smul_single, RingHom.id_apply]

def cechCharacterScalarToLaurent (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechScalarCoefficient 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) degree tuple →+
      fan.divisorLaurentSectionSpace 𝕜 (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor where
  toFun scalar := ⟨MonoidAlgebra.single (ofAdd character) scalar.val,
    (fan.divisorLaurentMonomial_mem_iff 𝕜 _ divisor character scalar.val).mpr scalar.property⟩
  map_zero' := by apply Subtype.ext; exact MonoidAlgebra.single_zero _
  map_add' first second := by apply Subtype.ext; exact MonoidAlgebra.single_add _ _ _

def cechCharacterScalarToCoefficient (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechScalarCoefficient 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) degree tuple →+
      fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple :=
  (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple).symm.toAddMonoidHom.comp
    (fan.cechCharacterScalarToLaurent 𝕜 complete regular divisor character degree tuple)

def cechCharacterCoefficientToScalar (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple →+
      fan.primitiveCechScalarCoefficient 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) degree tuple := by
  refine {
    toFun := fun element => ⟨
      (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple element).val.coeff
        (ofAdd character), ?_⟩
    map_zero' := ?_
    map_add' := fun first second => ?_ }
  · apply (fan.divisorLaurentMonomial_mem_iff 𝕜 _ divisor character _).mp
    exact (fan.divisorLaurentCharacterProjection 𝕜
      (fan.primitiveCechCone 𝕜 complete regular degree tuple).val divisor character
      (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple element)).property
  · apply Subtype.ext
    simp only [map_zero, Submodule.coe_zero, MonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      AddSubgroup.coe_zero]
  · apply Subtype.ext
    simp only [map_add, Submodule.coe_add, MonoidAlgebra.coeff_add, Finsupp.add_apply,
      AddSubgroup.coe_add]

theorem cechCharacterCoefficientToScalar_toCoefficient (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (scalar : fan.primitiveCechScalarCoefficient 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree tuple) :
    fan.cechCharacterCoefficientToScalar 𝕜 complete regular divisor character degree tuple
      (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor character degree tuple scalar) = scalar := by
  apply Subtype.ext
  change (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple
    ((fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple).symm
      (fan.cechCharacterScalarToLaurent 𝕜 complete regular divisor character degree tuple scalar))).val.coeff
        (ofAdd character) = _
  rw [AddEquiv.apply_symm_apply]
  simp [cechCharacterScalarToLaurent, MonoidAlgebra.coeff_single]

theorem cechCharacterScalarToCoefficient_laurent (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (scalar : fan.primitiveCechScalarCoefficient 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree tuple) :
    (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple
      (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor character degree tuple scalar)).val =
        MonoidAlgebra.single (ofAdd character) scalar.val := by
  exact congrArg Subtype.val
    ((fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple).apply_symm_apply _)

theorem cechCharacterScalarToCoefficient_face (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones)) (deleted : Fin (degree + 2))
    (scalar : fan.primitiveCechScalarCoefficient 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree (tuple ∘ deleted.succAbove)) :
    fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted
      (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor character degree
        (tuple ∘ deleted.succAbove) scalar) =
      fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor character (degree + 1) tuple
        (fan.primitiveCechScalarFaceRestriction 𝕜 complete regular
          (divisor + fan.principalRayDivisor character) degree tuple deleted scalar) := by
  apply (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor (degree + 1) tuple).injective
  apply Subtype.ext
  rw [fan.primitiveCechCoefficientLaurentEquiv_face 𝕜,
    fan.cechCharacterScalarToCoefficient_laurent 𝕜, fan.cechCharacterScalarToCoefficient_laurent 𝕜]
  rfl

theorem cechCharacterCoefficientToScalar_face (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 2) → Fin (Nat.card fan.cones)) (deleted : Fin (degree + 2))
    (element : fan.primitiveCechCoefficient 𝕜 complete regular divisor degree (tuple ∘ deleted.succAbove)) :
    fan.primitiveCechScalarFaceRestriction 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree tuple deleted
        (fan.cechCharacterCoefficientToScalar 𝕜 complete regular divisor character degree
          (tuple ∘ deleted.succAbove) element) =
      fan.cechCharacterCoefficientToScalar 𝕜 complete regular divisor character (degree + 1) tuple
        (fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted element) := by
  apply Subtype.ext
  change _ = (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor (degree + 1) tuple
    (fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted element)).val.coeff
      (ofAdd character)
  rw [fan.primitiveCechCoefficientLaurentEquiv_face 𝕜]
  rfl

def cechCharacterDegreeInclusion (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) :
    fan.primitiveComplementDegree 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) degree ⟶
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree :=
  Limits.Pi.map (fun tuple => AddCommGrpCat.ofHom
    (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor character degree tuple))

def cechCharacterDegreeRetraction (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) :
    (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree ⟶
      fan.primitiveComplementDegree 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) degree :=
  Limits.Pi.map (fun tuple => AddCommGrpCat.ofHom
    (fan.cechCharacterCoefficientToScalar 𝕜 complete regular divisor character degree tuple))

theorem cechCharacterDegree_split (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) :
    fan.cechCharacterDegreeInclusion 𝕜 complete regular divisor character degree ≫
      fan.cechCharacterDegreeRetraction 𝕜 complete regular divisor character degree =
        𝟙 (fan.primitiveComplementDegree 𝕜 complete regular
          (divisor + fan.principalRayDivisor character) degree) := by
  change Limits.Pi.map _ ≫ Limits.Pi.map _ = _
  rw [Limits.Pi.map_comp_map]
  apply Limits.Pi.hom_ext
  intro tuple
  simp only [Limits.Pi.map_π]
  have composite : AddCommGrpCat.ofHom
        (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor character degree tuple) ≫
      AddCommGrpCat.ofHom
        (fan.cechCharacterCoefficientToScalar 𝕜 complete regular divisor character degree tuple) =
      𝟙 (fan.primitiveComplementCoefficient 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) degree tuple) := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact fan.cechCharacterCoefficientToScalar_toCoefficient 𝕜 complete regular divisor character degree tuple
  rw [composite]
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp only [Category.comp_id, Category.id_comp]

theorem cechCharacterDegreeInclusion_coface (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) (deleted : Fin (degree + 2)) :
    fan.cechCharacterDegreeInclusion 𝕜 complete regular divisor character degree ≫
        fan.primitiveCechCoface 𝕜 complete regular divisor degree deleted =
      fan.primitiveComplementCoface 𝕜 complete regular
          (divisor + fan.principalRayDivisor character) degree deleted ≫
        fan.cechCharacterDegreeInclusion 𝕜 complete regular divisor character (degree + 1) := by
  exact productMaps_restriction
    (fan.primitiveComplementCoefficient 𝕜 complete regular (divisor + fan.principalRayDivisor character) degree)
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree)
    (fan.primitiveComplementCoefficient 𝕜 complete regular (divisor + fan.principalRayDivisor character) (degree + 1))
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor (degree + 1))
    (fun tuple => AddCommGrpCat.ofHom
      (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor character degree tuple))
    (fun tuple => AddCommGrpCat.ofHom
      (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor character (degree + 1) tuple))
    (fun tuple => tuple ∘ deleted.succAbove)
    (fun tuple => AddCommGrpCat.ofHom (fan.primitiveCechScalarFaceRestriction 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree tuple deleted))
    (fun tuple => fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted)
    (fun tuple => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact fan.cechCharacterScalarToCoefficient_face 𝕜 complete regular divisor character degree tuple deleted)

theorem cechCharacterDegreeRetraction_coface (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) (deleted : Fin (degree + 2)) :
    fan.cechCharacterDegreeRetraction 𝕜 complete regular divisor character degree ≫
        fan.primitiveComplementCoface 𝕜 complete regular
          (divisor + fan.principalRayDivisor character) degree deleted =
      fan.primitiveCechCoface 𝕜 complete regular divisor degree deleted ≫
        fan.cechCharacterDegreeRetraction 𝕜 complete regular divisor character (degree + 1) := by
  exact productMaps_restriction
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree)
    (fan.primitiveComplementCoefficient 𝕜 complete regular (divisor + fan.principalRayDivisor character) degree)
    (fan.primitiveCechCoefficient 𝕜 complete regular divisor (degree + 1))
    (fan.primitiveComplementCoefficient 𝕜 complete regular (divisor + fan.principalRayDivisor character) (degree + 1))
    (fun tuple => AddCommGrpCat.ofHom
      (fan.cechCharacterCoefficientToScalar 𝕜 complete regular divisor character degree tuple))
    (fun tuple => AddCommGrpCat.ofHom
      (fan.cechCharacterCoefficientToScalar 𝕜 complete regular divisor character (degree + 1) tuple))
    (fun tuple => tuple ∘ deleted.succAbove)
    (fun tuple => fan.primitiveCechFaceRestriction 𝕜 complete regular divisor degree tuple deleted)
    (fun tuple => AddCommGrpCat.ofHom (fan.primitiveCechScalarFaceRestriction 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree tuple deleted))
    (fun tuple => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact fan.cechCharacterCoefficientToScalar_face 𝕜 complete regular divisor character degree tuple deleted)

theorem cechCharacterDegreeInclusion_d (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) :
    fan.cechCharacterDegreeInclusion 𝕜 complete regular divisor character degree ≫
        (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).d degree (degree + 1) =
      fan.primitiveComplementDifferential 𝕜 complete regular
          (divisor + fan.principalRayDivisor character) degree ≫
        fan.cechCharacterDegreeInclusion 𝕜 complete regular divisor character (degree + 1) := by
  rw [fan.primitiveWeightZeroCechComplex_d 𝕜, primitiveComplementDifferential, comp_sum, sum_comp]
  apply Finset.sum_congr rfl
  intro deleted _member
  rw [comp_zsmul, zsmul_comp, fan.cechCharacterDegreeInclusion_coface 𝕜]

theorem cechCharacterDegreeRetraction_d (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) :
    fan.cechCharacterDegreeRetraction 𝕜 complete regular divisor character degree ≫
        fan.primitiveComplementDifferential 𝕜 complete regular
          (divisor + fan.principalRayDivisor character) degree =
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).d degree (degree + 1) ≫
        fan.cechCharacterDegreeRetraction 𝕜 complete regular divisor character (degree + 1) := by
  rw [fan.primitiveWeightZeroCechComplex_d 𝕜, primitiveComplementDifferential, comp_sum, sum_comp]
  apply Finset.sum_congr rfl
  intro deleted _member
  rw [comp_zsmul, zsmul_comp, fan.cechCharacterDegreeRetraction_coface 𝕜]

def cechCharacterInclusion (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) :
    fan.primitiveComplementComplex 𝕜 complete regular (divisor + fan.principalRayDivisor character) ⟶
      fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor :=
  CochainComplex.ofHom (fan.cechCharacterDegreeInclusion 𝕜 complete regular divisor character)
    (fun degree => by
      simpa only [primitiveComplementComplex, CochainComplex.of_d] using
        fan.cechCharacterDegreeInclusion_d 𝕜 complete regular divisor character degree)

def cechCharacterRetraction (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) :
    fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor ⟶
      fan.primitiveComplementComplex 𝕜 complete regular (divisor + fan.principalRayDivisor character) :=
  CochainComplex.ofHom (fan.cechCharacterDegreeRetraction 𝕜 complete regular divisor character)
    (fun degree => by
      simpa only [primitiveComplementComplex, CochainComplex.of_d] using
        fan.cechCharacterDegreeRetraction_d 𝕜 complete regular divisor character degree)

def cechCharacterChainProjector (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) :
    fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor ⟶
      fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor :=
  fan.cechCharacterRetraction 𝕜 complete regular divisor character ≫
    fan.cechCharacterInclusion 𝕜 complete regular divisor character

def cechCharacterCoefficientProjector (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple ⟶
      fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple :=
  AddCommGrpCat.ofHom (fan.cechCharacterCoefficientToScalar 𝕜 complete regular divisor character degree tuple) ≫
    AddCommGrpCat.ofHom (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor character degree tuple)

theorem cechCharacterCoefficientProjector_laurent (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (element : fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple) :
    (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple
      (fan.cechCharacterCoefficientProjector 𝕜 complete regular divisor character degree tuple element)).val =
        MonoidAlgebra.single (ofAdd character)
          ((fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple element).val.coeff
            (ofAdd character)) :=
  fan.cechCharacterScalarToCoefficient_laurent 𝕜 complete regular divisor character degree tuple _

theorem cechCharacterChainProjector_f (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) :
    (fan.cechCharacterChainProjector 𝕜 complete regular divisor character).f degree =
      Limits.Pi.map (fan.cechCharacterCoefficientProjector 𝕜 complete regular divisor character degree) := by
  unfold cechCharacterChainProjector cechCharacterInclusion cechCharacterRetraction
    cechCharacterDegreeInclusion cechCharacterDegreeRetraction
  dsimp only [HomologicalComplex.comp_f, CochainComplex.ofHom]
  rw [Limits.Pi.map_comp_map]
  rfl

def cechCoefficientCharacterSupport (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (element : fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple) :
    Finset (Lattice →+ ℤ) :=
  (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple element).val.coeff.support.image
    toAdd

theorem cechCharacterCoefficientProjector_eq_zero_of_not_mem_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (element : fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple)
    (absent : character ∉ fan.cechCoefficientCharacterSupport 𝕜 complete regular divisor degree tuple element) :
    fan.cechCharacterCoefficientProjector 𝕜 complete regular divisor character degree tuple element = 0 := by
  have coefficient_zero :
      (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple element).val.coeff
        (ofAdd character) = 0 := by
    by_contra nonzero
    apply absent
    have supported := Finsupp.mem_support_iff.mpr nonzero
    exact Finset.mem_image.mpr ⟨ofAdd character, supported, rfl⟩
  apply (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple).injective
  apply Subtype.ext
  rw [fan.cechCharacterCoefficientProjector_laurent 𝕜, coefficient_zero]
  simp only [map_zero, Submodule.coe_zero, MonoidAlgebra.single_zero]

theorem cechCharacterCoefficientProjector_sum_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (element : fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple) :
    ∑ character ∈ fan.cechCoefficientCharacterSupport 𝕜 complete regular divisor degree tuple element,
      fan.cechCharacterCoefficientProjector 𝕜 complete regular divisor character degree tuple element = element := by
  apply (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple).injective
  apply Subtype.ext
  rw [map_sum, Submodule.coe_sum]
  simp_rw [fan.cechCharacterCoefficientProjector_laurent 𝕜]
  unfold cechCoefficientCharacterSupport
  rw [Finset.sum_image]
  · simp only [ofAdd_toAdd]
    exact MonoidAlgebra.sum_coeff_single _
  · intro first _first_member second _second_member same
    exact congrArg ofAdd same

theorem cechCharacterCoefficientProjector_sum_of_support_subset (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (element : fan.primitiveCechCoefficient 𝕜 complete regular divisor degree tuple)
    (weights : Finset (Lattice →+ ℤ))
    (supported : fan.cechCoefficientCharacterSupport 𝕜 complete regular divisor degree tuple element ⊆ weights) :
    ∑ character ∈ weights,
      fan.cechCharacterCoefficientProjector 𝕜 complete regular divisor character degree tuple element = element := by
  calc
    _ = ∑ character ∈ fan.cechCoefficientCharacterSupport 𝕜 complete regular divisor degree tuple element,
        fan.cechCharacterCoefficientProjector 𝕜 complete regular divisor character degree tuple element :=
      (Finset.sum_subset supported (fun character _member absent =>
        fan.cechCharacterCoefficientProjector_eq_zero_of_not_mem_support 𝕜
          complete regular divisor character degree tuple element absent)).symm
    _ = element := fan.cechCharacterCoefficientProjector_sum_support 𝕜
      complete regular divisor degree tuple element

def cechDegreeCharacterSupport (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (element : (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree) :
    Finset (Lattice →+ ℤ) :=
  Finset.univ.biUnion (fun tuple =>
    fan.cechCoefficientCharacterSupport 𝕜 complete regular divisor degree tuple
      (Limits.Pi.π (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree) tuple element))

theorem cechCharacterChainProjector_coordinate (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (element : (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    Limits.Pi.π (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree) tuple
      ((fan.cechCharacterChainProjector 𝕜 complete regular divisor character).f degree element) =
      fan.cechCharacterCoefficientProjector 𝕜 complete regular divisor character degree tuple
        (Limits.Pi.π (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree) tuple element) := by
  rw [fan.cechCharacterChainProjector_f 𝕜]
  exact ConcreteCategory.congr_hom (Limits.Pi.map_π _ tuple) element

theorem cechCharacterChainProjector_sum_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (element : (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree) :
    ∑ character ∈ fan.cechDegreeCharacterSupport 𝕜 complete regular divisor degree element,
      (fan.cechCharacterChainProjector 𝕜 complete regular divisor character).f degree element = element := by
  apply (Concrete.productEquiv (fan.primitiveCechCoefficient 𝕜 complete regular divisor degree)).injective
  funext tuple
  simp only [Concrete.productEquiv_apply_apply]
  rw [map_sum]
  simp_rw [fan.cechCharacterChainProjector_coordinate 𝕜]
  apply fan.cechCharacterCoefficientProjector_sum_of_support_subset 𝕜
  intro character supported
  exact Finset.mem_biUnion.mpr ⟨tuple, Finset.mem_univ _, supported⟩

theorem cechCharacterCoefficientToScalar_other (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (first second : Lattice →+ ℤ) (different : first ≠ second) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones))
    (scalar : fan.primitiveCechScalarCoefficient 𝕜 complete regular
      (divisor + fan.principalRayDivisor first) degree tuple) :
    fan.cechCharacterCoefficientToScalar 𝕜 complete regular divisor second degree tuple
      (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor first degree tuple scalar) = 0 := by
  apply Subtype.ext
  change (fan.primitiveCechCoefficientLaurentEquiv 𝕜 complete regular divisor degree tuple
    (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor first degree tuple scalar)).val.coeff
      (ofAdd second) = 0
  rw [fan.cechCharacterScalarToCoefficient_laurent 𝕜]
  simp [MonoidAlgebra.coeff_single, different]

theorem cechCharacterDegree_other (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (first second : Lattice →+ ℤ) (different : first ≠ second) (degree : ℕ) :
    fan.cechCharacterDegreeInclusion 𝕜 complete regular divisor first degree ≫
      fan.cechCharacterDegreeRetraction 𝕜 complete regular divisor second degree = 0 := by
  change Limits.Pi.map _ ≫ Limits.Pi.map _ = _
  rw [Limits.Pi.map_comp_map]
  apply Limits.Pi.hom_ext
  intro tuple
  rw [Limits.Pi.map_π]
  have composite : AddCommGrpCat.ofHom
        (fan.cechCharacterScalarToCoefficient 𝕜 complete regular divisor first degree tuple) ≫
      AddCommGrpCat.ofHom
        (fan.cechCharacterCoefficientToScalar 𝕜 complete regular divisor second degree tuple) =
      (0 : fan.primitiveComplementCoefficient 𝕜 complete regular
        (divisor + fan.principalRayDivisor first) degree tuple ⟶
          fan.primitiveComplementCoefficient 𝕜 complete regular
            (divisor + fan.principalRayDivisor second) degree tuple) := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact fan.cechCharacterCoefficientToScalar_other 𝕜 complete regular divisor first second different degree tuple
  rw [composite]
  simp only [comp_zero, zero_comp]

end

end TauCeti.Toric.Fan
