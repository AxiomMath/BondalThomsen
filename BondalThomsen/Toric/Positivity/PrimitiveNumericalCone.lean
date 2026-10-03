module

public import BondalThomsen.Toric.Positivity.PrimitiveNumericalClass
public import BondalThomsen.Fan.PrimitiveRelationFiniteness
public import BondalThomsen.Fan.FiniteConeExtremalGenerators

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

noncomputable section

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable {𝕜} in
local instance primitiveConeBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

def primitiveNumericalGenerators (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    Set (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)) :=
  Set.range fun index : fan.PrimitiveRelationIndex =>
    index.2.2.numericalClass 𝕜 complete regular projective

theorem primitiveNumericalGenerators_finite
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    (fan.primitiveNumericalGenerators 𝕜 complete regular projective).Finite := by
  let := fan.primitiveRelationIndex_finite regular
  exact Set.finite_range _

def primitiveNumericalCone (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    PointedCone ℝ (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)) :=
  PointedCone.hull ℝ (fan.primitiveNumericalGenerators 𝕜 complete regular projective)

theorem PrimitiveLatticeRelation.numericalClass_mem_primitiveNumericalCone
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    relation.numericalClass 𝕜 complete regular projective ∈
      fan.primitiveNumericalCone 𝕜 complete regular projective :=
  PointedCone.subset_hull ⟨⟨left, right, relation⟩, rfl⟩

theorem primitiveNumericalCone_isClosed
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    IsClosed (fan.primitiveNumericalCone 𝕜 complete regular projective :
      Set (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular))) := by
  classical
  let : Fintype fan.Ray := Fintype.ofFinite fan.Ray
  let coordinates := fan.numericalRayCoordinates 𝕜 complete regular
  let generators := fan.primitiveNumericalGenerators 𝕜 complete regular projective
  have mappedHull : PointedCone.map coordinates (fan.primitiveNumericalCone 𝕜 complete regular projective) =
      PointedCone.hull ℝ (coordinates '' generators) := by
    simp only [primitiveNumericalCone, PointedCone.map, PointedCone.hull, Submodule.map_span]
    rfl
  have mappedClosed : IsClosed
      (PointedCone.map coordinates (fan.primitiveNumericalCone 𝕜 complete regular projective) :
        Set (fan.Ray → ℝ)) := by
    rw [mappedHull]
    exact BondalThomsen.FiniteConeExtremalGenerators.hull_isClosed_of_finite
      ((fan.primitiveNumericalGenerators_finite 𝕜 complete regular projective).image coordinates)
  have preimage : coordinates ⁻¹'
      (PointedCone.map coordinates (fan.primitiveNumericalCone 𝕜 complete regular projective) :
        Set (fan.Ray → ℝ)) =
      (fan.primitiveNumericalCone 𝕜 complete regular projective :
        Set (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular))) := by
    ext numericalClass
    change coordinates numericalClass ∈ PointedCone.map coordinates _ ↔ _
    rw [PointedCone.mem_map]
    constructor
    · rintro ⟨other, membership, equality⟩
      have same := fan.numericalRayCoordinates_injective 𝕜 complete regular equality
      exact same ▸ membership
    · intro membership
      exact ⟨numericalClass, membership, rfl⟩
  rw [← preimage]
  exact mappedClosed.preimage (fan.numericalRayCoordinates_continuous 𝕜 complete regular)

theorem primitiveNumericalCone_salient
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    (fan.primitiveNumericalCone 𝕜 complete regular projective : ConvexCone ℝ
      (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular))).Salient := by
  obtain ⟨divisor, strict⟩ := fan.exists_strictSupportDivisor_of_projective 𝕜 complete regular projective
  let evaluation := (LinearMap.proj
    (fan.invariantDivisorPicardRealization 𝕜 complete regular (fan.invariantRayDivisorClass divisor))).comp
      (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)).subtype
  apply BondalThomsen.FiniteConeExtremalGenerators.salient_of_positive_functional evaluation
  rintro numericalClass ⟨⟨left, right, relation⟩, rfl⟩ _nonzero
  change 0 < (relation.numericalClass 𝕜 complete regular projective).val
    (fan.invariantDivisorPicardRealization 𝕜 complete regular (fan.invariantRayDivisorClass divisor))
  rw [relation.numericalClass_realization 𝕜, relation.classPairing_mk]
  exact_mod_cast relation.primitiveSupportIntersection_positive_of_strictSupport
    complete regular divisor strict

def primitiveNumericalProperCone (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular) :
    ProperCone ℝ (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)) :=
  { fan.primitiveNumericalCone 𝕜 complete regular projective with
    isClosed' := fan.primitiveNumericalCone_isClosed 𝕜 complete regular projective }

theorem primitiveNumericalCone_bipolar
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (numericalClass : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular)) :
    numericalClass ∈ fan.primitiveNumericalCone 𝕜 complete regular projective ↔
      ∀ coefficients : fan.Ray → ℝ,
        (∀ primitiveClass ∈ fan.primitiveNumericalCone 𝕜 complete regular projective,
          0 ≤ fan.numericalRealPicardFunctional 𝕜 complete regular coefficients primitiveClass) →
        0 ≤ fan.numericalRealPicardFunctional 𝕜 complete regular coefficients numericalClass :=
  fan.numericalClosedCone_bipolar 𝕜 complete regular
    (fan.primitiveNumericalProperCone 𝕜 complete regular projective) numericalClass

end

end TauCeti.Toric.Fan
