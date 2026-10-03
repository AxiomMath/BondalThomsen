module

public import BondalThomsen.Toric.Positivity.PrimitiveZeroSupport
public import BondalThomsen.Toric.Positivity.PrimitiveRayObstruction
public import BondalThomsen.Fan.PrimitiveNonfaces
public import BondalThomsen.Fan.FiniteConeExposedFaces
public import BondalThomsen.Toric.Positivity.NefMoriProof

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

noncomputable section

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance reidRayDecidableEq (fan : Fan embedding) : DecidableEq fan.Ray :=
  Classical.decEq _

variable {𝕜} in
local instance reidBaseOver (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨fan.structureMap 𝕜 regular⟩

theorem PrimitiveLatticeRelation.exists_primitiveRelation_omitting_leftRay_of_noncone
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (extra : Finset fan.Ray) (disjoint : Disjoint extra left) (distinguished : left)
    (noncone : fan.finiteRayHull (left.erase distinguished.val ∪ right ∪ extra) ∉ fan.cones) :
    ∃ other_left other_right : Finset fan.Ray,
      ∃ _other : fan.PrimitiveLatticeRelation other_left other_right,
        other_left ⊆ left.erase distinguished.val ∪ right ∪ extra ∧
          distinguished.val ∉ other_left := by
  classical
  have nonempty : (left.erase distinguished.val ∪ right ∪ extra).Nonempty := by
    by_contra empty
    have rays_empty := Finset.not_nonempty_iff_eq_empty.mp empty
    apply noncone
    rw [rays_empty, fan.finiteRayHull_empty]
    exact fan.bot_mem distinguished.val.property.2
  obtain ⟨other_left, subset, primitive⟩ := fan.exists_primitiveCollection_subset_of_noncone
    regular (left.erase distinguished.val ∪ right ∪ extra) nonempty noncone
  obtain ⟨other_right, ⟨other⟩⟩ := primitive.exists_primitiveLatticeRelation complete regular
  refine ⟨other_left, other_right, other, subset, ?_⟩
  intro member
  rcases Finset.mem_union.mp (subset member) with relation_member | extra_member
  · rcases Finset.mem_union.mp relation_member with left_member | right_member
    · exact (Finset.mem_erase.mp left_member).1 rfl
    · exact Finset.disjoint_left.mp relation.disjoint distinguished.property right_member
  · exact Finset.disjoint_left.mp disjoint extra_member distinguished.property

theorem PrimitiveLatticeRelation.coneExtension_of_exposing_functional
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (functional : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular) →ₗ[ℝ] ℝ)
    (nonnegative : ∀ numericalClass ∈ fan.primitiveNumericalCone 𝕜 complete regular projective,
      0 ≤ functional numericalClass)
    (zero : functional (relation.numericalClass 𝕜 complete regular projective) = 0)
    (zero_locus : {numericalClass |
      numericalClass ∈ fan.primitiveNumericalCone 𝕜 complete regular projective ∧
        functional numericalClass = 0} =
      (PointedCone.hull ℝ {relation.numericalClass 𝕜 complete regular projective} :
        Set (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular))))
    (extra : Finset fan.Ray) (disjoint : Disjoint extra left)
    (cone : fan.finiteRayHull (right ∪ extra) ∈ fan.cones) (distinguished : left) :
    fan.finiteRayHull (left.erase distinguished.val ∪ right ∪ extra) ∈ fan.cones := by
  classical
  obtain ⟨values, functional_eq⟩ :=
    fan.numericalLinearFunctional_eq_realPicard 𝕜 complete regular functional
  have evaluation : ∀ other_left other_right
      (other : fan.PrimitiveLatticeRelation other_left other_right),
      functional (other.numericalClass 𝕜 complete regular projective) = other.realRayPairing values := by
    intro other_left other_right other
    rw [functional_eq]
    change fan.realRayNumericalEvaluation 𝕜 complete regular
      (other.numericalClass 𝕜 complete regular projective) values = _
    rw [other.realRayNumericalEvaluation_eq 𝕜 complete regular projective]
  have pairings : fan.HasNonnegativeRealPrimitivePairings values := by
    intro other_left other_right other
    rw [← evaluation other_left other_right other]
    exact nonnegative _ (other.numericalClass_mem_primitiveNumericalCone 𝕜 complete regular projective)
  have support := fan.hasRealRaySupportInequalities_of_nonnegativePrimitivePairings 𝕜
    complete regular projective values pairings
  have zero_pairing : relation.realRayPairing values = 0 :=
    (evaluation left right relation).symm.trans zero
  obtain ⟨dimension, basis, cone_basis, above, zero_gaps, zero_pairings⟩ :=
    relation.exists_coneBasis_zeroSupport_and_pairings_of_right_union_cone
      complete regular values support zero_pairing extra cone
  by_contra noncone
  obtain ⟨other_left, other_right, other, subset, omitted⟩ :=
    relation.exists_primitiveRelation_omitting_leftRay_of_noncone
      complete regular extra disjoint distinguished noncone
  have full_subset : other_left ⊆ left ∪ right ∪ extra := by
    intro ray member
    rcases Finset.mem_union.mp (subset member) with relation_member | extra_member
    · rcases Finset.mem_union.mp relation_member with left_member | right_member
      · exact Finset.mem_union_left extra (Finset.mem_union_left right
          (Finset.mem_of_mem_erase left_member))
      · exact Finset.mem_union_left extra (Finset.mem_union_right left right_member)
    · exact Finset.mem_union_right (left ∪ right) extra_member
  have other_zero : functional (other.numericalClass 𝕜 complete regular projective) = 0 :=
    (evaluation other_left other_right other).trans
      (zero_pairings other_left other_right other full_subset)
  have zero_membership : other.numericalClass 𝕜 complete regular projective ∈
      {numericalClass |
        numericalClass ∈ fan.primitiveNumericalCone 𝕜 complete regular projective ∧
          functional numericalClass = 0} :=
    ⟨other.numericalClass_mem_primitiveNumericalCone 𝕜 complete regular projective, other_zero⟩
  rw [zero_locus] at zero_membership
  exact relation.numericalClass_not_mem_ray_of_omitted_leftRay 𝕜 other complete regular projective
    distinguished omitted zero_membership

theorem PrimitiveLatticeRelation.exists_exposing_functional_of_primitiveNumericalFace
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (is_face : (PointedCone.hull ℝ {relation.numericalClass 𝕜 complete regular projective}).IsFaceOf
      (fan.primitiveNumericalCone 𝕜 complete regular projective)) :
    ∃ functional : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular) →ₗ[ℝ] ℝ,
      (∀ numericalClass ∈ fan.primitiveNumericalCone 𝕜 complete regular projective,
        0 ≤ functional numericalClass) ∧
      functional (relation.numericalClass 𝕜 complete regular projective) = 0 ∧
      {numericalClass |
        numericalClass ∈ fan.primitiveNumericalCone 𝕜 complete regular projective ∧
          functional numericalClass = 0} =
        (PointedCone.hull ℝ {relation.numericalClass 𝕜 complete regular projective} :
          Set (BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular))) := by
  classical
  let := Fintype.ofFinite fan.Ray
  let coordinates := LinearEquiv.ofInjective (fan.numericalRayCoordinates 𝕜 complete regular)
    (fan.numericalRayCoordinates_injective 𝕜 complete regular)
  exact BondalThomsen.FiniteConeExposedFaces.exists_nonnegative_linear_functional_exposing_ray_of_linearEquiv
    coordinates (fan.primitiveNumericalGenerators_finite 𝕜 complete regular projective) is_face

theorem PrimitiveLatticeRelation.coneExtension_of_primitiveNumericalFace
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (is_face : (PointedCone.hull ℝ {relation.numericalClass 𝕜 complete regular projective}).IsFaceOf
      (fan.primitiveNumericalCone 𝕜 complete regular projective))
    (extra : Finset fan.Ray) (disjoint : Disjoint extra left)
    (cone : fan.finiteRayHull (right ∪ extra) ∈ fan.cones) (distinguished : left) :
    fan.finiteRayHull (left.erase distinguished.val ∪ right ∪ extra) ∈ fan.cones := by
  obtain ⟨functional, nonnegative, zero, zero_locus⟩ :=
    relation.exists_exposing_functional_of_primitiveNumericalFace 𝕜 complete regular projective is_face
  exact relation.coneExtension_of_exposing_functional 𝕜 complete regular projective
    functional nonnegative zero zero_locus extra disjoint cone distinguished

theorem PrimitiveLatticeRelation.coneExtension_of_moriCone_eq
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (cone_eq : BondalThomsen.moriCone 𝕜 (fan.algebraicRealization 𝕜 regular) =
      fan.primitiveNumericalCone 𝕜 complete regular projective)
    (extremal : relation.IsMoriExtremal 𝕜 complete regular)
    (extra : Finset fan.Ray) (disjoint : Disjoint extra left)
    (cone : fan.finiteRayHull (right ∪ extra) ∈ fan.cones) (distinguished : left) :
    fan.finiteRayHull (left.erase distinguished.val ∪ right ∪ extra) ∈ fan.cones := by
  have numerical_extremal :=
    (relation.isMoriExtremal_iff_numericalClass 𝕜 complete regular projective).mp extremal
  have is_face := numerical_extremal.2
  rw [cone_eq] at is_face
  exact relation.coneExtension_of_primitiveNumericalFace 𝕜 complete regular projective
    is_face extra disjoint cone distinguished

theorem PrimitiveLatticeRelation.coneExtension_of_isMoriExtremal
    {fan : Fan embedding} {left right : Finset fan.Ray}
    (relation : fan.PrimitiveLatticeRelation left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (projective : BondalThomsen.ToricSchemeIsProjective 𝕜 fan regular)
    (extremal : relation.IsMoriExtremal 𝕜 complete regular)
    (extra : Finset fan.Ray) (disjoint : Disjoint extra left)
    (cone : fan.finiteRayHull (right ∪ extra) ∈ fan.cones) (distinguished : left) :
    fan.finiteRayHull (left.erase distinguished.val ∪ right ∪ extra) ∈ fan.cones :=
  relation.coneExtension_of_moriCone_eq 𝕜 complete regular projective
    (fan.moriCone_eq_primitiveNumericalCone 𝕜 complete regular projective)
    extremal extra disjoint cone distinguished

end TauCeti.Toric.Fan

namespace BondalThomsen

theorem reidExtremalPrimitiveConeIncidence_proved : ReidExtremalPrimitiveConeIncidence 𝕜 := by
  intro Lattice Ambient _ _ _ _ embedding fan complete regular projective
    left right relation extremal extra disjoint_left _disjoint_right _extra_cone cone distinguished
  exact relation.coneExtension_of_isMoriExtremal 𝕜 complete regular projective
    extremal extra disjoint_left cone distinguished

end BondalThomsen
