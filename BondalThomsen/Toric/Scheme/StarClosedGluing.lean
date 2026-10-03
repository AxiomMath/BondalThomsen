module

public import BondalThomsen.Toric.Scheme.Separated
public import BondalThomsen.Fan.Completeness
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import BondalThomsen.Toric.Scheme.BasisChart
public import Mathlib.Algebra.MvPolynomial.Rename
public import BondalThomsen.Fan.StarFan
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import BondalThomsen.Toric.Scheme.Integral

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

def rayCharacterDescend (fan : Fan embedding) (ray : fan.Ray)
    (character : Lattice →+ ℤ) (vanishes : character ray.val = 0) :
    fan.StarLattice ray →+ ℤ :=
  (Submodule.liftQSpanSingleton ray.val character.toIntLinearMap vanishes).toAddMonoidHom

@[simp] theorem rayCharacterDescend_mkQ (fan : Fan embedding) (ray : fan.Ray)
    (character : Lattice →+ ℤ) (vanishes : character ray.val = 0) (vector : Lattice) :
    fan.rayCharacterDescend ray character vanishes
      ((Submodule.span ℤ {ray.val}).mkQ vector) = character vector := rfl

theorem rayCharacterDescend_pullback (fan : Fan embedding) (ray : fan.Ray)
    (character : Lattice →+ ℤ) (vanishes : character ray.val = 0) :
    (fan.rayCharacterDescend ray character vanishes).comp
      (Submodule.span ℤ {ray.val}).mkQ.toAddMonoidHom = character := by
  ext vector
  rfl

theorem rayCharacterDescend_zero (fan : Fan embedding) (ray : fan.Ray) :
    fan.rayCharacterDescend ray 0 (by simp) = 0 := by
  ext quotient_vector
  obtain ⟨vector, rfl⟩ := Submodule.mkQ_surjective (Submodule.span ℤ {ray.val}) quotient_vector
  rfl

theorem rayCharacterDescend_add (fan : Fan embedding) (ray : fan.Ray)
    (first second : Lattice →+ ℤ)
    (first_zero : first ray.val = 0) (second_zero : second ray.val = 0) :
    fan.rayCharacterDescend ray (first + second) (by simp [first_zero, second_zero]) =
      fan.rayCharacterDescend ray first first_zero +
        fan.rayCharacterDescend ray second second_zero := by
  ext quotient_vector
  obtain ⟨vector, rfl⟩ := Submodule.mkQ_surjective (Submodule.span ℤ {ray.val}) quotient_vector
  rfl

theorem rayCharacterDescend_realCharacter (fan : Fan embedding) (ray : fan.Ray)
    (character : Lattice →+ ℤ) (vanishes : character ray.val = 0) :
    ((fan.star ray).lattice.realCharacter (fan.rayCharacterDescend ray character vanishes)).comp
      (fan.starProjection ray) = fan.lattice.realCharacter character := by
  rw [← fan.lattice.realCharacter_comp (fan.star ray).lattice
    (Submodule.span ℤ {ray.val}).mkQ.toAddMonoidHom (fan.starProjection ray)
    (fun vector => (fan.starEmbedding_mkQ ray vector).symm),
    fan.rayCharacterDescend_pullback]

theorem rayCharacterDescend_mem_dualSemigroup (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (character : dualSemigroup fan.lattice cone)
    (vanishes : (character : Lattice →+ ℤ) ray.val = 0) :
    fan.rayCharacterDescend ray character vanishes ∈
      dualSemigroup (fan.star ray).lattice (PointedCone.map (fan.starProjection ray) cone) := by
  intro quotient_vector projected
  obtain ⟨vector, member, rfl⟩ := projected
  have equality := LinearMap.congr_fun
    (fan.rayCharacterDescend_realCharacter ray character vanishes) vector
  change 0 ≤ (fan.star ray).lattice.realCharacter
    (fan.rayCharacterDescend ray character vanishes) (fan.starProjection ray vector)
  rw [← LinearMap.comp_apply, fan.rayCharacterDescend_realCharacter]
  exact character.property member

noncomputable def rayFaceQuotientCharacter (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (character : dualSemigroup fan.lattice cone)
    (vanishes : (character : Lattice →+ ℤ) ray.val = 0) :
    dualSemigroup (fan.star ray).lattice (PointedCone.map (fan.starProjection ray) cone) :=
  ⟨fan.rayCharacterDescend ray character vanishes,
    fan.rayCharacterDescend_mem_dualSemigroup ray cone character vanishes⟩

theorem dualSemigroup_rayValue_nonnegative (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (contains : embedding ray.val ∈ cone)
    (character : dualSemigroup fan.lattice cone) : 0 ≤ (character : Lattice →+ ℤ) ray.val := by
  have nonnegative := character.property contains
  change 0 ≤ fan.lattice.realCharacter (character : Lattice →+ ℤ) (embedding ray.val) at nonnegative
  rw [fan.lattice.realCharacter_apply] at nonnegative
  exact_mod_cast nonnegative

noncomputable def rayFaceMonomialMap (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (contains : embedding ray.val ∈ cone) :
    Multiplicative (dualSemigroup fan.lattice cone) →*
      affineCoordinateRing 𝕜 (fan.star ray).lattice (PointedCone.map (fan.starProjection ray) cone) := by
  classical
  refine {
    toFun := fun exponent =>
      if vanishes : (toAdd exponent).val ray.val = 0 then
        MonoidAlgebra.single (ofAdd (fan.rayFaceQuotientCharacter ray cone (toAdd exponent) vanishes)) 1
      else 0
    map_one' := ?_
    map_mul' := ?_ }
  · simp only [toAdd_one, AddSubmonoid.coe_zero, AddMonoidHom.zero_apply, dite_true]
    have quotient_zero : fan.rayFaceQuotientCharacter ray cone 0 (by simp) = 0 := by
      apply Subtype.ext
      exact fan.rayCharacterDescend_zero ray
    rw [quotient_zero]
    rfl
  · intro first second
    have first_nonnegative := fan.dualSemigroup_rayValue_nonnegative ray cone contains (toAdd first)
    have second_nonnegative := fan.dualSemigroup_rayValue_nonnegative ray cone contains (toAdd second)
    have sum_zero_iff : ((toAdd (first * second) : dualSemigroup fan.lattice cone) : Lattice →+ ℤ)
        ray.val = 0 ↔ (toAdd first).val ray.val = 0 ∧
          (toAdd second).val ray.val = 0 := by
      change (toAdd first).val ray.val + (toAdd second).val ray.val = 0 ↔ _
      omega
    by_cases first_zero : (toAdd first).val ray.val = 0
    · by_cases second_zero : (toAdd second).val ray.val = 0
      · have sum_zero := sum_zero_iff.mpr ⟨first_zero, second_zero⟩
        simp only [dite_eq_left first_zero, dite_eq_left second_zero, dite_eq_left sum_zero]
        rw [MonoidAlgebra.single_mul_single, mul_one]
        congr 2
        apply Subtype.ext
        exact fan.rayCharacterDescend_add ray (toAdd first).val (toAdd second).val
          first_zero second_zero
      · have sum_nonzero : ((toAdd (first * second) : dualSemigroup fan.lattice cone) : Lattice →+ ℤ)
            ray.val ≠ 0 := fun equality => second_zero (sum_zero_iff.mp equality).2
        simp only [dite_eq_right sum_nonzero, dite_eq_right second_zero, mul_zero]
    · have sum_nonzero : ((toAdd (first * second) : dualSemigroup fan.lattice cone) : Lattice →+ ℤ)
          ray.val ≠ 0 := fun equality => first_zero (sum_zero_iff.mp equality).1
      simp only [dite_eq_right sum_nonzero, dite_eq_right first_zero, zero_mul]

noncomputable def rayFaceCoordinateRingMap (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (contains : embedding ray.val ∈ cone) :
    affineCoordinateRing 𝕜 fan.lattice cone →ₐ[𝕜]
      (affineCoordinateRing 𝕜) (fan.star ray).lattice (PointedCone.map (fan.starProjection ray) cone) :=
  MonoidAlgebra.lift 𝕜 _ _ (fan.rayFaceMonomialMap 𝕜 ray cone contains)

theorem rayFaceCoordinateRingMap_single_of_zero (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (contains : embedding ray.val ∈ cone)
    (character : dualSemigroup fan.lattice cone)
    (vanishes : (character : Lattice →+ ℤ) ray.val = 0) :
    fan.rayFaceCoordinateRingMap 𝕜 ray cone contains (MonoidAlgebra.single (ofAdd character) 1) =
      MonoidAlgebra.single (ofAdd (fan.rayFaceQuotientCharacter ray cone character vanishes)) 1 := by
  classical
  simp [rayFaceCoordinateRingMap, rayFaceMonomialMap, vanishes]

theorem rayFaceCoordinateRingMap_single_of_nonzero (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (contains : embedding ray.val ∈ cone)
    (character : dualSemigroup fan.lattice cone)
    (nonzero : (character : Lattice →+ ℤ) ray.val ≠ 0) :
    fan.rayFaceCoordinateRingMap 𝕜 ray cone contains (MonoidAlgebra.single (ofAdd character) 1) = 0 := by
  classical
  simp [rayFaceCoordinateRingMap, rayFaceMonomialMap, nonzero]

theorem rayFaceCoordinateRingMap_face (fan : Fan embedding) (ray : fan.Ray)
    {face cone : PointedCone ℝ Ambient} (is_face : face.IsFaceOf cone)
    (contains : embedding ray.val ∈ face) :
    (fan.rayFaceCoordinateRingMap 𝕜 ray face contains).comp
      (faceAffineCoordinateRingMap 𝕜 fan.lattice is_face) =
      (faceAffineCoordinateRingMap 𝕜 (fan.star ray).lattice
        (BondalThomsen.rayQuotient_map_isFaceOf (embedding ray.val) is_face contains)).comp
          (fan.rayFaceCoordinateRingMap 𝕜 ray cone (is_face.le contains)) := by
  apply MonoidAlgebra.algHom_ext
  · intro exponent
    let character := toAdd exponent
    change (fan.rayFaceCoordinateRingMap 𝕜 ray face contains)
      (faceAffineCoordinateRingMap 𝕜 fan.lattice is_face
        (MonoidAlgebra.single (ofAdd character) 1)) =
      faceAffineCoordinateRingMap 𝕜 (fan.star ray).lattice
        (BondalThomsen.rayQuotient_map_isFaceOf (embedding ray.val) is_face contains)
          (fan.rayFaceCoordinateRingMap 𝕜 ray cone (is_face.le contains)
            (MonoidAlgebra.single (ofAdd character) 1))
    by_cases vanishes : (character : Lattice →+ ℤ) ray.val = 0
    · rw [faceAffineCoordinateRingMap_single]
      rw [fan.rayFaceCoordinateRingMap_single_of_zero 𝕜 ray cone (is_face.le contains)
        character vanishes]
      have restriction := faceAffineCoordinateRingMap_single 𝕜 (fan.star ray).lattice
        (BondalThomsen.rayQuotient_map_isFaceOf (embedding ray.val) is_face contains)
        (fan.rayFaceQuotientCharacter ray cone character vanishes) (1 : 𝕜)
      refine (fan.rayFaceCoordinateRingMap_single_of_zero 𝕜 ray face contains _ vanishes).trans ?_
      refine Eq.trans ?_ restriction.symm
      apply congrArg (fun quotient_character => MonoidAlgebra.single (ofAdd quotient_character) 1)
      apply Subtype.ext
      rfl
    · rw [faceAffineCoordinateRingMap_single]
      rw [fan.rayFaceCoordinateRingMap_single_of_nonzero 𝕜 ray cone (is_face.le contains)
        character vanishes, map_zero]
      exact fan.rayFaceCoordinateRingMap_single_of_nonzero 𝕜 ray face contains _ vanishes
  · exact Subsingleton.elim _ _

noncomputable def rayFaceAffineSchemeMap (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (contains : embedding ray.val ∈ cone) :
    affineToricScheme 𝕜 (fan.star ray).lattice (PointedCone.map (fan.starProjection ray) cone) ⟶
      affineToricScheme 𝕜 fan.lattice cone :=
  Spec.map (CommRingCat.ofHom (fan.rayFaceCoordinateRingMap 𝕜 ray cone contains).toRingHom)

theorem rayFaceAffineSchemeMap_face (fan : Fan embedding) (ray : fan.Ray)
    {face cone : PointedCone ℝ Ambient} (is_face : face.IsFaceOf cone)
    (contains : embedding ray.val ∈ face) :
    faceAffineToricSchemeMap 𝕜 (fan.star ray).lattice
      (BondalThomsen.rayQuotient_map_isFaceOf (embedding ray.val) is_face contains) ≫
        fan.rayFaceAffineSchemeMap 𝕜 ray cone (is_face.le contains) =
      fan.rayFaceAffineSchemeMap 𝕜 ray face contains ≫
        faceAffineToricSchemeMap 𝕜 fan.lattice is_face := by
  rw [faceAffineToricSchemeMap_def, faceAffineToricSchemeMap_def,
    rayFaceAffineSchemeMap, rayFaceAffineSchemeMap, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun ring_map => Spec.map (CommRingCat.ofHom ring_map.toRingHom))
    (fan.rayFaceCoordinateRingMap_face 𝕜 ray is_face contains).symm

theorem exists_starConeLift (fan : Fan embedding) (ray : fan.Ray)
    (cone : (fan.star ray).cones) :
    ∃ original : fan.cones, embedding ray.val ∈ original.val ∧
      PointedCone.map (fan.starProjection ray) original.val = cone.val := by
  obtain ⟨original, ⟨member, contains⟩, projected⟩ := cone.property
  exact ⟨⟨original, member⟩, contains, projected⟩

noncomputable def starConeLift (fan : Fan embedding) (ray : fan.Ray)
    (cone : (fan.star ray).cones) : fan.cones :=
  Classical.choose (fan.exists_starConeLift ray cone)

theorem starConeLift_contains (fan : Fan embedding) (ray : fan.Ray)
    (cone : (fan.star ray).cones) : embedding ray.val ∈ (fan.starConeLift ray cone).val :=
  (Classical.choose_spec (fan.exists_starConeLift ray cone)).1

theorem starConeLift_projected (fan : Fan embedding) (ray : fan.Ray)
    (cone : (fan.star ray).cones) :
    PointedCone.map (fan.starProjection ray) (fan.starConeLift ray cone).val = cone.val :=
  (Classical.choose_spec (fan.exists_starConeLift ray cone)).2

theorem rayContainingCone_le_of_projected_le (fan : Fan embedding) (ray : fan.Ray)
    (first second : fan.cones) (first_contains : embedding ray.val ∈ first.val)
    (second_contains : embedding ray.val ∈ second.val)
    (projected_le : PointedCone.map (fan.starProjection ray) first.val ≤
      PointedCone.map (fan.starProjection ray) second.val) : first.val ≤ second.val := by
  intro vector member
  have in_intersection : fan.starProjection ray vector ∈
      PointedCone.map (fan.starProjection ray) (first.val ⊓ second.val) := by
    change (Submodule.span ℝ {embedding ray.val}).mkQ vector ∈
      PointedCone.map (Submodule.span ℝ {embedding ray.val}).mkQ (first.val ⊓ second.val)
    rw [BondalThomsen.rayQuotient_map_inf _ _ _ first_contains second_contains]
    exact ⟨⟨vector, member, rfl⟩, projected_le ⟨vector, member, rfl⟩⟩
  exact (BondalThomsen.rayQuotient_face_saturated (embedding ray.val)
    (fan.inf_isFaceOf_left first.property second.property)
    ⟨first_contains, second_contains⟩ member in_intersection).2

theorem starConeLift_eq_of_projected (fan : Fan embedding) (ray : fan.Ray)
    (cone : (fan.star ray).cones) (original : fan.cones)
    (contains : embedding ray.val ∈ original.val)
    (projected : PointedCone.map (fan.starProjection ray) original.val = cone.val) :
    fan.starConeLift ray cone = original := by
  apply Subtype.ext
  apply le_antisymm
  · apply fan.rayContainingCone_le_of_projected_le ray _ _
      (fan.starConeLift_contains ray cone) contains
    rw [fan.starConeLift_projected ray cone, projected]
  · apply fan.rayContainingCone_le_of_projected_le ray _ _ contains
      (fan.starConeLift_contains ray cone)
    rw [fan.starConeLift_projected ray cone, projected]

theorem starConeLift_mono (fan : Fan embedding) (ray : fan.Ray)
    {first second : (fan.star ray).cones} (inclusion : first.val ≤ second.val) :
    (fan.starConeLift ray first).val ≤ (fan.starConeLift ray second).val := by
  apply fan.rayContainingCone_le_of_projected_le ray _ _
    (fan.starConeLift_contains ray first) (fan.starConeLift_contains ray second)
  rw [fan.starConeLift_projected ray first, fan.starConeLift_projected ray second]
  exact inclusion

theorem starConeLift_isFaceOf (fan : Fan embedding) (ray : fan.Ray)
    {first second : (fan.star ray).cones} (inclusion : first.val ≤ second.val) :
    (fan.starConeLift ray first).val.IsFaceOf (fan.starConeLift ray second).val :=
  fan.isFaceOf_of_le (fan.starConeLift ray second).property
    (fan.starConeLift ray first).property (fan.starConeLift_mono ray inclusion)

noncomputable def rayFaceChartMap (fan : Fan embedding) (ray : fan.Ray)
    (cone : (fan.star ray).cones) :
    (fan.star ray).affineToricChart 𝕜 cone ⟶ fan.affineToricChart 𝕜 (fan.starConeLift ray cone) :=
  eqToHom (congrArg (affineToricScheme 𝕜 (fan.star ray).lattice)
    (fan.starConeLift_projected ray cone).symm) ≫
      fan.rayFaceAffineSchemeMap 𝕜 ray (fan.starConeLift ray cone).val
        (fan.starConeLift_contains ray cone)

theorem rayFaceAffineSchemeMap_face_transport (fan : Fan embedding) (ray : fan.Ray)
    {face cone : PointedCone ℝ Ambient} (is_face : face.IsFaceOf cone)
    (contains : embedding ray.val ∈ face)
    (projected_face projected_cone : PointedCone ℝ (fan.StarAmbient ray))
    (face_eq : PointedCone.map (fan.starProjection ray) face = projected_face)
    (cone_eq : PointedCone.map (fan.starProjection ray) cone = projected_cone)
    (quotient_face : projected_face.IsFaceOf projected_cone) :
    faceAffineToricSchemeMap 𝕜 (fan.star ray).lattice quotient_face ≫
      eqToHom (congrArg (affineToricScheme 𝕜 (fan.star ray).lattice) cone_eq.symm) ≫
        fan.rayFaceAffineSchemeMap 𝕜 ray cone (is_face.le contains) =
      eqToHom (congrArg (affineToricScheme 𝕜 (fan.star ray).lattice) face_eq.symm) ≫
        fan.rayFaceAffineSchemeMap 𝕜 ray face contains ≫
          faceAffineToricSchemeMap 𝕜 fan.lattice is_face := by
  subst projected_face
  subst projected_cone
  simpa using fan.rayFaceAffineSchemeMap_face 𝕜 ray is_face contains

theorem rayFaceChartMap_face (fan : Fan embedding) (ray : fan.Ray)
    {face cone : (fan.star ray).cones} (inclusion : face.val ≤ cone.val) :
    faceAffineToricSchemeMap 𝕜 (fan.star ray).lattice
      ((fan.star ray).isFaceOf_of_le cone.property face.property inclusion) ≫
        fan.rayFaceChartMap 𝕜 ray cone =
      fan.rayFaceChartMap 𝕜 ray face ≫ faceAffineToricSchemeMap 𝕜 fan.lattice
        (fan.starConeLift_isFaceOf ray inclusion) := by
  exact fan.rayFaceAffineSchemeMap_face_transport 𝕜 ray
    (fan.starConeLift_isFaceOf ray inclusion) (fan.starConeLift_contains ray face)
    face.val cone.val (fan.starConeLift_projected ray face)
    (fan.starConeLift_projected ray cone)
    ((fan.star ray).isFaceOf_of_le cone.property face.property inclusion)

noncomputable def rayFaceGlobalCocone (fan : Fan embedding) (regular : fan.IsRegular)
    (ray : fan.Ray) : Cocone ((fan.star ray).affineToricDiagram 𝕜) where
  pt := fan.algebraicRealization 𝕜 regular
  ι := {
    app := fun cone => fan.rayFaceChartMap 𝕜 ray cone ≫
      fan.affineToricChartι 𝕜 regular (fan.starConeLift ray cone)
    naturality := by
      intro face cone inclusion
      change faceAffineToricSchemeMap 𝕜 (fan.star ray).lattice
        ((fan.star ray).isFaceOf_of_le cone.property face.property (leOfHom inclusion)) ≫
          (fan.rayFaceChartMap 𝕜 ray cone ≫
            fan.affineToricChartι 𝕜 regular (fan.starConeLift ray cone)) = _
      rw [← Category.assoc, fan.rayFaceChartMap_face 𝕜 ray (leOfHom inclusion), Category.assoc,
        fan.faceAffineToricSchemeMap_comp_affineToricChartι 𝕜 regular]
      rfl }

noncomputable def starOrbitClosureMap (fan : Fan embedding) (regular : fan.IsRegular)
    (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular) :
    (fan.star ray).algebraicRealization 𝕜 star_regular ⟶ fan.algebraicRealization 𝕜 regular :=
  ((fan.star ray).isColimitAffineToricCocone 𝕜 star_regular).desc
    (fan.rayFaceGlobalCocone 𝕜 regular ray)

theorem affineToricChartι_comp_starOrbitClosureMap (fan : Fan embedding)
    (regular : fan.IsRegular) (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular)
    (cone : (fan.star ray).cones) :
    (fan.star ray).affineToricChartι 𝕜 star_regular cone ≫
        fan.starOrbitClosureMap 𝕜 regular ray star_regular =
      fan.rayFaceChartMap 𝕜 ray cone ≫
        fan.affineToricChartι 𝕜 regular (fan.starConeLift ray cone) :=
  ((fan.star ray).isColimitAffineToricCocone 𝕜 star_regular).fac
    (fan.rayFaceGlobalCocone 𝕜 regular ray) cone

noncomputable def rayFaceCoordinateRingSection (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) :
    affineCoordinateRing 𝕜 (fan.star ray).lattice (PointedCone.map (fan.starProjection ray) cone) →ₐ[𝕜]
      (affineCoordinateRing 𝕜) fan.lattice cone :=
  affineCoordinateRingMap 𝕜 fan.lattice (fan.star ray).lattice
    (Submodule.span ℤ {ray.val}).mkQ.toAddMonoidHom (fan.starProjection ray)
    (fun vector => (fan.starEmbedding_mkQ ray vector).symm)
    (fun vector member => ⟨vector, member, rfl⟩)

theorem rayFaceCoordinateRingMap_comp_section (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (contains : embedding ray.val ∈ cone) :
    (fan.rayFaceCoordinateRingMap 𝕜 ray cone contains).comp
      (fan.rayFaceCoordinateRingSection 𝕜 ray cone) =
        AlgHom.id 𝕜 (affineCoordinateRing 𝕜 (fan.star ray).lattice
          (PointedCone.map (fan.starProjection ray) cone)) := by
  apply MonoidAlgebra.algHom_ext
  · intro exponent
    let character := toAdd exponent
    change fan.rayFaceCoordinateRingMap 𝕜 ray cone contains
      (fan.rayFaceCoordinateRingSection 𝕜 ray cone (MonoidAlgebra.single (ofAdd character) 1)) =
        MonoidAlgebra.single (ofAdd character) 1
    rw [rayFaceCoordinateRingSection, affineCoordinateRingMap_single]
    let pulled := dualSemigroupMap fan.lattice (fan.star ray).lattice
      (σ := cone) (τ := PointedCone.map (fan.starProjection ray) cone)
      (Submodule.span ℤ {ray.val}).mkQ.toAddMonoidHom (fan.starProjection ray)
      (fun vector => (fan.starEmbedding_mkQ ray vector).symm)
      (fun vector member => ⟨vector, member, rfl⟩) character
    have zero : (pulled : Lattice →+ ℤ) ray.val = 0 := by
      rw [dualSemigroupMap_apply]
      have killed : (Submodule.span ℤ {ray.val}).mkQ ray.val = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Set.mem_singleton _)
      change (character : fan.StarLattice ray →+ ℤ)
        ((Submodule.span ℤ {ray.val}).mkQ ray.val) = 0
      rw [killed, map_zero]
    rw [fan.rayFaceCoordinateRingMap_single_of_zero 𝕜 ray cone contains pulled zero]
    apply congrArg (fun quotient_character => MonoidAlgebra.single (ofAdd quotient_character) 1)
    apply Subtype.ext
    ext quotient_vector
    obtain ⟨vector, rfl⟩ := Submodule.mkQ_surjective (Submodule.span ℤ {ray.val}) quotient_vector
    rw [rayFaceQuotientCharacter, fan.rayCharacterDescend_mkQ]
    exact dualSemigroupMap_apply _ _ _ _ _ _ _ vector
  · exact Subsingleton.elim _ _

theorem rayFaceCoordinateRingMap_surjective (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (contains : embedding ray.val ∈ cone) :
    Function.Surjective (fan.rayFaceCoordinateRingMap 𝕜 ray cone contains) := by
  intro element
  exact ⟨fan.rayFaceCoordinateRingSection 𝕜 ray cone element,
    AlgHom.congr_fun (fan.rayFaceCoordinateRingMap_comp_section 𝕜 ray cone contains) element⟩

theorem rayFaceAffineSchemeMap_isClosedImmersion (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (contains : embedding ray.val ∈ cone) :
    IsClosedImmersion (fan.rayFaceAffineSchemeMap 𝕜 ray cone contains) :=
  IsClosedImmersion.spec_of_surjective _ (fan.rayFaceCoordinateRingMap_surjective 𝕜 ray cone contains)

theorem rayFaceChartMap_isClosedImmersion (fan : Fan embedding) (ray : fan.Ray)
    (cone : (fan.star ray).cones) : IsClosedImmersion (fan.rayFaceChartMap 𝕜 ray cone) := by
  unfold rayFaceChartMap
  let := fan.rayFaceAffineSchemeMap_isClosedImmersion 𝕜 ray (fan.starConeLift ray cone).val
    (fan.starConeLift_contains ray cone)
  infer_instance

noncomputable def completeStarOrbitClosureMap [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) (ray : fan.Ray) :
    (fan.star ray).algebraicRealization 𝕜 (fan.star_isRegular complete regular ray) ⟶
      fan.algebraicRealization 𝕜 regular :=
  fan.starOrbitClosureMap 𝕜 regular ray (fan.star_isRegular complete regular ray)

theorem rayCharacterDescend_projected_cut (fan : Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (vanishes : character ray.val = 0) :
    PointedCone.map (fan.starProjection ray) cone ⊓
        PointedCone.ofSubmodule (LinearMap.ker ((fan.star ray).lattice.realCharacter
          (fan.rayCharacterDescend ray character vanishes))) =
      PointedCone.map (fan.starProjection ray)
        (cone ⊓ PointedCone.ofSubmodule (LinearMap.ker (fan.lattice.realCharacter character))) := by
  ext quotient_vector
  constructor
  · rintro ⟨⟨vector, member, rfl⟩, killed⟩
    refine ⟨vector, ⟨member, ?_⟩, rfl⟩
    change fan.lattice.realCharacter character vector = 0
    exact (LinearMap.congr_fun (fan.rayCharacterDescend_realCharacter ray character vanishes)
      vector).symm.trans killed
  · rintro ⟨vector, ⟨member, killed⟩, rfl⟩
    refine ⟨⟨vector, member, rfl⟩, ?_⟩
    change (fan.star ray).lattice.realCharacter
      (fan.rayCharacterDescend ray character vanishes) (fan.starProjection ray vector) = 0
    exact (LinearMap.congr_fun (fan.rayCharacterDescend_realCharacter ray character vanishes)
      vector).trans killed

theorem rayFaceAffineSchemeMap_preimage_face (fan : Fan embedding) (ray : fan.Ray)
    {face cone : PointedCone ℝ Ambient} (member : cone ∈ fan.cones)
    (regular : TauCeti.Toric.IsRegularCone embedding cone) (is_face : face.IsFaceOf cone)
    (contains : embedding ray.val ∈ face) :
    (fan.rayFaceAffineSchemeMap 𝕜 ray cone (is_face.le contains)) ⁻¹'
      Set.range (faceAffineToricSchemeMap 𝕜 fan.lattice is_face) =
        Set.range (faceAffineToricSchemeMap 𝕜 (fan.star ray).lattice
          (BondalThomsen.rayQuotient_map_isFaceOf (embedding ray.val) is_face contains)) := by
  obtain ⟨character, character_member, cut⟩ :=
    regular.exists_mem_dualSemigroup_inf_ker_eq fan.lattice is_face
  have vanishes : character ray.val = 0 := by
    have killed : fan.lattice.realCharacter character (embedding ray.val) = 0 := by
      exact (show embedding ray.val ∈ cone ⊓
        PointedCone.ofSubmodule (LinearMap.ker (fan.lattice.realCharacter character)) from
          cut.symm ▸ contains).2
    rw [fan.lattice.realCharacter_apply] at killed
    exact_mod_cast killed
  let monomial_character : dualSemigroup fan.lattice cone := ⟨character, character_member⟩
  have projected_cut : PointedCone.map (fan.starProjection ray) cone ⊓
      PointedCone.ofSubmodule (LinearMap.ker ((fan.star ray).lattice.realCharacter
        (fan.rayFaceQuotientCharacter ray cone monomial_character vanishes))) =
      PointedCone.map (fan.starProjection ray) face := by
    exact (fan.rayCharacterDescend_projected_cut ray cone character vanishes).trans
      (congrArg (PointedCone.map (fan.starProjection ray)) cut)
  have original_range := range_faceAffineToricSchemeMap_of_eq 𝕜 fan.lattice regular.fg
    is_face monomial_character cut
  have projected_range := range_faceAffineToricSchemeMap_of_eq 𝕜 (fan.star ray).lattice
    (fan.starCone_isToricCone ray cone member (is_face.le contains)).fg
    (BondalThomsen.rayQuotient_map_isFaceOf (embedding ray.val) is_face contains)
    (fan.rayFaceQuotientCharacter ray cone monomial_character vanishes) projected_cut
  refine Eq.trans (congrArg
    (fun region => (fan.rayFaceAffineSchemeMap 𝕜 ray cone (is_face.le contains)) ⁻¹' region)
      original_range) ?_
  refine Eq.trans ?_ projected_range.symm
  ext point
  change MonoidAlgebra.single (ofAdd monomial_character) 1 ∉
      (PrimeSpectrum.comap (fan.rayFaceCoordinateRingMap 𝕜 ray cone (is_face.le contains)).toRingHom
        point).asIdeal ↔ _
  change fan.rayFaceCoordinateRingMap 𝕜 ray cone (is_face.le contains)
      (MonoidAlgebra.single (ofAdd monomial_character) 1) ∉ point.asIdeal ↔ _
  rw [fan.rayFaceCoordinateRingMap_single_of_zero 𝕜 ray cone (is_face.le contains)
    monomial_character vanishes]
  rfl

theorem rayFaceAffineSchemeMap_preimage_face_without_ray (fan : Fan embedding) (ray : fan.Ray)
    {face cone : PointedCone ℝ Ambient} (regular : TauCeti.Toric.IsRegularCone embedding cone)
    (is_face : face.IsFaceOf cone) (contains : embedding ray.val ∈ cone)
    (absent : embedding ray.val ∉ face) :
    (fan.rayFaceAffineSchemeMap 𝕜 ray cone contains) ⁻¹'
      Set.range (faceAffineToricSchemeMap 𝕜 fan.lattice is_face) = ∅ := by
  obtain ⟨character, character_member, cut⟩ :=
    regular.exists_mem_dualSemigroup_inf_ker_eq fan.lattice is_face
  have nonzero : character ray.val ≠ 0 := by
    intro zero
    apply absent
    rw [← cut]
    refine ⟨contains, ?_⟩
    change fan.lattice.realCharacter character (embedding ray.val) = 0
    rw [fan.lattice.realCharacter_apply, zero, Int.cast_zero]
  let monomial_character : dualSemigroup fan.lattice cone := ⟨character, character_member⟩
  rw [range_faceAffineToricSchemeMap_of_eq 𝕜 fan.lattice regular.fg is_face monomial_character cut]
  ext point
  change MonoidAlgebra.single (ofAdd monomial_character) 1 ∉
      (PrimeSpectrum.comap (fan.rayFaceCoordinateRingMap 𝕜 ray cone contains).toRingHom point).asIdeal ↔ False
  change fan.rayFaceCoordinateRingMap 𝕜 ray cone contains
      (MonoidAlgebra.single (ofAdd monomial_character) 1) ∉ point.asIdeal ↔ False
  rw [fan.rayFaceCoordinateRingMap_single_of_nonzero 𝕜 ray cone contains monomial_character nonzero]
  simp

theorem rayFaceAffineSchemeMap_preimage_face_transport (fan : Fan embedding) (ray : fan.Ray)
    {face cone : PointedCone ℝ Ambient} (member : cone ∈ fan.cones)
    (regular : TauCeti.Toric.IsRegularCone embedding cone) (is_face : face.IsFaceOf cone)
    (contains : embedding ray.val ∈ face)
    (projected_face projected_cone : PointedCone ℝ (fan.StarAmbient ray))
    (face_eq : PointedCone.map (fan.starProjection ray) face = projected_face)
    (cone_eq : PointedCone.map (fan.starProjection ray) cone = projected_cone)
    (quotient_face : projected_face.IsFaceOf projected_cone) :
    (eqToHom (congrArg (affineToricScheme 𝕜 (fan.star ray).lattice) cone_eq.symm) ≫
      fan.rayFaceAffineSchemeMap 𝕜 ray cone (is_face.le contains)) ⁻¹'
        Set.range (faceAffineToricSchemeMap 𝕜 fan.lattice is_face) =
      Set.range (faceAffineToricSchemeMap 𝕜 (fan.star ray).lattice quotient_face) := by
  cases face_eq
  cases cone_eq
  have same : quotient_face =
      BondalThomsen.rayQuotient_map_isFaceOf (embedding ray.val) is_face contains := Subsingleton.elim _ _
  subst quotient_face
  change (fan.rayFaceAffineSchemeMap 𝕜 ray cone (is_face.le contains)) ⁻¹'
      Set.range (faceAffineToricSchemeMap 𝕜 fan.lattice is_face) =
    Set.range (faceAffineToricSchemeMap 𝕜 (fan.star ray).lattice
      (BondalThomsen.rayQuotient_map_isFaceOf (embedding ray.val) is_face contains))
  exact fan.rayFaceAffineSchemeMap_preimage_face 𝕜 ray member regular is_face contains

theorem rayFaceChartMap_preimage_overlap (fan : Fan embedding) (regular : fan.IsRegular)
    (ray : fan.Ray) (first second : (fan.star ray).cones) :
    (fan.rayFaceChartMap 𝕜 ray first) ⁻¹'
      Set.range (fan.affineToricOverlapLeft 𝕜 (fan.starConeLift ray first)
        (fan.starConeLift ray second)) =
      Set.range ((fan.star ray).affineToricOverlapLeft 𝕜 first second) := by
  have projected_inf : PointedCone.map (fan.starProjection ray)
      ((fan.starConeLift ray first).val ⊓ (fan.starConeLift ray second).val) = first.val ⊓ second.val := by
    change PointedCone.map (Submodule.span ℝ {embedding ray.val}).mkQ _ = _
    rw [BondalThomsen.rayQuotient_map_inf _ _ _
      (fan.starConeLift_contains ray first) (fan.starConeLift_contains ray second)]
    exact congrArg₂ (fun left right : PointedCone ℝ (fan.StarAmbient ray) => left ⊓ right)
      (fan.starConeLift_projected ray first) (fan.starConeLift_projected ray second)
  exact fan.rayFaceAffineSchemeMap_preimage_face_transport 𝕜 ray
    (fan.starConeLift ray first).property (regular (fan.starConeLift ray first).property)
    (fan.inf_isFaceOf_left (fan.starConeLift ray first).property (fan.starConeLift ray second).property)
    ⟨fan.starConeLift_contains ray first, fan.starConeLift_contains ray second⟩
    (first.val ⊓ second.val) first.val projected_inf (fan.starConeLift_projected ray first)
    ((fan.star ray).inf_isFaceOf_left first.property second.property)

theorem starOrbitClosureMap_preimage_lifted_chart (fan : Fan embedding)
    (regular : fan.IsRegular) (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular)
    (cone : (fan.star ray).cones) :
    (fan.starOrbitClosureMap 𝕜 regular ray star_regular) ⁻¹'
      Set.range (fan.affineToricChartι 𝕜 regular (fan.starConeLift ray cone)) =
        Set.range ((fan.star ray).affineToricChartι 𝕜 star_regular cone) := by
  ext point
  obtain ⟨source_cone, source_point, rfl⟩ :=
    (fan.star ray).exists_affineToricChartι_apply_eq 𝕜 star_regular point
  have mapped := congrArg (fun morphism : (fan.star ray).affineToricChart 𝕜 source_cone ⟶
      fan.algebraicRealization 𝕜 regular => morphism source_point)
    (fan.affineToricChartι_comp_starOrbitClosureMap 𝕜 regular ray star_regular source_cone)
  simp only [Scheme.Hom.comp_apply] at mapped
  change fan.starOrbitClosureMap 𝕜 regular ray star_regular
    ((fan.star ray).affineToricChartι 𝕜 star_regular source_cone source_point) ∈
      Set.range (fan.affineToricChartι 𝕜 regular (fan.starConeLift ray cone)) ↔
    (fan.star ray).affineToricChartι 𝕜 star_regular source_cone source_point ∈
      Set.range ((fan.star ray).affineToricChartι 𝕜 star_regular cone)
  rw [mapped]
  constructor
  · rintro ⟨target_point, same⟩
    obtain ⟨overlap_point, left_eq, right_eq⟩ :=
      (fan.affineToricChartι_eq_affineToricChartι_iff 𝕜 regular
        (fan.rayFaceChartMap 𝕜 ray source_cone source_point) target_point).mp same.symm
    have member : source_point ∈ Set.range ((fan.star ray).affineToricOverlapLeft 𝕜 source_cone cone) :=
      (Set.ext_iff.mp (fan.rayFaceChartMap_preimage_overlap 𝕜 regular ray source_cone cone) source_point).mp
        ⟨overlap_point, left_eq⟩
    obtain ⟨star_overlap, star_left_eq⟩ := member
    refine ⟨(fan.star ray).affineToricOverlapRight 𝕜 source_cone cone star_overlap, ?_⟩
    have chart_equality := congrArg (fun morphism : (fan.star ray).affineToricOverlap 𝕜 source_cone cone ⟶
        (fan.star ray).algebraicRealization 𝕜 star_regular => morphism star_overlap)
      ((fan.star ray).affineToricOverlap_comp_affineToricChartι 𝕜 star_regular source_cone cone)
    simpa only [Scheme.Hom.comp_apply, star_left_eq] using chart_equality.symm
  · rintro ⟨target_point, same⟩
    have star_overlap := ((fan.star ray).affineToricChartι_eq_affineToricChartι_iff 𝕜 star_regular
      source_point target_point).mp same.symm
    obtain ⟨overlap_point, left_eq, right_eq⟩ := star_overlap
    have member : fan.rayFaceChartMap 𝕜 ray source_cone source_point ∈
        Set.range (fan.affineToricOverlapLeft 𝕜 (fan.starConeLift ray source_cone)
          (fan.starConeLift ray cone)) :=
      (Set.ext_iff.mp (fan.rayFaceChartMap_preimage_overlap 𝕜 regular ray source_cone cone) source_point).mpr
        ⟨overlap_point, left_eq⟩
    obtain ⟨original_overlap, original_left_eq⟩ := member
    refine ⟨fan.affineToricOverlapRight 𝕜 (fan.starConeLift ray source_cone)
      (fan.starConeLift ray cone) original_overlap, ?_⟩
    have chart_equality := congrArg (fun morphism : fan.affineToricOverlap 𝕜
        (fan.starConeLift ray source_cone) (fan.starConeLift ray cone) ⟶
          fan.algebraicRealization 𝕜 regular => morphism original_overlap)
      (fan.affineToricOverlap_comp_affineToricChartι 𝕜 regular (fan.starConeLift ray source_cone)
        (fan.starConeLift ray cone))
    simpa only [Scheme.Hom.comp_apply, original_left_eq] using chart_equality.symm

theorem starOrbitClosureMap_lifted_chart_isPullback (fan : Fan embedding)
    (regular : fan.IsRegular) (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular)
    (cone : (fan.star ray).cones) :
    IsPullback (fan.rayFaceChartMap 𝕜 ray cone)
      ((fan.star ray).affineToricChartι 𝕜 star_regular cone)
      (fan.affineToricChartι 𝕜 regular (fan.starConeLift ray cone))
      (fan.starOrbitClosureMap 𝕜 regular ray star_regular) := by
  apply IsOpenImmersion.isPullback
  · exact fan.affineToricChartι_comp_starOrbitClosureMap 𝕜 regular ray star_regular cone
  · ext point
    exact Set.ext_iff.mp (fan.starOrbitClosureMap_preimage_lifted_chart 𝕜 regular ray star_regular cone) point

theorem rayFaceChartMap_not_mem_face_without_ray (fan : Fan embedding) (regular : fan.IsRegular)
    (ray : fan.Ray) (cone : (fan.star ray).cones) (face : PointedCone ℝ Ambient)
    (is_face : face.IsFaceOf (fan.starConeLift ray cone).val)
    (absent : embedding ray.val ∉ face) (point : (fan.star ray).affineToricChart 𝕜 cone) :
    fan.rayFaceChartMap 𝕜 ray cone point ∉ Set.range (faceAffineToricSchemeMap 𝕜 fan.lattice is_face) := by
  have empty := fan.rayFaceAffineSchemeMap_preimage_face_without_ray 𝕜 ray
    (regular (fan.starConeLift ray cone).property) is_face
    (fan.starConeLift_contains ray cone) absent
  change fan.rayFaceAffineSchemeMap 𝕜 ray (fan.starConeLift ray cone).val
      (fan.starConeLift_contains ray cone)
        (eqToHom (congrArg (affineToricScheme 𝕜 (fan.star ray).lattice)
          (fan.starConeLift_projected ray cone).symm) point) ∉ _
  exact fun member => (Set.ext_iff.mp empty
    (eqToHom (congrArg (affineToricScheme 𝕜 (fan.star ray).lattice)
      (fan.starConeLift_projected ray cone).symm) point)).mp member

theorem starOrbitClosureMap_preimage_chart_without_ray (fan : Fan embedding)
    (regular : fan.IsRegular) (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular)
    (cone : fan.cones) (absent : embedding ray.val ∉ cone.val) :
    (fan.starOrbitClosureMap 𝕜 regular ray star_regular) ⁻¹'
      Set.range (fan.affineToricChartι 𝕜 regular cone) = ∅ := by
  ext point
  constructor
  · intro member
    obtain ⟨source_cone, source_point, source_eq⟩ :=
      (fan.star ray).exists_affineToricChartι_apply_eq 𝕜 star_regular point
    obtain ⟨target_point, target_eq⟩ := member
    have mapped := congrArg (fun morphism : (fan.star ray).affineToricChart 𝕜 source_cone ⟶
      fan.algebraicRealization 𝕜 regular => morphism source_point)
      (fan.affineToricChartι_comp_starOrbitClosureMap 𝕜 regular ray star_regular source_cone)
    simp only [Scheme.Hom.comp_apply, source_eq] at mapped
    have equal_images : fan.affineToricChartι 𝕜 regular (fan.starConeLift ray source_cone)
        (fan.rayFaceChartMap 𝕜 ray source_cone source_point) =
      fan.affineToricChartι 𝕜 regular cone target_point := mapped.symm.trans target_eq.symm
    obtain ⟨overlap_point, left_eq, right_eq⟩ :=
      (fan.affineToricChartι_eq_affineToricChartι_iff 𝕜 regular
        (fan.rayFaceChartMap 𝕜 ray source_cone source_point) target_point).mp equal_images
    apply fan.rayFaceChartMap_not_mem_face_without_ray 𝕜 regular ray source_cone
      ((fan.starConeLift ray source_cone).val ⊓ cone.val)
      (fan.inf_isFaceOf_left (fan.starConeLift ray source_cone).property cone.property)
      (fun in_intersection => absent in_intersection.2) source_point
    exact ⟨overlap_point, left_eq⟩
  · exact False.elim

theorem starOrbitClosureMap_isClosedImmersion (fan : Fan embedding)
    (regular : fan.IsRegular) (ray : fan.Ray) (star_regular : (fan.star ray).IsRegular) :
    IsClosedImmersion (fan.starOrbitClosureMap 𝕜 regular ray star_regular) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (fan.toricChartOpenCover 𝕜 regular)
  intro cone
  by_cases contains : embedding ray.val ∈ cone.val
  · let projected : (fan.star ray).cones :=
      ⟨PointedCone.map (fan.starProjection ray) cone.val, ⟨cone.val, ⟨cone.property, contains⟩, rfl⟩⟩
    have lift_eq : fan.starConeLift ray projected = cone :=
      fan.starConeLift_eq_of_projected ray projected cone contains rfl
    have cartesian := fan.starOrbitClosureMap_lifted_chart_isPullback 𝕜 regular ray star_regular projected
    have local_closed := fan.rayFaceChartMap_isClosedImmersion 𝕜 ray projected
    have transferred : IsClosedImmersion (pullback.snd
        (fan.starOrbitClosureMap 𝕜 regular ray star_regular)
        (fan.affineToricChartι 𝕜 regular (fan.starConeLift ray projected))) := by
      apply (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
        cartesian.flip.isoPullback.hom _).mp
      exact (congrArg (fun morphism => IsClosedImmersion morphism)
        cartesian.flip.isoPullback_hom_snd).mpr local_closed
    rw [lift_eq] at transferred
    change IsClosedImmersion (pullback.snd (fan.starOrbitClosureMap 𝕜 regular ray star_regular)
      (fan.affineToricChartι 𝕜 regular cone))
    exact transferred
  · have empty_preimage := fan.starOrbitClosureMap_preimage_chart_without_ray 𝕜
      regular ray star_regular cone contains
    have empty_pullback : IsEmpty (↑(pullback
        (fan.starOrbitClosureMap 𝕜 regular ray star_regular)
        (fan.affineToricChartι 𝕜 regular cone)) : Type) := by
      apply Scheme.isEmpty_pullback
      apply Set.disjoint_left.mpr
      rintro point ⟨source_point, rfl⟩ member
      exact (Set.ext_iff.mp empty_preimage source_point).mp member
    let := empty_pullback
    change IsClosedImmersion (pullback.snd (fan.starOrbitClosureMap 𝕜 regular ray star_regular)
      (fan.affineToricChartι 𝕜 regular cone))
    infer_instance

theorem completeStarOrbitClosureMap_isClosedImmersion [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) (ray : fan.Ray) :
    IsClosedImmersion (fan.completeStarOrbitClosureMap 𝕜 complete regular ray) :=
  fan.starOrbitClosureMap_isClosedImmersion 𝕜 regular ray (fan.star_isRegular complete regular ray)

end TauCeti.Toric.Fan
