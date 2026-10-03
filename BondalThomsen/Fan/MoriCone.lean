module

public import BondalThomsen.LineBundle.PicardGeometricNef
public import BondalThomsen.Toric.Divisor.PicardEquivalence
public import BondalThomsen.Fan.PrimitiveDivisorPairing
public import BondalThomsen.Toric.RankOne.CurveDegreeNormalization
public import Mathlib.Analysis.Convex.Cone.Closure
public import Mathlib.Geometry.Convex.Cone.Face.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable section

variable {baseField : Type} [Field baseField] {scheme : Scheme.{0}}
    [scheme.Over (Spec (CommRingCat.of baseField))]

def integralCurvePicardDegree (curve : IntegralCurve baseField scheme) :
    Additive (LineBundleClass scheme) →+ ℤ where
  toFun := fun bundleClass => LineBundleClass.lift
    (fun bundle => curve.lineBundleDegree ((Scheme.Modules.pullback curve.ι).obj bundle.obj))
    (by
      intro first second isomorphic
      exact curve.lineBundleDegree_eq_of_iso
        ((Scheme.Modules.pullback curve.ι).mapIso isomorphic.some)) bundleClass.toMul
  map_zero' := by
    change LineBundleClass.lift _ _ (LineBundleClass.mk (InvertibleSheaf.trivial _)) = 0
    rw [LineBundleClass.lift_mk]
    let comparison :
        Scheme.Modules.tensor (InvertibleSheaf.trivial scheme).obj
            (InvertibleSheaf.trivial scheme).obj ≅ (InvertibleSheaf.trivial scheme).obj :=
      (SheafOfModules.isInvertible _).ι.mapIso
        (InvertibleSheaf.tensorTrivialLeftIso (InvertibleSheaf.trivial _))
    have additive := curve.lineBundleDegree_pullback_tensor
      (InvertibleSheaf.trivial scheme).obj (InvertibleSheaf.trivial scheme).obj
    rw [curve.lineBundleDegree_eq_of_iso
      ((Scheme.Modules.pullback curve.ι).mapIso comparison)] at additive
    omega
  map_add' := by
    intro firstClass secondClass
    obtain ⟨first, firstEquality⟩ := LineBundleClass.mk_surjective firstClass.toMul
    obtain ⟨second, secondEquality⟩ := LineBundleClass.mk_surjective secondClass.toMul
    change LineBundleClass.lift _ _ (firstClass.toMul * secondClass.toMul) =
      LineBundleClass.lift _ _ firstClass.toMul + LineBundleClass.lift _ _ secondClass.toMul
    rw [← firstEquality, ← secondEquality, ← LineBundleClass.mk_tensorProduct]
    simp only [LineBundleClass.lift_mk]
    exact curve.lineBundleDegree_pullback_tensor first.obj second.obj

@[simp] theorem integralCurvePicardDegree_mk (curve : IntegralCurve baseField scheme)
    (bundle : InvertibleSheaf scheme) :
    integralCurvePicardDegree curve (Additive.ofMul (LineBundleClass.mk bundle)) =
      curve.lineBundleDegree ((Scheme.Modules.pullback curve.ι).obj bundle.obj) := by
  simp only [integralCurvePicardDegree, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  change LineBundleClass.lift _ _ (LineBundleClass.mk bundle) = _
  exact LineBundleClass.lift_mk bundle

abbrev NumericalCurveFunctionals (scheme : Scheme.{0}) :=
  Additive (LineBundleClass scheme) → ℝ

def integralCurveNumericalFunctional (curve : IntegralCurve baseField scheme) :
    NumericalCurveFunctionals scheme :=
  fun bundleClass => (integralCurvePicardDegree curve bundleClass : ℝ)

def numericalCurveSpace (baseField : Type) [Field baseField] (scheme : Scheme.{0})
    [scheme.Over (Spec (CommRingCat.of baseField))] :
    Submodule ℝ (NumericalCurveFunctionals scheme) :=
  Submodule.span ℝ (Set.range (integralCurveNumericalFunctional (baseField := baseField)
    (scheme := scheme)))

theorem numericalCurveSpace_isAdditive
    (numericalClass : numericalCurveSpace baseField scheme) :
    numericalClass.val 0 = 0 ∧
      ∀ first second : Additive (LineBundleClass scheme),
        numericalClass.val (first + second) =
          numericalClass.val first + numericalClass.val second := by
  obtain ⟨functional, membership⟩ := numericalClass
  change functional 0 = 0 ∧ ∀ first second, functional (first + second) =
    functional first + functional second
  induction membership using Submodule.span_induction with
  | mem functional inGenerators =>
      obtain ⟨curve, rfl⟩ := inGenerators
      constructor
      · simp [integralCurveNumericalFunctional]
      · intro first second
        simp [integralCurveNumericalFunctional, map_add]
  | zero =>
      constructor
      · rfl
      · intro first second
        simp
  | add first second firstMembership secondMembership firstAdditive secondAdditive =>
      constructor
      · change first 0 + second 0 = 0
        rw [firstAdditive.1, secondAdditive.1, add_zero]
      · intro firstClass secondClass
        change first (firstClass + secondClass) + second (firstClass + secondClass) = _
        rw [firstAdditive.2, secondAdditive.2]
        change _ = (first firstClass + second firstClass) +
          (first secondClass + second secondClass)
        abel
  | smul scalar functional membership additive =>
      constructor
      · change scalar * functional 0 = 0
        rw [additive.1, mul_zero]
      · intro first second
        change scalar * functional (first + second) =
          scalar * functional first + scalar * functional second
        rw [additive.2, mul_add]

def integralCurveNumericalClass (curve : IntegralCurve baseField scheme) :
    numericalCurveSpace baseField scheme :=
  ⟨integralCurveNumericalFunctional curve, Submodule.subset_span ⟨curve, rfl⟩⟩

@[simp] theorem integralCurveNumericalClass_apply (curve : IntegralCurve baseField scheme)
    (bundleClass : Additive (LineBundleClass scheme)) :
    (integralCurveNumericalClass curve).val bundleClass =
      (integralCurvePicardDegree curve bundleClass : ℝ) := rfl

def moriCone (baseField : Type) [Field baseField] (scheme : Scheme.{0})
    [scheme.Over (Spec (CommRingCat.of baseField))] :
    PointedCone ℝ (numericalCurveSpace baseField scheme) :=
  (PointedCone.hull ℝ (Set.range (integralCurveNumericalClass (baseField := baseField)
    (scheme := scheme)))).closure

theorem integralCurveNumericalClass_mem_moriCone (curve : IntegralCurve baseField scheme) :
    integralCurveNumericalClass curve ∈ moriCone baseField scheme :=
  subset_closure (PointedCone.subset_hull ⟨curve, rfl⟩)

def IsExtremalMoriClass (numericalClass : numericalCurveSpace baseField scheme) : Prop :=
  numericalClass ≠ 0 ∧
    (PointedCone.hull ℝ {numericalClass}).IsFaceOf (moriCone baseField scheme)

theorem IsExtremalMoriClass.mem_moriCone
    {numericalClass : numericalCurveSpace baseField scheme}
    (extremal : IsExtremalMoriClass numericalClass) :
    numericalClass ∈ moriCone baseField scheme :=
  extremal.2.le (PointedCone.subset_hull (Set.mem_singleton numericalClass))

theorem schemeLineBundleClassIsNef_iff_curveDegree_nonnegative
    (bundleClass : LineBundleClass scheme) :
    SchemeLineBundleClassIsNef (baseField := baseField) bundleClass ↔
      ∀ curve : IntegralCurve baseField scheme,
        0 ≤ (integralCurveNumericalClass curve).val (Additive.ofMul bundleClass) := by
  obtain ⟨bundle, rfl⟩ := LineBundleClass.mk_surjective bundleClass
  rw [schemeLineBundleClassIsNef_mk_iff]
  change (∀ curve : IntegralCurve baseField scheme, 0 ≤
    curve.lineBundleDegree ((Scheme.Modules.pullback curve.ι).obj bundle.obj)) ↔ _
  simp only [integralCurveNumericalClass_apply, integralCurvePicardDegree_mk,
    Int.cast_nonneg_iff]

theorem schemeLineBundleClassIsNef_iff_moriCone_nonnegative
    (bundleClass : LineBundleClass scheme) :
    SchemeLineBundleClassIsNef (baseField := baseField) bundleClass ↔
      ∀ numericalClass ∈ moriCone baseField scheme,
        0 ≤ numericalClass.val (Additive.ofMul bundleClass) := by
  rw [schemeLineBundleClassIsNef_iff_curveDegree_nonnegative]
  constructor
  · intro curveNonnegative
    let nonnegativeCone : PointedCone ℝ (numericalCurveSpace baseField scheme) :=
      { carrier := {numericalClass | 0 ≤ numericalClass.val (Additive.ofMul bundleClass)}
        zero_mem' := by simp
        add_mem' := by
          intro first second firstNonnegative secondNonnegative
          change 0 ≤ first.val (Additive.ofMul bundleClass) +
            second.val (Additive.ofMul bundleClass)
          exact add_nonneg firstNonnegative secondNonnegative
        smul_mem' := by
          intro scalar numericalClass nonnegative
          change 0 ≤ scalar.val * numericalClass.val (Additive.ofMul bundleClass)
          exact mul_nonneg scalar.property nonnegative }
    have hullContained :
        PointedCone.hull ℝ (Set.range (integralCurveNumericalClass
          (baseField := baseField) (scheme := scheme))) ≤ nonnegativeCone := by
      apply Submodule.span_le.mpr
      rintro numericalClass ⟨curve, rfl⟩
      exact curveNonnegative curve
    have closed : IsClosed (nonnegativeCone : Set (numericalCurveSpace baseField scheme)) :=
      isClosed_Ici.preimage ((continuous_apply (Additive.ofMul bundleClass)).comp
        continuous_subtype_val)
    intro numericalClass inMoriCone
    exact (closed.closure_subset_iff.mpr hullContained) inMoriCone
  · intro allNonnegative curve
    exact allNonnegative (integralCurveNumericalClass curve)
      (integralCurveNumericalClass_mem_moriCone curve)

end

end BondalThomsen

namespace TauCeti.Toric.Fan

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry Module

variable {Lattice : Type} {Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}
    {fan : Fan embedding} {left right : Finset fan.Ray}

noncomputable def PrimitiveLatticeRelation.schemePicardPairing
    (relation : PrimitiveLatticeRelation fan left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    Additive (LineBundleClass (fan.algebraicRealization 𝕜 regular)) →+ ℤ :=
  relation.classPairing.comp (fan.invariantDivisorPicardEquiv 𝕜 complete regular).symm.toAddMonoidHom

@[simp] theorem PrimitiveLatticeRelation.schemePicardPairing_realization
    (relation : PrimitiveLatticeRelation fan left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisorClass : fan.InvariantRayDivisorClass) :
    relation.schemePicardPairing 𝕜 complete regular
        (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass) =
      relation.classPairing divisorClass := by
  change relation.classPairing ((fan.invariantDivisorPicardEquiv 𝕜 complete regular).symm
    ((fan.invariantDivisorPicardEquiv 𝕜 complete regular) divisorClass)) = _
  rw [AddEquiv.symm_apply_apply]

noncomputable def PrimitiveLatticeRelation.numericalFunctional
    (relation : PrimitiveLatticeRelation fan left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    BondalThomsen.NumericalCurveFunctionals (fan.algebraicRealization 𝕜 regular) :=
  fun bundleClass => (relation.schemePicardPairing 𝕜 complete regular bundleClass : ℝ)

@[simp] theorem PrimitiveLatticeRelation.numericalFunctional_realization
    (relation : PrimitiveLatticeRelation fan left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisorClass : fan.InvariantRayDivisorClass) :
    relation.numericalFunctional 𝕜 complete regular
        (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass) =
      (relation.classPairing divisorClass : ℝ) := by
  simp [PrimitiveLatticeRelation.numericalFunctional]

theorem PrimitiveLatticeRelation.schemePicardPairing_leftRay
    (relation : PrimitiveLatticeRelation fan left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (distinguished : left) :
    relation.schemePicardPairing 𝕜 complete regular
        (fan.invariantDivisorPicardRealization 𝕜 complete regular
          (fan.invariantRayDivisorClass (Finsupp.single distinguished.val 1))) = 1 := by
  classical
  rw [relation.schemePicardPairing_realization 𝕜, relation.classPairing_mk]
  unfold PrimitiveLatticeRelation.divisorIntersection
  have rightZero : ∀ ray : right,
      (Finsupp.single distinguished.val (1 : ℤ) : fan.InvariantRayDivisor) ray.val = 0 := by
    intro ray
    have different : distinguished.val ≠ ray.val := by
      intro same
      exact (Finset.disjoint_left.mp relation.disjoint) distinguished.property
        (same.symm ▸ ray.property)
    simp [different]
  simp only [rightZero, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [Finset.sum_eq_single distinguished]
  · simp
  · intro ray member different
    apply Finsupp.single_eq_of_ne
    exact fun same => different (Subtype.ext same)
  · intro absent
    exact False.elim (absent (Finset.mem_univ distinguished))

theorem PrimitiveLatticeRelation.numericalFunctional_ne_zero
    (relation : PrimitiveLatticeRelation fan left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular) :
    relation.numericalFunctional 𝕜 complete regular ≠ 0 := by
  classical
  obtain ⟨ray, member⟩ := relation.primitive_collection.1
  intro zero
  have evaluated := congrFun zero (fan.invariantDivisorPicardRealization 𝕜 complete regular
    (fan.invariantRayDivisorClass (Finsupp.single ray 1)))
  change (relation.schemePicardPairing 𝕜 complete regular
    (fan.invariantDivisorPicardRealization 𝕜 complete regular
      (fan.invariantRayDivisorClass (Finsupp.single ray 1))) : ℝ) = 0 at evaluated
  rw [relation.schemePicardPairing_leftRay 𝕜 complete regular ⟨ray, member⟩] at evaluated
  norm_num at evaluated

def PrimitiveLatticeRelation.IsMoriExtremal
    (relation : PrimitiveLatticeRelation fan left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular) : Prop :=
  letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨fan.structureMap 𝕜 regular⟩
  ∃ numericalClass : BondalThomsen.numericalCurveSpace 𝕜 (fan.algebraicRealization 𝕜 regular),
    numericalClass.val = relation.numericalFunctional 𝕜 complete regular ∧
      BondalThomsen.IsExtremalMoriClass numericalClass

theorem PrimitiveLatticeRelation.schemePicardPairing_nonnegative_of_isMoriExtremal
    (relation : PrimitiveLatticeRelation fan left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (extremal : relation.IsMoriExtremal 𝕜 complete regular)
    (bundleClass : LineBundleClass (fan.algebraicRealization 𝕜 regular)) :
    letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
      ⟨fan.structureMap 𝕜 regular⟩
    BondalThomsen.SchemeLineBundleClassIsNef (baseField := 𝕜) bundleClass →
      0 ≤ relation.schemePicardPairing 𝕜 complete regular (Additive.ofMul bundleClass) := by
  let : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨fan.structureMap 𝕜 regular⟩
  intro nef
  obtain ⟨numericalClass, coefficients, extremalClass⟩ := extremal
  have nonnegative :=
    (BondalThomsen.schemeLineBundleClassIsNef_iff_moriCone_nonnegative bundleClass).mp nef
      numericalClass extremalClass.mem_moriCone
  rw [coefficients] at nonnegative
  change 0 ≤ (relation.schemePicardPairing 𝕜 complete regular
    (Additive.ofMul bundleClass) : ℝ) at nonnegative
  exact_mod_cast nonnegative

theorem PrimitiveLatticeRelation.classPairing_nonnegative_of_isMoriExtremal
    (relation : PrimitiveLatticeRelation fan left right)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (extremal : relation.IsMoriExtremal 𝕜 complete regular)
    (divisorClass : fan.InvariantRayDivisorClass) :
    letI : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
      ⟨fan.structureMap 𝕜 regular⟩
    BondalThomsen.SchemeLineBundleClassIsNef (baseField := 𝕜)
        (Additive.toMul (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass)) →
      0 ≤ relation.classPairing divisorClass := by
  let : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨fan.structureMap 𝕜 regular⟩
  intro nef
  have nonnegative := relation.schemePicardPairing_nonnegative_of_isMoriExtremal 𝕜
    complete regular extremal _ nef
  change 0 ≤ relation.schemePicardPairing 𝕜 complete regular
    (fan.invariantDivisorPicardRealization 𝕜 complete regular divisorClass) at nonnegative
  simpa only [relation.schemePicardPairing_realization 𝕜] using nonnegative

end TauCeti.Toric.Fan
