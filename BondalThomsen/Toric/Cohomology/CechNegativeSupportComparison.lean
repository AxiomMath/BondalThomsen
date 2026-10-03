module

public import BondalThomsen.Toric.Cohomology.CechWeightDecomposition
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TauCeti.Toric
open scoped Classical Simplicial

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ToricCechNegativeSupportComparison

variable {Ray : Type*} {Chart : Type}

def tupleForbidden (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : Fin (degree + 1) → Chart) : Prop :=
  ∃ ray, negative ray ∧ ∀ column, incidence ray (tuple column)

theorem tupleForbidden_precomp (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Chart)
    (forbidden : tupleForbidden incidence negative next tuple) :
    tupleForbidden incidence negative degree (tuple ∘ selection) := by
  obtain ⟨ray, negativeRay, contains⟩ := forbidden
  exact ⟨ray, negativeRay, fun column => contains (selection column)⟩

def negativeChartComplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    PreAbstractSimplicialComplex Chart where
  faces := {face | face.Nonempty ∧ ∃ ray, negative ray ∧
    ∀ chart ∈ face, incidence ray chart}
  isRelLowerSet_faces := by
    intro face member
    refine ⟨member.1, ?_⟩
    intro smaller subset nonempty
    obtain ⟨ray, negativeRay, contains⟩ := member.2
    exact ⟨nonempty, ray, negativeRay, fun chart present => contains chart (subset present)⟩

theorem tupleForbidden_iff_face (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) (tuple : Fin (degree + 1) → Chart) :
    tupleForbidden incidence negative degree tuple ↔
      Finset.univ.image tuple ∈ negativeChartComplex incidence negative := by
  constructor
  · rintro ⟨ray, negativeRay, contains⟩
    refine ⟨⟨tuple 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩,
      ray, negativeRay, ?_⟩
    intro chart present
    obtain ⟨column, _, rfl⟩ := Finset.mem_image.mp present
    exact contains column
  · rintro ⟨_, ray, negativeRay, contains⟩
    exact ⟨ray, negativeRay, fun column =>
      contains (tuple column) (Finset.mem_image.mpr ⟨column, Finset.mem_univ _, rfl⟩)⟩

def relativeScalarCoefficient (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : Fin (degree + 1) → Chart) : AddSubgroup 𝕜 where
  carrier := {scalar | tupleForbidden incidence negative degree tuple → scalar = 0}
  zero_mem' := fun _ => rfl
  add_mem' := fun first second forbidden => by rw [first forbidden, second forbidden, zero_add]
  neg_mem' := fun scalar forbidden => by rw [scalar forbidden, neg_zero]

noncomputable def relativeCoefficient (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) (tuple : Fin (degree + 1) → Chart) : AddCommGrpCat :=
  AddCommGrpCat.of (relativeScalarCoefficient 𝕜 incidence negative degree tuple)

noncomputable def relativeDegree (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) : AddCommGrpCat :=
  ∏ᶜ (relativeCoefficient 𝕜 incidence negative degree)

def relativeScalarRestriction (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {degree next : ℕ} (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Chart) :
    relativeScalarCoefficient 𝕜 incidence negative degree (tuple ∘ selection) →+
      relativeScalarCoefficient 𝕜 incidence negative next tuple where
  toFun scalar := ⟨scalar.val, fun forbidden => scalar.property
    (tupleForbidden_precomp incidence negative selection tuple forbidden)⟩
  map_zero' := rfl
  map_add' _first _second := rfl

noncomputable def relativeTupleMap (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {degree next : ℕ} (selection : Fin (degree + 1) → Fin (next + 1)) :
    relativeDegree 𝕜 incidence negative degree ⟶ relativeDegree 𝕜 incidence negative next :=
  Limits.Pi.lift (fun tuple =>
    Limits.Pi.π (relativeCoefficient 𝕜 incidence negative degree) (tuple ∘ selection) ≫
      AddCommGrpCat.ofHom (relativeScalarRestriction 𝕜 incidence negative selection tuple))

noncomputable def relativeCosimplicial (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) : CosimplicialObject AddCommGrpCat where
  obj simplex := relativeDegree 𝕜 incidence negative simplex.len
  map selection := relativeTupleMap 𝕜 incidence negative selection.toOrderHom
  map_id simplex := by
    apply Limits.Pi.hom_ext
    intro tuple
    simp only [relativeTupleMap, Limits.Pi.lift_comp_π, Category.id_comp]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl
  map_comp first second := by
    apply Limits.Pi.hom_ext
    intro tuple
    simp only [relativeTupleMap, Category.assoc, Limits.Pi.lift_comp_π]
    rw [← Category.assoc, Limits.Pi.lift_comp_π]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl

noncomputable def relativeComplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    CochainComplex AddCommGrpCat ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (relativeCosimplicial 𝕜 incidence negative)

theorem relativeComplex_d (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) :
    (relativeComplex 𝕜 incidence negative).d degree (degree + 1) =
      ∑ deleted : Fin (degree + 2), (-1 : ℤ) ^ deleted.val •
        relativeTupleMap 𝕜 incidence negative deleted.succAbove := by
  simp only [relativeComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    CochainComplex.of_d]
  rfl

end BondalThomsen.ToricCechNegativeSupportComparison

namespace TauCeti.Toric.Fan

open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricPrimitiveWeightZeroComplex

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

def cechRayChartIncidence (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ray : fan.Ray) (chart : Fin (Nat.card fan.cones)) : Prop :=
  embedding ray.val ∈ (fan.divisorLocalCone 𝕜 complete regular chart).val

def cechCharacterNegativeRay (fan : Fan embedding) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (ray : fan.Ray) : Prop :=
  divisor ray + character ray.val < 0

theorem primitiveCechCone_mem_iff_charts (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) (point : Ambient) :
    point ∈ (fan.primitiveCechCone 𝕜 complete regular degree tuple).val ↔
      ∀ column, point ∈ (fan.divisorLocalCone 𝕜 complete regular (tuple column)).val := by
  constructor
  · intro contains column
    exact fan.primitiveCechCone_le_chart 𝕜 complete regular degree tuple column contains
  · induction degree with
    | zero =>
      intro contains
      exact contains 0
    | succ degree induction =>
      intro contains
      exact ⟨contains 0, induction (tuple ∘ Fin.succ) (fun column => contains column.succ)⟩

theorem cechCharacterTupleAvailable_iff_not_forbidden (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.cechCharacterTupleAvailable 𝕜 complete regular divisor character degree tuple ↔
      ¬ tupleForbidden (fan.cechRayChartIncidence 𝕜 complete regular)
        (fan.cechCharacterNegativeRay divisor character) degree tuple := by
  rw [fan.cechCharacterTupleAvailable_iff_avoids_negative 𝕜]
  constructor
  · intro avoids
    rintro ⟨ray, negative, contains⟩
    exact avoids ray negative
      ((fan.primitiveCechCone_mem_iff_charts 𝕜 complete regular degree tuple _).mpr contains)
  · intro unforbidden ray negative contains
    exact unforbidden ⟨ray, negative,
      (fan.primitiveCechCone_mem_iff_charts 𝕜 complete regular degree tuple _).mp contains⟩

noncomputable def cechNegativeSupportComplex (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) : CochainComplex AddCommGrpCat ℕ :=
  relativeComplex 𝕜 (fan.cechRayChartIncidence 𝕜 complete regular)
    (fan.cechCharacterNegativeRay divisor character)

noncomputable def cechCharacterRelativeCoefficientEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Fin (Nat.card fan.cones)) :
    fan.primitiveCechScalarCoefficient 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) degree tuple ≃+
      relativeScalarCoefficient 𝕜 (fan.cechRayChartIncidence 𝕜 complete regular)
        (fan.cechCharacterNegativeRay divisor character) degree tuple where
  toFun scalar := ⟨scalar.val, fun forbidden => scalar.property (fun available =>
    (fan.cechCharacterTupleAvailable_iff_not_forbidden 𝕜 complete regular divisor character
      degree tuple).mp available forbidden)⟩
  invFun scalar := ⟨scalar.val, fun unavailable => scalar.property (by
    by_contra unforbidden
    exact unavailable ((fan.cechCharacterTupleAvailable_iff_not_forbidden 𝕜 complete regular
      divisor character degree tuple).mpr unforbidden))⟩
  left_inv _scalar := rfl
  right_inv _scalar := rfl
  map_add' _first _second := rfl

noncomputable def cechCharacterRelativeDegreeIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) :
    fan.primitiveComplementDegree 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) degree ≅
      relativeDegree 𝕜 (fan.cechRayChartIncidence 𝕜 complete regular)
        (fan.cechCharacterNegativeRay divisor character) degree :=
  Limits.Pi.mapIso (fun tuple => (fan.cechCharacterRelativeCoefficientEquiv 𝕜 complete regular
    divisor character degree tuple).toAddCommGrpIso)

theorem cechCharacterRelativeDegreeIso_coface (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) (degree : ℕ) (deleted : Fin (degree + 2)) :
    (fan.cechCharacterRelativeDegreeIso 𝕜 complete regular divisor character degree).hom ≫
        relativeTupleMap 𝕜 (fan.cechRayChartIncidence 𝕜 complete regular)
          (fan.cechCharacterNegativeRay divisor character) deleted.succAbove =
      fan.primitiveComplementCoface 𝕜 complete regular
          (divisor + fan.principalRayDivisor character) degree deleted ≫
        (fan.cechCharacterRelativeDegreeIso 𝕜 complete regular divisor character (degree + 1)).hom := by
  apply Limits.Pi.hom_ext
  intro tuple
  simp only [Category.assoc, relativeTupleMap, primitiveComplementCoface,
    Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc, cechCharacterRelativeDegreeIso,
    Limits.Pi.mapIso_hom_π, Limits.Pi.mapIso_hom_π_assoc]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro cochain
  rfl

noncomputable def cechCharacterNegativeSupportIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) :
    fan.primitiveComplementComplex 𝕜 complete regular (divisor + fan.principalRayDivisor character) ≅
      fan.cechNegativeSupportComplex 𝕜 complete regular divisor character :=
  HomologicalComplex.Hom.isoOfComponents
    (fan.cechCharacterRelativeDegreeIso 𝕜 complete regular divisor character)
    (fun degree next related => by
      change degree + 1 = next at related
      subst next
      rw [show (fan.cechNegativeSupportComplex 𝕜 complete regular divisor character).d
          degree (degree + 1) = _ from relativeComplex_d 𝕜 _ _ degree]
      rw [show (fan.primitiveComplementComplex 𝕜 complete regular
          (divisor + fan.principalRayDivisor character)).d degree (degree + 1) =
          fan.primitiveComplementDifferential 𝕜 complete regular
            (divisor + fan.principalRayDivisor character) degree from CochainComplex.of_d _ _ degree]
      simp only [primitiveComplementDifferential, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
      apply Finset.sum_congr rfl
      intro deleted _present
      exact congrArg (fun morphism => (-1 : ℤ) ^ deleted.val • morphism)
        (fan.cechCharacterRelativeDegreeIso_coface 𝕜 complete regular divisor character degree deleted))

end TauCeti.Toric.Fan
