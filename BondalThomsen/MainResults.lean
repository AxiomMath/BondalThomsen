module

public import BondalThomsen.Cited
public import BondalThomsen.Collection.FaithfulCollection
public import BondalThomsen.Classical.Vanishing
public import BondalThomsen.Rarity.ActualSheafOrderingIntegralFanRarity
public import BondalThomsen.Classical.Proofs

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Module Set Filter Real
open TauCeti.AlgebraicGeometry
open BondalThomsen.ToricTransport BondalThomsen.ProjectiveBundle BondalThomsen.SectionThree
open scoped Classical Topology

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BondalThomsen

def goodToricFanoClasses (dimension : ℕ) :
    Set (IntegralFanClass (latticeEmbedding
      (familyRows dimension) (familyWeight dimension) (familyColumns dimension))) :=
  {fanClass | ∃ fan : TauCeti.Toric.Fan (latticeEmbedding
      (familyRows dimension) (familyWeight dimension) (familyColumns dimension)),
    ∃ (complete : fan.IsComplete) (regular : fan.IsRegular),
      integralFanClass fan = fanClass ∧
      SmoothOfRelativeDimension dimension (fan.structureMap 𝕜 regular) ∧
      (∃ Index : Type, Finite Index ∧
        ∃ closedMap : fan.algebraicRealization 𝕜 regular ⟶
            Proj (MvPolynomial.homogeneousSubmodule Index 𝕜),
          IsClosedImmersion closedMap ∧
            closedMap ≫ polynomialProjStructureMap 𝕜 Index = fan.structureMap 𝕜 regular) ∧
      (letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete);
        SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹)) ∧
      FaithfulCollection.fullStrongOrdering 𝕜 fan complete regular}

noncomputable def exceptionalToricFanoProportion (dimension : ℕ) : ℝ :=
  (Nat.card ↥(goodToricFanoClasses 𝕜 dimension) : ℝ) /
    Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension)

theorem smoothProjectiveToricFanoIntegralFanClasses_card_eventually_pos :
    ∀ᶠ dimension : ℕ in atTop,
      0 < Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) := by
  filter_upwards [smoothProjectiveToricFanoIntegralFanClasses_exp_lower 𝕜] with dimension lower
  have positive : (0 : ℝ) <
      Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) :=
    (exp_pos _).trans_le lower
  exact_mod_cast positive

theorem smoothProjectiveToricFanoIntegralFanClasses_eventually_nonempty :
    ∀ᶠ dimension : ℕ in atTop,
      (smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension).Nonempty := by
  filter_upwards [smoothProjectiveToricFanoIntegralFanClasses_card_eventually_pos 𝕜]
    with dimension positive
  obtain ⟨member⟩ := (Nat.card_pos_iff.mp positive).1
  exact ⟨member.val, member.property⟩

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    {embedding : Lattice →+ Ambient}

theorem theorem_1_2 [IsAlgClosed 𝕜] [CharZero 𝕜] (generation : BondalThomsenGeneration 𝕜)
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (projective : ToricSchemeIsProjective 𝕜 fan regular)
    (fano :
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹)) :
    (FaithfulCollection.exceptionalOrdering 𝕜 fan complete regular ↔
      PositiveSheafExtVanishing (fan.algebraicRealization 𝕜 regular)
        (fun member : fan.BondalThomsenClass =>
          fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val)) ∧
    (PositiveSheafExtVanishing (fan.algebraicRealization 𝕜 regular)
        (fun member : fan.BondalThomsenClass =>
          fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val) ↔
      FaithfulCollection.fullStrongOrdering 𝕜 fan complete regular) := by
  let : HasDerivedCategory (fan.algebraicRealization 𝕜 regular).Modules :=
    HasDerivedCategory.standard _
  let : (fan.algebraicRealization 𝕜 regular).Over (Spec (CommRingCat.of 𝕜)) :=
    ⟨fan.structureMap 𝕜 regular⟩
  let extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop :=
    fun _left _right relation => relation.IsMoriExtremal 𝕜 complete regular
  have support := toricFanoExtremalSupport_of_actualCanonicalInverse_isAmple 𝕜
    fan complete regular (Module.finBasis ℤ Lattice) extremal fano
    (extremalDropOneIncidence_proved 𝕜 fan complete regular projective)
  have equivalences := fan.actualDerived_exceptional_iff_strong_of_kodaira_nef_inputs 𝕜
    complete regular (Module.finrank ℤ Lattice)
    (SchemeLineBundleClassIsNef (baseField := 𝕜)) extremal
    (primitiveNefCriterion_proved 𝕜 fan complete regular projective) support
    (nefPositiveVanishing_of_demazure 𝕜 (demazureVanishing_proved 𝕜) fan complete regular)
  have generation := generation Lattice Ambient embedding fan complete regular
  exact ⟨equivalences.1, equivalences.2.trans
    (FaithfulCollection.fullStrongOrdering_iff_of_generation 𝕜
      fan complete regular generation).symm⟩

theorem theorem_1_3_estimates_and_limit :
    ∃ constant : ℝ, 0 < constant ∧
      (∀ᶠ dimension : ℕ in atTop,
        (Nat.card ↥(goodToricFanoClasses 𝕜 dimension) : ℝ) ≤ exp (constant * dimension) ∧
        exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
          constant * dimension) ≤
            (Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) : ℝ)) ∧
      Tendsto (exceptionalToricFanoProportion 𝕜) atTop (𝓝 0) := by
  classical
  choose fans complete regular realized smooth projective ample ordering using
    (fun dimension (fanClass : goodToricFanoClasses 𝕜 dimension) => fanClass.property)
  have counting := theorem_1_3_of_actualSheafExt_backward_presentations_and_geometricNef_inputs 𝕜
    (goodToricFanoClasses 𝕜) fans complete regular realized
    (fun dimension fanClass _left _right relation =>
      relation.IsMoriExtremal 𝕜 (complete dimension fanClass) (regular dimension fanClass))
    ample
    (fun dimension fanClass => extremalDropOneIncidence_proved 𝕜
      (fans dimension fanClass) (complete dimension fanClass) (regular dimension fanClass)
      (projective dimension fanClass))
    (fun dimension fanClass => necessaryNefSupport_proved 𝕜
      (fans dimension fanClass) (complete dimension fanClass) (regular dimension fanClass) dimension)
    (fun dimension fanClass => toricNefMoriCriterion_proved 𝕜 _ _ _ (fans dimension fanClass)
      (complete dimension fanClass) (regular dimension fanClass) (projective dimension fanClass))
    (fun dimension fanClass => FaithfulCollection.fullStrongOrdering_sheafBackwardExt 𝕜
      (fans dimension fanClass) (complete dimension fanClass) (regular dimension fanClass)
      (ordering dimension fanClass))
  exact counting.2

end BondalThomsen
