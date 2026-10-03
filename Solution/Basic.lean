module

public import BondalThomsen

@[expose] public section

set_option autoImplicit false

open Filter Topology Real

namespace BondalThomsen.Challenge

variable {𝕜 : Type} [Field 𝕜]

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    {embedding : Lattice →+ Ambient}

theorem thm_exceptional_iff_full_strong [IsAlgClosed 𝕜] [CharZero 𝕜]
    (generation : BondalThomsenGeneration 𝕜)
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (projective : ToricSchemeIsProjective 𝕜 fan regular)
    (fano :
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹)) :
    (FaithfulCollection.exceptionalOrdering 𝕜 fan complete regular ↔
      SectionThree.PositiveSheafExtVanishing (fan.algebraicRealization 𝕜 regular)
        (fun member : fan.BondalThomsenClass =>
          fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val)) ∧
    (SectionThree.PositiveSheafExtVanishing (fan.algebraicRealization 𝕜 regular)
        (fun member : fan.BondalThomsenClass =>
          fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val) ↔
      FaithfulCollection.fullStrongOrdering 𝕜 fan complete regular) :=
  theorem_1_2 𝕜 generation fan complete regular projective fano

theorem thm_hypotheses_satisfiable :
    ∃ (Lattice Ambient : Type) (_ : AddCommGroup Lattice) (_ : NormedAddCommGroup Ambient)
      (_ : NormedSpace ℝ Ambient) (_ : FiniteDimensional ℝ Ambient)
      (_ : Module.Free ℤ Lattice) (_ : Module.Finite ℤ Lattice)
      (embedding : Lattice →+ Ambient) (fan : TauCeti.Toric.Fan embedding)
      (complete : fan.IsComplete) (regular : fan.IsRegular),
      ToricSchemeIsProjective 𝕜 fan regular ∧
      letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
      SchemeLineBundleClassAmple ((fan.toricCanonicalLineBundleClass 𝕜 complete regular)⁻¹) :=
  ⟨_, _, _, _, _, _, inferInstance, inferInstance, _, Examples.projectiveLineFan,
    Examples.projectiveLineFan_complete_regular.1, Examples.projectiveLineFan_complete_regular.2,
    Examples.projectiveLineScheme_projective 𝕜, Examples.projectiveLine_inverseCanonical_isAmple 𝕜⟩

theorem thm_rarity :
    ∃ constant : ℝ, 0 < constant ∧
      (∀ᶠ dimension : ℕ in atTop,
        (Nat.card ↥(goodToricFanoClasses 𝕜 dimension) : ℝ) ≤ exp (constant * dimension) ∧
        exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
          constant * dimension) ≤
            (Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) : ℝ)) ∧
      Tendsto (exceptionalToricFanoProportion 𝕜) atTop (𝓝 0) :=
  theorem_1_3_estimates_and_limit 𝕜

theorem thm_toricFano_finite (dimension : ℕ) :
    (smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension).Finite :=
  smoothProjectiveToricFanoIntegralFanClasses_finite 𝕜 dimension

theorem thm_toricFano_eventually_nonempty :
    ∀ᶠ dimension : ℕ in atTop, (smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension).Nonempty :=
  smoothProjectiveToricFanoIntegralFanClasses_eventually_nonempty 𝕜

end BondalThomsen.Challenge

end
