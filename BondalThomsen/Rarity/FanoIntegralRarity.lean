module

public import BondalThomsen.Fan.SmoothFanoIntegralFanClassFiniteness
public import BondalThomsen.Rarity.DerivedOrderingIntegralFanRarity

@[expose] public section

open Filter Real
open scoped Topology

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

theorem smoothProjectiveToricFanoIntegralFanClasses_exp_lower :
    ∀ᶠ dimension : ℕ in atTop,
      exp ((dimension : ℝ) * log dimension - 2 * dimension * log (log dimension) -
        10 * dimension) ≤
          (Nat.card ↥(smoothProjectiveToricFanoIntegralFanClasses 𝕜 dimension) : ℝ) :=
  smoothProjectiveToricFanoIntegralFanClasses_exp_lower_eventually 𝕜
    (smoothProjectiveToricFanoIntegralFanClasses_finite 𝕜)

end BondalThomsen
