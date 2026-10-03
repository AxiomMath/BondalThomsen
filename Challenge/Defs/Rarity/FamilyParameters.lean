module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic

@[expose] public section
namespace BondalThomsen
open Real Filter
open scoped Topology
noncomputable def familyWeight (dimension : ℕ) : ℕ := ⌊log dimension⌋₊

noncomputable def familyRows (dimension : ℕ) : ℕ := dimension / (familyWeight dimension + 1)

noncomputable def familyColumns (dimension : ℕ) : ℕ :=
  dimension - familyRows dimension * familyWeight dimension

end BondalThomsen
end
