module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic
public import Challenge.Defs.Ports.TauCeti.Algebra.Module.Primitive

@[expose] public section
namespace BondalThomsen.ProjectiveBundle
open Finset Module
variable {rows baseDimension columns : ℕ}
abbrev Coordinate (rows baseDimension columns : ℕ) :=
  (Fin rows × Fin baseDimension) ⊕ Fin columns

abbrev Lattice (rows baseDimension columns : ℕ) :=
  Coordinate rows baseDimension columns → ℤ

end BondalThomsen.ProjectiveBundle
end
