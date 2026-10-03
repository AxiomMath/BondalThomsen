module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Basic
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import Challenge.Defs.Ports.TauCeti.CategoryTheory.Sites.Units

@[expose] public section
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite
namespace TauCeti
namespace AlgebraicGeometry
universe u
noncomputable section
namespace Scheme
variable (X : Scheme.{u}) [IsIntegral X]
variable {X} in
def CartierDivisor.IsLocalEquationAt (D : CartierDivisor X) (x : X) (f : X.functionFieldˣ) : Prop :=
  ∃ (V : X.Opens) (hx : x ∈ V),
    haveI : Nonempty V := ⟨⟨x, hx⟩⟩
    rationalUnitClass X V (Additive.ofMul f) = D |_ V

namespace CartierDivisor
variable {X}
end CartierDivisor
end Scheme
end
end AlgebraicGeometry
end TauCeti
end
