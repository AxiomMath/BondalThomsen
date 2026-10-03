module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
public import Challenge.Defs.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Basic
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.LocalEquations
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import Challenge.Defs.Ports.TauCeti.CategoryTheory.Sites.Units

@[expose] public section
open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
namespace TauCeti
namespace AlgebraicGeometry
universe u
noncomputable section
namespace Scheme
variable {X : Scheme.{u}} [IsIntegral X]
namespace CartierDivisor
def sections (D : CartierDivisor X) (U : X.Opens) :
    Submodule Γ(X, U) Γ(rationalFunctions X, U) where
  carrier := {s | ∀ (x : X) (hx : x ∈ U) (f : X.functionFieldˣ), D.IsLocalEquationAt x f →
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    (f : X.functionField) * rationalFunctionsEquiv U s ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range}
  zero_mem' := by
    intro x hx f _
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_zero, mul_zero]
    exact Subring.zero_mem _
  add_mem' := by
    intro s t hs ht x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_add, mul_add]
    exact Subring.add_mem _ (hs x hx f hf) (ht x hx f hf)
  smul_mem' := by
    intro r s hs x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_smul, ← germ_smul_functionField hx, Algebra.smul_def, mul_left_comm]
    exact Subring.mul_mem _ (RingHom.mem_range_self _ _) (hs x hx f hf)

lemma sections_map {D : CartierDivisor X} {U V : X.Opens} (i : V ⟶ U)
    {s : Γ(rationalFunctions X, U)} (hs : s ∈ D.sections U) :
    (rationalFunctions X).presheaf.map i.op s ∈ D.sections V :=
  sorry

def submodule (D : CartierDivisor X) : (rationalFunctions X).Submodule where
  obj U := D.sections U.unop
  map i := fun {_} hs ↦ sections_map i.unop hs
  isSheaf {U} s hs := by
    intro x hx f hf
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U.unop := ⟨⟨x, hx⟩⟩
    have hi' : (rationalFunctions X).presheaf.map i.op s ∈ D.sections V := hi
    rw [← rationalFunctionsEquiv_map i s]
    exact hi' x hxV f hf

def sheaf (D : CartierDivisor X) : X.Modules :=
  D.submodule.toSheafOfModules

theorem isInvertible_sheaf (D : CartierDivisor X) : SheafOfModules.isInvertible X D.sheaf :=
  sorry

def toInvertibleSheaf (D : CartierDivisor X) : InvertibleSheaf X :=
  ⟨D.sheaf, D.isInvertible_sheaf⟩

end CartierDivisor
end Scheme
end
end AlgebraicGeometry
end TauCeti
end
