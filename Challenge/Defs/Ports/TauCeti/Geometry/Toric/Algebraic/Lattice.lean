module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

@[expose] public section
namespace TauCeti.Toric
open scoped TensorProduct
section Basic
variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
structure IsIntegralLattice (i : N →+ V) : Prop where

  free : Module.Free ℤ N

  finite : Module.Finite ℤ N

  isBaseChange : IsBaseChange ℝ i.toIntLinearMap

end Basic
section Naturality
variable {N N' N'' V V' V'' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
noncomputable def IsIntegralLattice.realCharacter (h : IsIntegralLattice i) :
    (N →+ ℤ) →+ Module.Dual ℝ V :=
  (h.isBaseChange.toDual.comp (addMonoidHomLequivInt ℤ).toLinearMap).toAddMonoidHom

theorem IsIntegralLattice.realCharacter_comp (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (m : N' →+ ℤ) :
    h.realCharacter (m.comp f) = (h'.realCharacter m).comp g :=
  sorry

end Naturality
section Discrete
variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V}
end Discrete
end TauCeti.Toric
end
