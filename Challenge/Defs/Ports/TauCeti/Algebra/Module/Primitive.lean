module

public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.RingTheory.Int.Basic

@[expose] public section
namespace TauCeti
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
abbrev IsPrimitive (v : M) : Prop := Module.IsUnimodular ℤ v

end TauCeti
namespace Module.Basis
variable {ι M : Type*} [AddCommGroup M] [Module ℤ M]
theorem isPrimitive (b : Module.Basis ι ℤ M) (j : ι) : TauCeti.IsPrimitive (b j) :=
  sorry

end Module.Basis
namespace LinearEquiv
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
end LinearEquiv
namespace TauCeti
variable {M : Type*} [AddCommGroup M] [Module ℤ M]
end TauCeti
end
