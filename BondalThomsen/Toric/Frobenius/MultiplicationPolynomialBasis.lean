module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

namespace BondalThomsen

variable {Index : Type*} [Finite Index] (degree : ℕ) [NeZero degree]

noncomputable def multiplicationExponentEquiv :
    (Index →₀ ℕ) ≃ (Index → Fin degree) × (Index →₀ ℕ) where
  toFun exponent :=
    (fun index => ⟨exponent index % degree, Nat.mod_lt _ (NeZero.pos degree)⟩,
      exponent.mapRange (fun value => value / degree) (Nat.zero_div degree))
  invFun pair := degree • pair.2 +
    Finsupp.equivFunOnFinite.symm (fun index => (pair.1 index).val)
  left_inv exponent := by
    ext index
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.mapRange_apply, Finsupp.coe_equivFunOnFinite_symm]
    exact Nat.div_add_mod _ _
  right_inv pair := by
    apply Prod.ext
    · funext index
      apply Fin.ext
      simp [Nat.add_mod, Nat.mod_eq_of_lt (pair.1 index).isLt]
    · ext index
      simp [Nat.mul_add_div (NeZero.pos degree), Nat.div_eq_of_lt (pair.1 index).isLt]

@[simp] theorem multiplicationExponentEquiv_symm_apply
    (residue : Index → Fin degree) (quotient : Index →₀ ℕ) :
    (multiplicationExponentEquiv degree).symm (residue, quotient) =
      degree • quotient + Finsupp.equivFunOnFinite.symm (fun index => (residue index).val) :=
  rfl

noncomputable def multiplicationPolynomialResidueEquiv
    (Coefficients : Type*) [CommSemiring Coefficients] :
    MvPolynomial Index Coefficients ≃ₗ[Coefficients]
      (Index → Fin degree) →₀ MvPolynomial Index Coefficients :=
  (AddMonoidAlgebra.coeffLinearEquiv Coefficients).trans
    (((Finsupp.mapDomain.linearEquiv Coefficients Coefficients
      (multiplicationExponentEquiv degree)).trans (Finsupp.curryLinearEquiv Coefficients)).trans
      (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv Coefficients).symm))

@[simp] theorem multiplicationPolynomialResidueEquiv_symm_single_monomial
    {Coefficients : Type*} [CommSemiring Coefficients]
    (residue : Index → Fin degree) (quotient : Index →₀ ℕ) (coefficient : Coefficients) :
    (multiplicationPolynomialResidueEquiv degree Coefficients).symm
      (Finsupp.single residue (MvPolynomial.monomial quotient coefficient)) =
      MvPolynomial.monomial
        (degree • quotient + Finsupp.equivFunOnFinite.symm
          (fun index => (residue index).val)) coefficient := by
  simp [multiplicationPolynomialResidueEquiv, Finsupp.uncurry_single,
    MvPolynomial.monomial, Finsupp.mapDomain.linearEquiv, Finsupp.curryLinearEquiv,
    Finsupp.mapRange.linearEquiv]

theorem multiplicationPolynomialResidueEquiv_symm_single
    {Coefficients : Type*} [CommSemiring Coefficients]
    (residue : Index → Fin degree) (polynomial : MvPolynomial Index Coefficients) :
    (multiplicationPolynomialResidueEquiv degree Coefficients).symm
      (Finsupp.single residue polynomial) =
      MvPolynomial.expand degree polynomial *
        MvPolynomial.monomial
          (Finsupp.equivFunOnFinite.symm (fun index => (residue index).val)) 1 := by
  induction polynomial using MvPolynomial.induction_on' with
  | monomial exponent coefficient =>
      simp [MvPolynomial.monomial_mul_monomial]
  | add first second first_eq second_eq =>
      simp only [Finsupp.single_add, map_add, first_eq, second_eq, add_mul]

theorem multiplicationPolynomialResidueEquiv_symm_smul
    {Coefficients : Type*} [CommSemiring Coefficients]
    (scalar : MvPolynomial Index Coefficients)
    (coefficients : (Index → Fin degree) →₀ MvPolynomial Index Coefficients) :
    (multiplicationPolynomialResidueEquiv degree Coefficients).symm (scalar • coefficients) =
      MvPolynomial.expand degree scalar *
        (multiplicationPolynomialResidueEquiv degree Coefficients).symm coefficients := by
  induction coefficients using Finsupp.induction_linear with
  | zero => simp
  | add first second first_eq second_eq =>
      simp only [smul_add, map_add, first_eq, second_eq, mul_add]
  | single residue polynomial =>
      simp [multiplicationPolynomialResidueEquiv_symm_single, Finsupp.smul_single,
        smul_eq_mul, mul_assoc]

noncomputable def multiplicationPolynomialLinearEquiv
    (Coefficients : Type*) [CommSemiring Coefficients] :
    letI : Algebra (MvPolynomial Index Coefficients) (MvPolynomial Index Coefficients) :=
      (MvPolynomial.expand degree).toRingHom.toAlgebra
    ((Index → Fin degree) →₀ MvPolynomial Index Coefficients) ≃ₗ[MvPolynomial Index Coefficients]
      RestrictScalars (MvPolynomial Index Coefficients) (MvPolynomial Index Coefficients)
        (MvPolynomial Index Coefficients) := by
  letI : Algebra (MvPolynomial Index Coefficients) (MvPolynomial Index Coefficients) :=
    (MvPolynomial.expand degree).toRingHom.toAlgebra
  refine
    { (multiplicationPolynomialResidueEquiv degree Coefficients).symm.toAddEquiv.trans
        (RestrictScalars.addEquiv (MvPolynomial Index Coefficients)
          (MvPolynomial Index Coefficients) (MvPolynomial Index Coefficients)).symm with
      map_smul' := ?_ }
  intro scalar coefficients
  change (multiplicationPolynomialResidueEquiv degree Coefficients).symm (scalar • coefficients) =
    MvPolynomial.expand degree scalar *
      (multiplicationPolynomialResidueEquiv degree Coefficients).symm coefficients
  exact multiplicationPolynomialResidueEquiv_symm_smul degree scalar coefficients

noncomputable def multiplicationPolynomialBasis
    (Coefficients : Type*) [CommSemiring Coefficients] :
    letI : Algebra (MvPolynomial Index Coefficients) (MvPolynomial Index Coefficients) :=
      (MvPolynomial.expand degree).toRingHom.toAlgebra
    Module.Basis (Index → Fin degree) (MvPolynomial Index Coefficients)
      (RestrictScalars (MvPolynomial Index Coefficients) (MvPolynomial Index Coefficients)
        (MvPolynomial Index Coefficients)) := by
  letI : Algebra (MvPolynomial Index Coefficients) (MvPolynomial Index Coefficients) :=
    (MvPolynomial.expand degree).toRingHom.toAlgebra
  exact Module.Basis.ofRepr (multiplicationPolynomialLinearEquiv degree Coefficients).symm

end BondalThomsen
