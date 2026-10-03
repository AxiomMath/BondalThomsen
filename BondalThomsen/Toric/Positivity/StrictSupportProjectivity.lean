module

public import BondalThomsen.Toric.Divisor.DivisorMonomialGlobalEmbedding
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Module Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectivePolynomialConstants_bijective (Index : Type) :
    Function.Bijective (projectivePolynomialConstants 𝕜 Index) := by
  constructor
  · intro first second same
    have constants_same : MvPolynomial.C first = (MvPolynomial.C second : MvPolynomial Index 𝕜) :=
      congrArg Subtype.val same
    simpa using congrArg (fun polynomial : MvPolynomial Index 𝕜 => polynomial.coeff 0)
      constants_same
  · intro polynomial
    refine ⟨polynomial.val.coeff 0, Subtype.ext ?_⟩
    exact (MvPolynomial.homogeneousComponent_zero polynomial.val).symm.trans
      (MvPolynomial.homogeneousComponent_eq_self polynomial.property)

noncomputable def projectivePolynomialConstantsEquiv (Index : Type) :
    𝕜 ≃+* MvPolynomial.homogeneousSubmodule Index 𝕜 0 :=
  RingEquiv.ofBijective (projectivePolynomialConstants 𝕜 Index)
    (projectivePolynomialConstants_bijective 𝕜 Index)

theorem projectivePolynomial_finiteType_over_degreeZero (Index : Type) [Finite Index] :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule Index 𝕜 0)
      (MvPolynomial Index 𝕜) := by
  classical
  let := Fintype.ofFinite Index
  refine ⟨⟨Finset.univ.image (MvPolynomial.X : Index → MvPolynomial Index 𝕜), ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  apply top_unique
  intro polynomial _
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
      exact (Algebra.adjoin (MvPolynomial.homogeneousSubmodule Index 𝕜 0)
        (Set.range (MvPolynomial.X : Index → MvPolynomial Index 𝕜))).algebraMap_mem
          (projectivePolynomialConstants 𝕜 Index scalar)
  | add first second first_mem second_mem =>
      exact Subalgebra.add_mem _ (first_mem trivial) (second_mem trivial)
  | mul_X polynomial index polynomial_mem =>
      exact Subalgebra.mul_mem _ (polynomial_mem trivial) (Algebra.subset_adjoin ⟨index, rfl⟩)

theorem polynomialProjStructureMap_isProper (Index : Type) [Finite Index] :
    IsProper (polynomialProjStructureMap 𝕜 Index) := by
  let := projectivePolynomial_finiteType_over_degreeZero 𝕜 Index
  let : IsIso (CommRingCat.ofHom (projectivePolynomialConstants 𝕜 Index)) := by
    change IsIso (projectivePolynomialConstantsEquiv 𝕜 Index).toCommRingCatIso.hom
    infer_instance
  unfold polynomialProjStructureMap
  infer_instance

end BondalThomsen

namespace TauCeti.Toric.Fan

attribute [local instance] MvPolynomial.gradedAlgebra

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)

include complete regular in
theorem allSectionProjectiveSpace_structureMap_isProper :
    IsProper (BondalThomsen.polynomialProjStructureMap 𝕜
      (fan.globalDivisorSectionExponents divisor)) := by
  let := fan.allDivisorMonomialCharacters_finite complete regular divisor
  exact BondalThomsen.polynomialProjStructureMap_isProper 𝕜 _

end TauCeti.Toric.Fan

namespace TauCeti.Toric.Fan

section SourceProjectivityObstruction

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

variable [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)
    (strict_support : ∀ dimension (basis : Basis (Fin dimension) ℤ Lattice)
      (cone_basis : fan.IsConeBasis basis),
        fan.BasisDivisorStrictSupport basis cone_basis divisor)
    (steps : fan.AllSectionProjectiveStepsAdmissible complete regular divisor)

include strict_support steps

end SourceProjectivityObstruction

end TauCeti.Toric.Fan
