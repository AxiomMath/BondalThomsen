module

public import BondalThomsen.ProjectiveBundle.FamilyProjectivity
public import BondalThomsen.ProjectiveBundle.FamilyNondeepScheme

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Filter Real

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BondalThomsen.ProjectiveBundle

theorem parameterScheme_projectiveClosedEmbedding (dimension : ℕ)
    (matrix : FixedWeightMatrix (familyRows dimension) (familyColumns dimension)
      (familyWeight dimension))
    (base_positive : 0 < familyWeight dimension) (fiber_positive : 0 < familyColumns dimension) :
    ∃ Index : Type, Finite Index ∧
      ∃ closed_map : parameterScheme 𝕜 dimension matrix ⟶
          Proj (MvPolynomial.homogeneousSubmodule Index 𝕜),
        IsClosedImmersion closed_map ∧ closed_map ≫ polynomialProjStructureMap 𝕜 Index =
          parameterSchemeStructureMap 𝕜 dimension matrix :=
  paperFamily_projectiveClosedEmbedding 𝕜 (baseDimension := familyWeight dimension)
    matrix base_positive fiber_positive

end BondalThomsen.ProjectiveBundle
