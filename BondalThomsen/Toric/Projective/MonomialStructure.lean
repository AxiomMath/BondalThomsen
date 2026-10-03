module

public import BondalThomsen.Toric.Projective.MonomialMap
public import BondalThomsen.Toric.Scheme.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def projectivePolynomialConstants (Index : Type) :
    𝕜 →+* MvPolynomial.homogeneousSubmodule Index 𝕜 0 where
  toFun scalar := ⟨MvPolynomial.C scalar, MvPolynomial.isHomogeneous_C Index scalar⟩
  map_one' := by apply Subtype.ext; exact MvPolynomial.C.map_one
  map_mul' first second := by apply Subtype.ext; exact MvPolynomial.C.map_mul first second
  map_zero' := by apply Subtype.ext; exact MvPolynomial.C.map_zero
  map_add' first second := by apply Subtype.ext; exact MvPolynomial.C.map_add first second

noncomputable def polynomialProjStructureMap (Index : Type) :
    Proj (MvPolynomial.homogeneousSubmodule Index 𝕜) ⟶ Spec (CommRingCat.of 𝕜) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule Index 𝕜) ≫
    Spec.map (CommRingCat.ofHom (projectivePolynomialConstants 𝕜 Index))

theorem projectiveAwayEvaluation_constant {Index Ring : Type} [CommRing Ring]
    (constants : 𝕜 →+* Ring) (coordinates : Index → Ring) (index : Index)
    (coordinate_unit : Ringˣ) (unit_value : coordinates index = coordinate_unit)
    (scalar : 𝕜) :
    projectiveAwayEvaluation 𝕜 constants coordinates (MvPolynomial.X index) coordinate_unit
      (by simpa using unit_value)
      (HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule Index 𝕜) (Submonoid.powers (MvPolynomial.X index))
        (projectivePolynomialConstants 𝕜 Index scalar)) = constants scalar := by
  have fraction : HomogeneousLocalization.fromZeroRingHom
      (MvPolynomial.homogeneousSubmodule Index 𝕜) (Submonoid.powers (MvPolynomial.X index))
      (projectivePolynomialConstants 𝕜 Index scalar) =
        HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule Index 𝕜)
          (MvPolynomial.isHomogeneous_X 𝕜 index) 0 (MvPolynomial.C scalar)
          (by simp) := by
    rfl
  rw [fraction, projectiveAwayEvaluation_mk]
  simp only [MvPolynomial.eval₂Hom_C, pow_zero, mul_one]

@[reassoc]
theorem projectiveCoordinateMap_structureMap {Index Ring : Type} [CommRing Ring]
    [Algebra 𝕜 Ring] (coordinates : Index → Ring) (index : Index)
    (coordinate_unit : Ringˣ) (unit_value : coordinates index = coordinate_unit) :
    projectiveCoordinateMap 𝕜 (algebraMap 𝕜 Ring) coordinates index coordinate_unit unit_value ≫
        polynomialProjStructureMap 𝕜 Index =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 Ring)) := by
  unfold projectiveCoordinateMap polynomialProjStructureMap
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro scalar
  exact projectiveAwayEvaluation_constant 𝕜 (algebraMap 𝕜 Ring) coordinates index
    coordinate_unit unit_value scalar

end BondalThomsen

namespace TauCeti.Toric.Fan

open TauCeti.Toric

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

end TauCeti.Toric.Fan
