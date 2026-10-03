module

public import BondalThomsen.Ports.MiyaokaMori.Nef.SpecResidueDegree
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Intersection

theorem residueFieldComp_isScalarTower {source intermediate target : Scheme.{u}}
    (first : source ⟶ intermediate) (second : intermediate ⟶ target) (point : source) :
    letI : Algebra (target.residueField (second (first point))) (intermediate.residueField (first point)) :=
      (second.residueFieldMap (first point)).hom.toAlgebra
    letI : Algebra (intermediate.residueField (first point)) (source.residueField point) :=
      (first.residueFieldMap point).hom.toAlgebra
    letI : Algebra (target.residueField (second (first point))) (source.residueField point) :=
      ((first ≫ second).residueFieldMap point).hom.toAlgebra
    IsScalarTower (target.residueField (second (first point)))
      (intermediate.residueField (first point)) (source.residueField point) := by
  let : Algebra (target.residueField (second (first point))) (intermediate.residueField (first point)) :=
    (second.residueFieldMap (first point)).hom.toAlgebra
  let : Algebra (intermediate.residueField (first point)) (source.residueField point) :=
    (first.residueFieldMap point).hom.toAlgebra
  let : Algebra (target.residueField (second (first point))) (source.residueField point) :=
    ((first ≫ second).residueFieldMap point).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  change ((first ≫ second).residueFieldMap point).hom =
    (first.residueFieldMap point).hom.comp (second.residueFieldMap (first point)).hom
  exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp first second point)

theorem residueDegree_comp {source intermediate target : Scheme.{u}}
    (first : source ⟶ intermediate) (second : intermediate ⟶ target) (point : source) :
    (first ≫ second).residueDegree point = second.residueDegree (first point) * first.residueDegree point := by
  let : Algebra (target.residueField (second (first point))) (intermediate.residueField (first point)) :=
    (second.residueFieldMap (first point)).hom.toAlgebra
  let : Algebra (intermediate.residueField (first point)) (source.residueField point) :=
    (first.residueFieldMap point).hom.toAlgebra
  let : Algebra (target.residueField (second (first point))) (source.residueField point) :=
    ((first ≫ second).residueFieldMap point).hom.toAlgebra
  have : IsScalarTower (target.residueField (second (first point)))
      (intermediate.residueField (first point)) (source.residueField point) :=
    residueFieldComp_isScalarTower first second point
  change Module.finrank (target.residueField (second (first point))) (source.residueField point) =
    Module.finrank (target.residueField (second (first point))) (intermediate.residueField (first point)) *
      Module.finrank (intermediate.residueField (first point)) (source.residueField point)
  exact (Module.finrank_mul_finrank (target.residueField (second (first point)))
    (intermediate.residueField (first point)) (source.residueField point)).symm

end AlgebraicGeometry.Intersection
