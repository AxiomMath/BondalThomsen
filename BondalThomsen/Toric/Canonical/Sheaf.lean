module

public import BondalThomsen.Toric.Scheme.BasisChart
public import BondalThomsen.Toric.Divisor.DivisorLineBundle
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

namespace BondalThomsen

universe schemeUniverse

noncomputable def cotangentCoefficientMap {SchemeModel Base : Scheme.{schemeUniverse}}
    (structureMap : SchemeModel ⟶ Base) :
    (Functor.const SchemeModel.Opensᵒᵖ).obj (Base.presheaf.obj (op ⊤)) ⟶ SchemeModel.presheaf where
  app domain := structureMap.appLE ⊤ domain.unop (by simp)
  naturality := by
    intro domain smaller inclusion
    change structureMap.appLE ⊤ smaller.unop (by simp) =
      structureMap.appLE ⊤ domain.unop (by simp) ≫ SchemeModel.presheaf.map inclusion
    exact (structureMap.appLE_map (by simp) inclusion).symm

noncomputable def cotangentPresheaf {SchemeModel Base : Scheme.{schemeUniverse}}
    (structureMap : SchemeModel ⟶ Base) : SchemeModel.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (cotangentCoefficientMap structureMap)

noncomputable def cotangentSheaf {SchemeModel Base : Scheme.{schemeUniverse}}
    (structureMap : SchemeModel ⟶ Base) : SchemeModel.Modules :=
  (PresheafOfModules.sheafification (𝟙 SchemeModel.ringCatSheaf.obj)).obj
    (cotangentPresheaf structureMap)

theorem cotangentPresheaf_map_d {SchemeModel Base : Scheme.{schemeUniverse}}
    (structureMap : SchemeModel ⟶ Base) {domain smaller : SchemeModel.Opens}
    (inclusion : smaller ⟶ domain) (regularFunction : Γ(SchemeModel, domain)) :
    (cotangentPresheaf structureMap).map inclusion.op
        (CommRingCat.KaehlerDifferential.d regularFunction) =
      CommRingCat.KaehlerDifferential.d (SchemeModel.presheaf.map inclusion.op regularFunction) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
    (cotangentCoefficientMap structureMap) inclusion.op regularFunction

namespace DifferentialCoordinates

universe coefficientUniverse algebraUniverse

variable {Coefficient : Type coefficientUniverse} [CommRing Coefficient]
    {Source Target : Type algebraUniverse} [CommRing Source] [CommRing Target]
    [Algebra Coefficient Source] [Algebra Coefficient Target]

noncomputable def map (algebraMap : Source →ₐ[Coefficient] Target) :
    KaehlerDifferential Coefficient Source →ₛₗ[algebraMap.toRingHom]
      KaehlerDifferential Coefficient Target := by
  letI := algebraMap.toRingHom.toAlgebra
  letI : IsScalarTower Coefficient Source Target :=
    IsScalarTower.of_algebraMap_eq' algebraMap.comp_algebraMap.symm
  let differentialMap := KaehlerDifferential.map Coefficient Coefficient Source Target
  exact
    { toFun := differentialMap
      map_add' := differentialMap.map_add
      map_smul' := fun coefficient differential => differentialMap.map_smul coefficient differential }

theorem map_D (algebraMap : Source →ₐ[Coefficient] Target) (regularFunction : Source) :
    map algebraMap (KaehlerDifferential.D Coefficient Source regularFunction) =
      KaehlerDifferential.D Coefficient Target (algebraMap regularFunction) := by
  let := algebraMap.toRingHom.toAlgebra
  let : IsScalarTower Coefficient Source Target :=
    IsScalarTower.of_algebraMap_eq' algebraMap.comp_algebraMap.symm
  exact KaehlerDifferential.map_D Coefficient Coefficient Source Target regularFunction

noncomputable def equiv (algebraEquiv : Source ≃ₐ[Coefficient] Target) :
    letI := RingHomInvPair.of_ringEquiv algebraEquiv.toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm algebraEquiv.toRingEquiv
    LinearEquiv (algebraEquiv.toRingEquiv : Source →+* Target)
      (σ' := (algebraEquiv.toRingEquiv.symm : Target →+* Source))
      (KaehlerDifferential Coefficient Source) (KaehlerDifferential Coefficient Target) := by
  letI := RingHomInvPair.of_ringEquiv algebraEquiv.toRingEquiv
  letI := RingHomInvPair.of_ringEquiv_symm algebraEquiv.toRingEquiv
  let forward := map algebraEquiv.toAlgHom
  let backward := map algebraEquiv.symm.toAlgHom
  have inverse {First Second : Type algebraUniverse} [CommRing First] [CommRing Second]
      [Algebra Coefficient First] [Algebra Coefficient Second]
      (first : First ≃ₐ[Coefficient] Second)
      (differential : KaehlerDifferential Coefficient First) :
      map first.symm.toAlgHom (map first.toAlgHom differential) = differential := by
    obtain ⟨coefficients, rfl⟩ :=
      KaehlerDifferential.linearCombination_surjective Coefficient First differential
    induction coefficients using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add first second first_eq second_eq => simp only [map_add, first_eq, second_eq]
    | single regularFunction coefficient =>
        simp only [Finsupp.linearCombination_single, map_smulₛₗ, map_D]
        change first.symm (first coefficient) •
          KaehlerDifferential.D Coefficient First (first.symm (first regularFunction)) = _
        simp only [AlgEquiv.symm_apply_apply]
  exact
    { forward with
      invFun := backward
      left_inv := inverse algebraEquiv
      right_inv := inverse algebraEquiv.symm }

end DifferentialCoordinates

end BondalThomsen

