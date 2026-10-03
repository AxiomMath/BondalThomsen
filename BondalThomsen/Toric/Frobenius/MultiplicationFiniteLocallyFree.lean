module

public import BondalThomsen.Toric.Frobenius.MultiplicationFlat
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.LinearAlgebra.Dimension.Free
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.GeneratingSections
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable def affinePushforwardStructureSectionsEquiv {Source Target : CommRingCat}
    (ring_map : Target ⟶ Source) :
    letI := Module.compHom Source ring_map.hom
    (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pushforward (Spec.map ring_map)).obj
        (SheafOfModules.unit (Spec Source).ringCatSheaf))) ≃ₗ[Target] Source := by
  letI := Module.compHom Source ring_map.hom
  refine
    { (Scheme.ΓSpecIso Source).commRingCatIsoToRingEquiv.toAddEquiv with
      map_smul' := ?_ }
  intro scalar element
  let value : Γ(Spec Source, ⊤) := element
  change (Scheme.ΓSpecIso Source).hom
      ((Spec.map ring_map).appTop ((Scheme.ΓSpecIso Target).inv scalar) * value) =
    ring_map.hom scalar * (Scheme.ΓSpecIso Source).hom value
  rw [map_mul]
  have naturality := congrArg (fun morphism : Target ⟶ Source => morphism scalar)
    (Scheme.ΓSpecIso_inv_naturality_assoc ring_map (Scheme.ΓSpecIso Source).hom)
  simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] using congrArg (fun coefficient : Source =>
    coefficient * (Scheme.ΓSpecIso Source).hom value) naturality.symm

set_option backward.isDefEq.respectTransparency false in
noncomputable def openPullbackPushforwardRestrictIso {Source Target LocalSource LocalTarget : Scheme}
    {morphism : Source ⟶ Target} {local_morphism : LocalSource ⟶ LocalTarget}
    {source_open : LocalSource ⟶ Source} {target_open : LocalTarget ⟶ Target}
    [IsOpenImmersion source_open] [IsOpenImmersion target_open]
    (square : IsPullback local_morphism source_open target_open morphism)
    (sheaf : Source.Modules) :
    ((Scheme.Modules.pushforward morphism).obj sheaf).restrict target_open ≅
      (Scheme.Modules.pushforward local_morphism).obj (sheaf.restrict source_open) := by
  let comparison := (Scheme.Modules.restrictFunctor target_open).map
    ((Scheme.Modules.pushforward morphism).map
      ((Scheme.Modules.restrictAdjunction source_open).unit.app sheaf))
  have image_eq (open_set : LocalTarget.Opens) :
      source_open ''ᵁ source_open ⁻¹ᵁ (morphism ⁻¹ᵁ target_open ''ᵁ open_set) =
        morphism ⁻¹ᵁ target_open ''ᵁ open_set := by
    rw [← IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback square open_set,
      source_open.preimage_image_eq]
  letI : IsIso comparison := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro open_set
    change IsIso (sheaf.presheaf.map
      (homOfLE (source_open.image_preimage_le
        (morphism ⁻¹ᵁ target_open ''ᵁ open_set))).op)
    have equal := image_eq open_set
    have inclusion_eq : homOfLE (source_open.image_preimage_le
        (morphism ⁻¹ᵁ target_open ''ᵁ open_set)) = eqToHom equal := Subsingleton.elim _ _
    rw [inclusion_eq]
    infer_instance
  let local_sheaf := (Scheme.Modules.pushforward local_morphism).obj
    (sheaf.restrict source_open)
  exact asIso comparison ≪≫
    (Scheme.Modules.restrictFunctor target_open).mapIso
      ((Scheme.Modules.pushforwardComp source_open morphism).app
        (sheaf.restrict source_open)) ≪≫
    (Scheme.Modules.restrictFunctor target_open).mapIso
      ((Scheme.Modules.pushforwardCongr square.w.symm).app
        (sheaf.restrict source_open)) ≪≫
    (Scheme.Modules.restrictFunctor target_open).mapIso
      ((Scheme.Modules.pushforwardComp local_morphism target_open).symm.app
        (sheaf.restrict source_open)) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso target_open).app local_sheaf

noncomputable def openImmersionOverRestrictionIso {Source Target : Scheme}
    (open_map : Source ⟶ Target) [IsOpenImmersion open_map] (sheaf : Target.Modules) :
    ((Scheme.Modules.restrictFunctor open_map.isoOpensRange.inv) ⋙
        (Scheme.Modules.overEquiv open_map.opensRange).inverse).obj
        (sheaf.restrict open_map) ≅ sheaf.over open_map.opensRange :=
  (Scheme.Modules.overEquiv open_map.opensRange).inverse.mapIso
      ((Scheme.Modules.restrictFunctorComp open_map.isoOpensRange.inv open_map).symm.app sheaf ≪≫
        (Scheme.Modules.restrictFunctorCongr open_map.isoOpensRange_inv_comp).app sheaf ≪≫
        (Scheme.Modules.overFunctorEquiv open_map.opensRange).symm.app sheaf) ≪≫
    (Scheme.Modules.overEquiv open_map.opensRange).unitIso.symm.app _

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def basisConeMultiplicationBasis (fan : Fan embedding)
    {degree dimension : ℕ} (positive : 0 < degree)
    (basis : Module.Basis (Fin dimension) ℤ Lattice) :
    letI := Module.compHom
      (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
      (fan.toricMultiplicationRing 𝕜 degree
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))).toRingHom
    Module.Basis (Fin dimension → Fin degree)
      (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
      (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) := by
  letI : NeZero degree := ⟨positive.ne'⟩
  letI : Algebra (MvPolynomial (Fin dimension) 𝕜)
      (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :=
    ((fan.toricMultiplicationRing 𝕜 degree _).toRingHom.comp
      (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm.toRingHom).toAlgebra
  letI : Algebra (MvPolynomial (Fin dimension) 𝕜) (MvPolynomial (Fin dimension) 𝕜) :=
    (MvPolynomial.expand degree).toRingHom.toAlgebra
  let polynomial_basis :=
    (BondalThomsen.multiplicationPolynomialBasis (Index := Fin dimension) degree 𝕜).map
      (fan.basisConeMultiplicationLinearEquiv 𝕜 degree basis).symm
  letI := Module.compHom
    (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (fan.toricMultiplicationRing 𝕜 degree
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))).toRingHom
  exact polynomial_basis.mapCoeffs
    (fan.basisConeCoordinateRingEquiv 𝕜 basis).symm.toRingEquiv (fun _ _ => rfl)

noncomputable def toricMultiplicationPushforward (fan : Fan embedding)
    (regular : fan.IsRegular) (degree : ℕ) : (fan.algebraicRealization 𝕜 regular).Modules :=
  (Scheme.Modules.pushforward (fan.toricMultiplication 𝕜 regular degree)).obj
    (SheafOfModules.unit (fan.algebraicRealization 𝕜 regular).ringCatSheaf)

noncomputable def toricMultiplicationPushforwardChartIso (fan : Fan embedding)
    (regular : fan.IsRegular) {degree : ℕ} (positive : 0 < degree) (cone : fan.cones) :
    (fan.toricMultiplicationPushforward 𝕜 regular degree).restrict
        (fan.affineToricChartι 𝕜 regular cone) ≅
      (Scheme.Modules.pushforward (fan.toricMultiplicationChart 𝕜 degree cone)).obj
        (SheafOfModules.unit (fan.affineToricChart 𝕜 cone).ringCatSheaf) :=
  BondalThomsen.openPullbackPushforwardRestrictIso
      (fan.toricMultiplicationChart_isPullback 𝕜 regular positive cone) _ ≪≫
    (Scheme.Modules.pushforward (fan.toricMultiplicationChart 𝕜 degree cone)).mapIso
      (Scheme.Modules.restrictUnitIso (fan.affineToricChartι 𝕜 regular cone))

end TauCeti.Toric.Fan
