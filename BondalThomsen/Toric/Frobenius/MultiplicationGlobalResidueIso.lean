module

public import BondalThomsen.Toric.Frobenius.MultiplicationResidueLocalIso

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

local instance globalResidueFrameSchemeFiniteBiproducts (schemeModel : Scheme) :
    HasFiniteBiproducts schemeModel.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance globalResidueFrameSheafFiniteBiproducts
    {Site : Type*} [Category Site] {Topology : GrothendieckTopology Site}
    (ringSheaf : Sheaf Topology RingCat) : HasFiniteBiproducts (SheafOfModules.{0} ringSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance globalResidueRestrictAdditive {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion] :
    (Scheme.Modules.restrictFunctor inclusion).Additive :=
  Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback inclusion).symm

noncomputable def finiteBiproductFrameRestrictionIso {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {Index : Type} [Fintype Index] (objects : Index → Target.Modules)
    [HasBiproduct objects]
    (frames : ∀ index, SheafOfModules.unit Source.ringCatSheaf ≅
      (objects index).restrict inclusion) :
    (⨁ fun _ : Index => (SheafOfModules.unit Source.ringCatSheaf : Source.Modules)) ≅
      (⨁ objects).restrict inclusion :=
  biproduct.mapIso frames ≪≫
    ((Scheme.Modules.restrictFunctor inclusion).mapBiproduct objects).symm

theorem finiteBiproductFrameRestrictionIso_summand {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {Index : Type} [Fintype Index] (objects : Index → Target.Modules)
    [HasBiproduct objects]
    (frames : ∀ index, SheafOfModules.unit Source.ringCatSheaf ≅
      (objects index).restrict inclusion) (index : Index) :
    biproduct.ι (fun _ : Index =>
      (SheafOfModules.unit Source.ringCatSheaf : Source.Modules)) index ≫
      (finiteBiproductFrameRestrictionIso inclusion objects frames).hom =
      (frames index).hom ≫
        (Scheme.Modules.restrictFunctor inclusion).map (biproduct.ι objects index) := by
  simp only [finiteBiproductFrameRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    biproduct.mapIso_hom, biproduct.ι_map_assoc,
    Functor.mapBiproduct_inv, biproduct.ι_desc]

noncomputable def residueRestrictSchemeIsoEquivalence {Source Target : Scheme}
    (schemeIso : Source ≅ Target) : Target.Modules ≌ Source.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor schemeIso.hom)
    (Scheme.Modules.restrictFunctor schemeIso.inv)
    (Scheme.Modules.restrictFunctorId.symm ≪≫
      Scheme.Modules.restrictFunctorCongr schemeIso.inv_hom_id.symm ≪≫
      Scheme.Modules.restrictFunctorComp schemeIso.inv schemeIso.hom)
    ((Scheme.Modules.restrictFunctorComp schemeIso.hom schemeIso.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr schemeIso.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId)

local instance residueRestrictSchemeIsoReflects {Source Target : Scheme}
    (schemeIso : Source ≅ Target) :
    (Scheme.Modules.restrictFunctor schemeIso.hom).ReflectsIsomorphisms :=
  inferInstanceAs (residueRestrictSchemeIsoEquivalence schemeIso).functor.ReflectsIsomorphisms

theorem residueRestriction_iso_of_affine {Source Target : Scheme}
    (inclusion : Source ⟶ Target) [IsOpenImmersion inclusion]
    {sourceSheaf targetSheaf : Target.Modules} (comparison : sourceSheaf ⟶ targetSheaf)
    [IsIso ((Scheme.Modules.restrictFunctor inclusion).map comparison)] :
    IsIso (comparison.over inclusion.opensRange) := by
  let transport := Scheme.Modules.restrictFunctor inclusion.isoOpensRange.hom
  have localIso : IsIso ((Scheme.Modules.restrictFunctor inclusion.opensRange.ι).map comparison) := by
    apply (isIso_iff_of_reflects_iso _ transport).mp
    have compositeIso : IsIso
        ((Scheme.Modules.restrictFunctor
          (inclusion.isoOpensRange.hom ≫ inclusion.opensRange.ι)).map comparison) := by
      let comparisonIso := Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_hom_ι
      rw [← isIso_comp_right_iff _ (comparisonIso.hom.app targetSheaf),
        comparisonIso.hom.naturality]
      infer_instance
    let := compositeIso
    let composition := Scheme.Modules.restrictFunctorComp
      inclusion.isoOpensRange.hom inclusion.opensRange.ι
    change IsIso ((Scheme.Modules.restrictFunctor inclusion.opensRange.ι ⋙
      Scheme.Modules.restrictFunctor inclusion.isoOpensRange.hom).map comparison)
    rw [← isIso_comp_left_iff (composition.hom.app sourceSheaf),
      ← composition.hom.naturality]
    infer_instance
  let := localIso
  apply (isIso_iff_of_reflects_iso _ (Scheme.Modules.overEquiv inclusion.opensRange).functor).mp
  let overComparison := Scheme.Modules.overFunctorEquiv inclusion.opensRange
  change IsIso ((SheafOfModules.overFunctor Target.ringCatSheaf inclusion.opensRange ⋙
    (Scheme.Modules.overEquiv inclusion.opensRange).functor).map comparison)
  rw [← isIso_comp_right_iff _ (overComparison.hom.app targetSheaf),
    overComparison.hom.naturality]
  infer_instance

end BondalThomsen

namespace TauCeti.Toric.Fan

local instance globalResidueSchemeFiniteBiproducts (schemeModel : Scheme) :
    HasFiniteBiproducts schemeModel.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance globalResidueSheafFiniteBiproducts
    {Site : Type*} [Category Site] {Topology : GrothendieckTopology Site}
    (ringSheaf : Sheaf Topology RingCat) : HasFiniteBiproducts (SheafOfModules.{0} ringSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def residueLineBundleChartFrameIso
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (degree : ℕ) (index : Fin (Nat.card fan.cones)) :
    let cone := (fan.residueFloorAtlas 𝕜 complete regular degree 0).cone index
    (⨁ fun _ : Fin (Module.finrank ℤ Lattice) → Fin degree =>
      (SheafOfModules.unit (fan.affineToricChart 𝕜 cone).ringCatSheaf :
        (fan.affineToricChart 𝕜 cone).Modules)) ≅
      (fan.residueLineBundleBiproduct 𝕜 complete regular degree).restrict
        (fan.affineToricChartι 𝕜 regular cone) :=
  BondalThomsen.finiteBiproductFrameRestrictionIso
    (fan.affineToricChartι 𝕜 regular ((fan.residueFloorAtlas 𝕜 complete regular degree 0).cone index))
    (fun residue : Fin (Module.finrank ℤ Lattice) → Fin degree =>
      (fan.floorDivisorInvertibleSheaf 𝕜 complete regular
        ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp
          (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue))).obj)
    (fun residue => BondalThomsen.residueOverToAffineFrame _ _
      (fan.residueFloorFrame 𝕜 complete regular degree
        (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue) index))

theorem residueLineBundleBiproductMap_chart_comparison
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) (index : Fin (Nat.card fan.cones)) :
    let cone := (fan.residueFloorAtlas 𝕜 complete regular degree 0).cone index
    (fan.residueLineBundleChartFrameIso 𝕜 complete regular degree index).hom ≫
      (Scheme.Modules.restrictFunctor (fan.affineToricChartι 𝕜 regular cone)).map
        (fan.residueLineBundleBiproductMap 𝕜 complete regular positive) ≫
      (fan.toricMultiplicationPushforwardChartIso 𝕜 regular positive cone).hom =
    (fan.basisConeGlobalResidueBiproductIso 𝕜 (Module.finBasis ℤ Lattice)
      (fan.residueFloorChartBasis 𝕜 complete regular degree 0 index).val.2
      (fan.residueFloorChartBasis 𝕜 complete regular degree 0 index).property.1 positive).hom := by
  classical
  dsimp only
  unfold residueLineBundleChartFrameIso
  apply biproduct.hom_ext'
  intro residue
  rw [← Category.assoc, ← Category.assoc,
    BondalThomsen.finiteBiproductFrameRestrictionIso_summand]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc,
    fan.residueLineBundleBiproductMap_summand 𝕜]
  exact (fan.residueFloorGlobalInclusion_canonicalChart_component 𝕜
    complete regular positive (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue)
      index).trans
    (fan.basisConeGlobalResidueBiproductIso_summand 𝕜 (Module.finBasis ℤ Lattice)
      (fan.residueFloorChartBasis 𝕜 complete regular degree 0 index).val.2
      (fan.residueFloorChartBasis 𝕜 complete regular degree 0 index).property.1
      positive residue).symm

theorem residueLineBundleBiproductMap_restrict_isIso
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) (index : Fin (Nat.card fan.cones)) :
    IsIso ((Scheme.Modules.restrictFunctor (fan.affineToricChartι 𝕜 regular
      ((fan.residueFloorAtlas 𝕜 complete regular degree 0).cone index))).map
        (fan.residueLineBundleBiproductMap 𝕜 complete regular positive)) := by
  let frames := fan.residueLineBundleChartFrameIso 𝕜 complete regular degree index
  let chartComparison := fan.toricMultiplicationPushforwardChartIso 𝕜 regular positive
    ((fan.residueFloorAtlas 𝕜 complete regular degree 0).cone index)
  rw [← isIso_comp_right_iff _ chartComparison.hom,
    ← isIso_comp_left_iff frames.hom,
    fan.residueLineBundleBiproductMap_chart_comparison 𝕜]
  infer_instance

theorem residueLineBundleBiproductMap_over_isIso
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) (index : Fin (Nat.card fan.cones)) :
    IsIso ((fan.residueLineBundleBiproductMap 𝕜 complete regular positive).over
      (fan.affineToricChartι 𝕜 regular
        ((fan.residueFloorAtlas 𝕜 complete regular degree 0).cone index)).opensRange) := by
  let := fan.residueLineBundleBiproductMap_restrict_isIso 𝕜 complete regular positive index
  exact BondalThomsen.residueRestriction_iso_of_affine _ _

theorem residueLineBundleBiproductMap_isIso
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) :
    IsIso (fan.residueLineBundleBiproductMap 𝕜 complete regular positive) := by
  let comparison := fan.residueLineBundleBiproductMap 𝕜 complete regular positive
  let schemeModel := fan.algebraicRealization 𝕜 regular
  let atlas := fan.residueFloorAtlas 𝕜 complete regular degree 0
  let forget := SheafOfModules.toSheaf schemeModel.ringCatSheaf
  have globalIso : IsIso (forget.map comparison) := by
    apply CategoryTheory.Sheaf.isIso_of_coversTop
      ((Opens.coversTop_iff (schemeModel : Type)
        (fun index => (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange)).mpr
        atlas.covers.iSup_eq_top)
    intro index
    let := fan.residueLineBundleBiproductMap_over_isIso 𝕜 complete regular positive index
    change IsIso ((SheafOfModules.toSheaf (schemeModel.ringCatSheaf.over
      (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange)).map
        (comparison.over (fan.affineToricChartι 𝕜 regular (atlas.cone index)).opensRange))
    infer_instance
  let := globalIso
  have presheafIso : IsIso ((Scheme.Modules.toPresheaf schemeModel).map comparison) := by
    change IsIso ((sheafToPresheaf (Opens.grothendieckTopology schemeModel) AddCommGrpCat).map
      (forget.map comparison))
    infer_instance
  exact (isIso_iff_of_reflects_iso comparison (Scheme.Modules.toPresheaf schemeModel)).mp
    presheafIso

noncomputable def toricMultiplicationGlobalResidueIso
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) :
    fan.toricMultiplicationPushforward 𝕜 regular degree ≅
      fan.residueLineBundleBiproduct 𝕜 complete regular degree := by
  letI := fan.residueLineBundleBiproductMap_isIso 𝕜 complete regular positive
  exact (asIso (fan.residueLineBundleBiproductMap 𝕜 complete regular positive)).symm

theorem toricMultiplicationResidueDecomposition
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) :
    fan.ToricMultiplicationResidueDecomposition 𝕜 complete regular := by
  intro degree positive
  exact ⟨fan.toricMultiplicationGlobalResidueIso 𝕜 complete regular positive⟩

end TauCeti.Toric.Fan
