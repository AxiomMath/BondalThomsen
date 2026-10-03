module

public import BondalThomsen.Toric.Frobenius.MultiplicationResidueGluing
public import BondalThomsen.Collection.BondalThomsenSummandRegrouping
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

local instance residueSplittingSchemeFiniteBiproducts (source : Scheme) :
    HasFiniteBiproducts source.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance residueSplittingSheafFiniteBiproducts
    {Site : Type*} [Category Site] {Topology : GrothendieckTopology Site}
    (ringSheaf : Sheaf Topology RingCat) : HasFiniteBiproducts (SheafOfModules.{0} ringSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

noncomputable def basisUnitBiproductIso {Ring Carrier Index : Type}
    [CommRing Ring] [AddCommGroup Carrier] [Module Ring Carrier] [Fintype Index]
    (basis : Module.Basis Index Ring Carrier) :
    (⨁ fun _ : Index => ModuleCat.of Ring Ring) ≅ ModuleCat.of Ring Carrier :=
  ModuleCat.biproductIsoPi (fun _ : Index => ModuleCat.of Ring Ring) ≪≫
    ((Finsupp.linearEquivFunOnFinite Ring Ring Index).symm.trans basis.repr.symm).toModuleIso

theorem basisUnitBiproductIso_summand {Ring Carrier Index : Type}
    [CommRing Ring] [AddCommGroup Carrier] [Module Ring Carrier] [Fintype Index]
    (basis : Module.Basis Index Ring Carrier) (index : Index) :
    biproduct.ι (fun _ : Index => ModuleCat.of Ring Ring) index ≫
      (basisUnitBiproductIso basis).hom = ModuleCat.ofHom (basisResidueInclusion basis index) := by
  classical
  have pi_single : biproduct.ι (fun _ : Index => ModuleCat.of Ring Ring) index ≫
      (ModuleCat.biproductIsoPi (fun _ : Index => ModuleCat.of Ring Ring)).hom =
      ModuleCat.ofHom (LinearMap.single Ring (fun _ : Index => Ring) index) := by
    apply (cancel_mono (ModuleCat.biproductIsoPi
      (fun _ : Index => ModuleCat.of Ring Ring)).inv).mp
    apply biproduct.hom_ext
    intro other
    rw [Category.assoc (biproduct.ι _ index), Iso.hom_inv_id, Category.comp_id]
    rw [Category.assoc, ModuleCat.biproductIsoPi_inv_comp_π]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro coefficient
    by_cases equal : index = other
    · subst other
      simp
    · simp [equal]
  simp only [basisUnitBiproductIso, Iso.trans_hom, ← Category.assoc, pi_single]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change basis.repr.symm
    ((Finsupp.linearEquivFunOnFinite Ring Ring Index).symm (Pi.single index coefficient)) = _
  rw [Finsupp.linearEquivFunOnFinite_symm_single]
  rfl

noncomputable def affineBasisUnitBiproductIso {Source Target : CommRingCat.{0}}
    (ring_map : Target ⟶ Source) {Index : Type} [Fintype Index]
    (basis : letI := Module.compHom Source ring_map.hom;
      Module.Basis Index Target Source) :
    (⨁ fun _ : Index => (SheafOfModules.unit (Spec Target).ringCatSheaf : (Spec Target).Modules)) ≅
      (Scheme.Modules.pushforward (Spec.map ring_map)).obj
        (SheafOfModules.unit (Spec Source).ringCatSheaf) := by
  letI := Module.compHom Source ring_map.hom
  exact biproduct.mapIso (fun _ => tildeSelf.symm) ≪≫
    ((tilde.functor Target).mapBiproduct (fun _ : Index => ModuleCat.of Target Target)).symm ≪≫
    (tilde.functor Target).mapIso (basisUnitBiproductIso basis) ≪≫
    affinePushforwardStructureTildeIso ring_map

theorem affineBasisUnitBiproductIso_summand {Source Target : CommRingCat.{0}}
    (ring_map : Target ⟶ Source) {Index : Type} [Fintype Index]
    (basis : letI := Module.compHom Source ring_map.hom;
      Module.Basis Index Target Source) (index : Index) :
    biproduct.ι (fun _ : Index =>
      (SheafOfModules.unit (Spec Target).ringCatSheaf : (Spec Target).Modules)) index ≫
      (affineBasisUnitBiproductIso ring_map basis).hom =
      (affineResidueSheafUnitIso ring_map basis index).hom ≫
        affineResidueSheafInclusion ring_map basis index := by
  let := Module.compHom Source ring_map.hom
  rw [affineResidueSheaf_frame_inclusion]
  simp only [affineBasisUnitBiproductIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, biproduct.mapIso_hom]
  rw [biproduct.ι_map_assoc]
  rw [← Category.assoc _ ((tilde.functor Target).mapBiproduct _).inv,
    Functor.mapBiproduct_inv, biproduct.ι_desc]
  rw [← Functor.map_comp_assoc, basisUnitBiproductIso_summand]

end BondalThomsen

namespace TauCeti.Toric.Fan

local instance coneResidueSplittingSheafFiniteBiproducts
    {Site : Type*} [Category Site] {Topology : GrothendieckTopology Site}
    (ringSheaf : Sheaf Topology RingCat) : HasFiniteBiproducts (SheafOfModules.{0} ringSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

local instance coneResidueSplittingSchemeFiniteBiproducts (source : Scheme) :
    HasFiniteBiproducts source.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

@[simp] theorem residueIntegralCharacter_basis {dimension degree : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (residue : Fin dimension → Fin degree) (index : Fin dimension) :
    residueIntegralCharacter basis residue (basis index) = (residue index).val := by
  simp [residueIntegralCharacter]

theorem residueIntegralCharacter_normalizedResidue {dimension degree : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (positive : 0 < degree)
    (character : Lattice →+ ℤ) :
    residueIntegralCharacter basis (normalizedResidue basis positive character) =
      normalizedResidueCharacter basis degree character := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  change residueIntegralCharacter basis (normalizedResidue basis positive character) (basis index) =
    (character - degree • residueFloorCharacter basis degree character) (basis index)
  simp only [residueIntegralCharacter_basis,
    normalizedResidue, AddMonoidHom.sub_apply,
    AddMonoidHom.smul_apply, nsmul_eq_mul, residueFloorCharacter_basis]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg (character (basis index))
    (by exact_mod_cast positive.ne'))]
  exact Int.emod_def _ _

@[simp] theorem normalizedResidue_integral {dimension degree : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (positive : 0 < degree)
    (residue : Fin dimension → Fin degree) :
    normalizedResidue basis positive (residueIntegralCharacter basis residue) = residue := by
  funext index
  apply Fin.ext
  simp only [normalizedResidue, residueIntegralCharacter_basis]
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast (residue index).isLt)]
  simp

theorem normalizedResidue_sub_multiple {dimension degree : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (positive : 0 < degree)
    (character correction : Lattice →+ ℤ) :
    normalizedResidue basis positive (character - degree • correction) =
      normalizedResidue basis positive character := by
  funext index
  apply Fin.ext
  simp only [normalizedResidue, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply,
    nsmul_eq_mul, Int.sub_mul_emod_self_left]

noncomputable def residueBasisChangeEquiv {globalDimension chartDimension degree : ℕ}
    (globalBasis : Module.Basis (Fin globalDimension) ℤ Lattice)
    (chartBasis : Module.Basis (Fin chartDimension) ℤ Lattice) (positive : 0 < degree) :
    (Fin globalDimension → Fin degree) ≃ (Fin chartDimension → Fin degree) where
  toFun residue := normalizedResidue chartBasis positive
    (residueIntegralCharacter globalBasis residue)
  invFun residue := normalizedResidue globalBasis positive
    (residueIntegralCharacter chartBasis residue)
  left_inv := by
    intro residue
    dsimp only
    rw [residueIntegralCharacter_normalizedResidue]
    simp only [normalizedResidueCharacter, normalizedResidue_sub_multiple,
      normalizedResidue_integral]
  right_inv := by
    intro residue
    dsimp only
    rw [residueIntegralCharacter_normalizedResidue]
    simp only [normalizedResidueCharacter, normalizedResidue_sub_multiple,
      normalizedResidue_integral]

noncomputable def residueLineBundleBiproduct
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular) (degree : ℕ) :
    (fan.algebraicRealization 𝕜 regular).Modules :=
  ⨁ fun residue : Fin (Module.finrank ℤ Lattice) → Fin degree =>
    (fan.floorDivisorInvertibleSheaf 𝕜 complete regular
      ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp
        (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue))).obj

noncomputable def basisConeGlobalResidueBiproductIso (fan : Fan embedding)
    {globalDimension chartDimension degree : ℕ}
    (globalBasis : Module.Basis (Fin globalDimension) ℤ Lattice)
    (chartBasis : Module.Basis (Fin chartDimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis chartBasis) (positive : 0 < degree) :
    (⨁ fun _ : Fin globalDimension → Fin degree =>
      (SheafOfModules.unit (fan.affineToricChart 𝕜 ⟨_, coneBasis⟩).ringCatSheaf :
        (fan.affineToricChart 𝕜 ⟨_, coneBasis⟩).Modules)) ≅
      (Scheme.Modules.pushforward (fan.toricMultiplicationChart 𝕜 degree ⟨_, coneBasis⟩)).obj
        (SheafOfModules.unit (fan.affineToricChart 𝕜 ⟨_, coneBasis⟩).ringCatSheaf) := by
  classical
  exact biproduct.reindex (residueBasisChangeEquiv globalBasis chartBasis positive)
      (fun _ : Fin chartDimension → Fin degree =>
        (SheafOfModules.unit (fan.affineToricChart 𝕜 ⟨_, coneBasis⟩).ringCatSheaf :
          (fan.affineToricChart 𝕜 ⟨_, coneBasis⟩).Modules)) ≪≫
    BondalThomsen.affineBasisUnitBiproductIso
      (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree _).toRingHom)
      (fan.basisConeMultiplicationBasis 𝕜 positive chartBasis)

omit [FiniteDimensional ℝ Ambient] in
theorem basisConeGlobalResidueBiproductIso_summand (fan : Fan embedding)
    {globalDimension chartDimension degree : ℕ}
    (globalBasis : Module.Basis (Fin globalDimension) ℤ Lattice)
    (chartBasis : Module.Basis (Fin chartDimension) ℤ Lattice)
    (coneBasis : fan.IsConeBasis chartBasis) (positive : 0 < degree)
    (residue : Fin globalDimension → Fin degree) :
    biproduct.ι (fun _ : Fin globalDimension → Fin degree =>
      (SheafOfModules.unit (fan.affineToricChart 𝕜 ⟨_, coneBasis⟩).ringCatSheaf :
        (fan.affineToricChart 𝕜 ⟨_, coneBasis⟩).Modules)) residue ≫
      (fan.basisConeGlobalResidueBiproductIso 𝕜 globalBasis chartBasis coneBasis positive).hom =
      (fan.basisConeResidueSheafUnitIso 𝕜 chartBasis coneBasis positive
        (residueIntegralCharacter globalBasis residue)).hom ≫
        fan.basisConeResidueSheafInclusion 𝕜 chartBasis coneBasis positive
          (residueIntegralCharacter globalBasis residue) := by
  classical
  simp only [basisConeGlobalResidueBiproductIso, Iso.trans_hom, biproduct.reindex_hom,
    biproduct.ι_desc_assoc]
  exact BondalThomsen.affineBasisUnitBiproductIso_summand
    (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree _).toRingHom)
    (fan.basisConeMultiplicationBasis 𝕜 positive chartBasis)
    (normalizedResidue chartBasis positive (residueIntegralCharacter globalBasis residue))

noncomputable def residueLineBundleBiproductMap
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) :
    fan.residueLineBundleBiproduct 𝕜 complete regular degree ⟶
      fan.toricMultiplicationPushforward 𝕜 regular degree :=
  biproduct.desc (fun residue => fan.residueFloorGlobalInclusion 𝕜 complete regular positive
    (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue))

theorem residueLineBundleBiproductMap_summand
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree)
    (residue : Fin (Module.finrank ℤ Lattice) → Fin degree) :
    biproduct.ι (fun residue : Fin (Module.finrank ℤ Lattice) → Fin degree =>
      (fan.floorDivisorInvertibleSheaf 𝕜 complete regular
        ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp
          (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue))).obj) residue ≫
      fan.residueLineBundleBiproductMap 𝕜 complete regular positive =
      fan.residueFloorGlobalInclusion 𝕜 complete regular positive
        (residueIntegralCharacter (Module.finBasis ℤ Lattice) residue) := by
  classical
  exact biproduct.ι_desc _ _

end TauCeti.Toric.Fan
