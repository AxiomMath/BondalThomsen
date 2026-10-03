module

public import BondalThomsen.Toric.Frobenius.MultiplicationFiniteLocallyFree
public import BondalThomsen.Collection.BondalThomsenCommonDenominator
public import BondalThomsen.Toric.Divisor.DivisorLineBundle

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

variable {Ring Index Carrier : Type} [CommRing Ring] [AddCommGroup Carrier]
    [Module Ring Carrier]

noncomputable def basisResidueInclusion (basis : Module.Basis Index Ring Carrier)
    (residue : Index) : Ring →ₗ[Ring] Carrier :=
  basis.repr.symm.toLinearMap.comp (Finsupp.lsingle residue)

theorem basisResidueInclusion_injective (basis : Module.Basis Index Ring Carrier)
    (residue : Index) : Function.Injective (basisResidueInclusion basis residue) :=
  basis.repr.symm.injective.comp (Finsupp.single_injective residue)

noncomputable def basisResidueSubmodule (basis : Module.Basis Index Ring Carrier)
    (residue : Index) : Submodule Ring Carrier :=
  (basisResidueInclusion basis residue).range

noncomputable def basisResidueEquiv (basis : Module.Basis Index Ring Carrier)
    (residue : Index) : Ring ≃ₗ[Ring] basisResidueSubmodule basis residue :=
  LinearEquiv.ofInjective (basisResidueInclusion basis residue)
    (basisResidueInclusion_injective basis residue)

noncomputable def basisResidueRetraction (basis : Module.Basis Index Ring Carrier)
    (residue : Index) : Carrier →ₗ[Ring] basisResidueSubmodule basis residue :=
  (basisResidueEquiv basis residue).toLinearMap.comp
    ((Finsupp.lapply residue).comp basis.repr.toLinearMap)

theorem basisResidueRetraction_subtype (basis : Module.Basis Index Ring Carrier)
    (residue : Index) :
    (basisResidueRetraction basis residue).comp
      (basisResidueSubmodule basis residue).subtype = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro element
  obtain ⟨scalar, rfl⟩ := (basisResidueEquiv basis residue).surjective element
  apply Subtype.ext
  change basisResidueInclusion basis residue
      ((basis.repr (basisResidueInclusion basis residue scalar)) residue) =
    basisResidueInclusion basis residue scalar
  simp [basisResidueInclusion]

noncomputable def affineResidueSheaf {Source Target : CommRingCat}
    (ring_map : Target ⟶ Source) {Index : Type}
    (basis : letI := Module.compHom Source ring_map.hom;
      Module.Basis Index Target Source) (residue : Index) : (Spec Target).Modules := by
  letI := Module.compHom Source ring_map.hom
  exact tilde (ModuleCat.of Target (basisResidueSubmodule basis residue))

noncomputable def affineResidueSheafUnitIso {Source Target : CommRingCat}
    (ring_map : Target ⟶ Source) {Index : Type}
    (basis : letI := Module.compHom Source ring_map.hom;
      Module.Basis Index Target Source) (residue : Index) :
    SheafOfModules.unit (Spec Target).ringCatSheaf ≅
      affineResidueSheaf ring_map basis residue := by
  letI := Module.compHom Source ring_map.hom
  exact tildeSelf.symm ≪≫ (tilde.functor Target).mapIso
    (basisResidueEquiv basis residue).toModuleIso

noncomputable def affinePushforwardStructureTildeIso {Source Target : CommRingCat}
    (ring_map : Target ⟶ Source) :
    letI := Module.compHom Source ring_map.hom
    tilde (ModuleCat.of Target Source) ≅
      (Scheme.Modules.pushforward (Spec.map ring_map)).obj
        (SheafOfModules.unit (Spec Source).ringCatSheaf) := by
  letI := Module.compHom Source ring_map.hom
  let pushforward := (Scheme.Modules.pushforward (Spec.map ring_map)).obj
    (SheafOfModules.unit (Spec Source).ringCatSheaf)
  letI : IsIso pushforward.fromTildeΓ := isIso_fromTildeΓ_pushforward ring_map _
  change tilde (ModuleCat.of Target Source) ≅ pushforward
  exact (tilde.functor Target).mapIso
      (affinePushforwardStructureSectionsEquiv ring_map).symm.toModuleIso ≪≫
    asIso pushforward.fromTildeΓ

noncomputable def affineResidueSheafInclusion {Source Target : CommRingCat}
    (ring_map : Target ⟶ Source) {Index : Type}
    (basis : letI := Module.compHom Source ring_map.hom;
      Module.Basis Index Target Source) (residue : Index) :
    affineResidueSheaf ring_map basis residue ⟶
      (Scheme.Modules.pushforward (Spec.map ring_map)).obj
        (SheafOfModules.unit (Spec Source).ringCatSheaf) := by
  letI := Module.compHom Source ring_map.hom
  exact (tilde.functor Target).map
      (ModuleCat.ofHom (basisResidueSubmodule basis residue).subtype) ≫
    (affinePushforwardStructureTildeIso ring_map).hom

noncomputable def affineResidueSheafRetraction {Source Target : CommRingCat}
    (ring_map : Target ⟶ Source) {Index : Type}
    (basis : letI := Module.compHom Source ring_map.hom;
      Module.Basis Index Target Source) (residue : Index) :
    (Scheme.Modules.pushforward (Spec.map ring_map)).obj
        (SheafOfModules.unit (Spec Source).ringCatSheaf) ⟶
      affineResidueSheaf ring_map basis residue := by
  letI := Module.compHom Source ring_map.hom
  exact (affinePushforwardStructureTildeIso ring_map).inv ≫
    (tilde.functor Target).map (ModuleCat.ofHom (basisResidueRetraction basis residue))

theorem affineResidueSheafInclusion_retraction {Source Target : CommRingCat}
    (ring_map : Target ⟶ Source) {Index : Type}
    (basis : letI := Module.compHom Source ring_map.hom;
      Module.Basis Index Target Source) (residue : Index) :
    affineResidueSheafInclusion ring_map basis residue ≫
      affineResidueSheafRetraction ring_map basis residue = 𝟙 _ := by
  let := Module.compHom Source ring_map.hom
  simp only [affineResidueSheafInclusion, affineResidueSheafRetraction,
    Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp]
  have composite : ModuleCat.ofHom (basisResidueSubmodule basis residue).subtype ≫
      ModuleCat.ofHom (basisResidueRetraction basis residue) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    exact basisResidueRetraction_subtype basis residue
  rw [composite]
  exact (tilde.functor Target).map_id _

instance affineResidueSheafInclusion_mono {Source Target : CommRingCat}
    (ring_map : Target ⟶ Source) {Index : Type}
    (basis : letI := Module.compHom Source ring_map.hom;
      Module.Basis Index Target Source) (residue : Index) :
    Mono (affineResidueSheafInclusion ring_map basis residue) :=
  mono_of_mono_fac (affineResidueSheafInclusion_retraction ring_map basis residue)

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def residueFloorCharacter {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (degree : ℕ)
    (character : Lattice →+ ℤ) : Lattice →+ ℤ :=
  (basis.constr ℤ (fun index => character (basis index) / (degree : ℤ))).toAddMonoidHom

noncomputable def normalizedResidue {dimension degree : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (positive : 0 < degree)
    (character : Lattice →+ ℤ) : Fin dimension → Fin degree := fun index =>
  ⟨(character (basis index) % (degree : ℤ)).toNat,
    (Int.toNat_lt (Int.emod_nonneg _ (by exact_mod_cast positive.ne'))).mpr
      (Int.emod_lt_of_pos _ (by exact_mod_cast positive))⟩

noncomputable def normalizedResidueCharacter {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (degree : ℕ)
    (character : Lattice →+ ℤ) : Lattice →+ ℤ :=
  character - degree • residueFloorCharacter basis degree character

@[simp] theorem residueFloorCharacter_basis {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (degree : ℕ)
    (character : Lattice →+ ℤ) (index : Fin dimension) :
    residueFloorCharacter basis degree character (basis index) =
      character (basis index) / (degree : ℤ) := by
  simp [residueFloorCharacter]

@[simp] theorem normalizedResidueCharacter_basis {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (degree : ℕ)
    (character : Lattice →+ ℤ) (index : Fin dimension) :
    normalizedResidueCharacter basis degree character (basis index) =
      character (basis index) % (degree : ℤ) := by
  simp only [normalizedResidueCharacter, AddMonoidHom.sub_apply,
    AddMonoidHom.smul_apply, residueFloorCharacter_basis, nsmul_eq_mul]
  have division := Int.emod_add_ediv_mul (character (basis index)) (degree : ℤ)
  nlinarith

theorem normalizedResidueCharacter_mem_dualSemigroup (fan : Fan embedding)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (positive : 0 < degree) (character : Lattice →+ ℤ) :
    normalizedResidueCharacter basis degree character ∈ dualSemigroup fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) := by
  apply (fan.mem_dualSemigroup_basisCone_iff basis _).mpr
  intro index
  rw [normalizedResidueCharacter_basis]
  exact Int.emod_nonneg _ (by exact_mod_cast positive.ne')

theorem floorRayDivisor_integral_scaled (fan : Fan embedding) (degree : ℕ)
    (character : Lattice →+ ℤ) (ray : fan.Ray) :
    fan.floorRayDivisor ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character) ray =
      character ray.val / (degree : ℤ) := by
  simp only [floorRayDivisor_apply, AddMonoidHom.smul_apply, AddMonoidHom.comp_apply,
    smul_eq_mul]
  change ⌊(degree : ℚ)⁻¹ * (character ray.val : ℚ)⌋ = _
  rw [mul_comm, ← div_eq_mul_inv, Int.floor_div_natCast]
  simp

theorem coneDivisorCharacter_floor_eq (fan : Fan embedding) {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (degree : ℕ) (character : Lattice →+ ℤ) :
    fan.coneDivisorCharacter basis cone_basis
      (fan.floorRayDivisor ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character)) =
      -residueFloorCharacter basis degree character := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro index
  change fan.coneDivisorCharacter basis cone_basis
      (fan.floorRayDivisor ((degree : ℚ)⁻¹ • (Int.castAddHom ℚ).comp character))
      (basis index) = -residueFloorCharacter basis degree character (basis index)
  rw [coneDivisorCharacter_basis, floorRayDivisor_integral_scaled]
  simp only [basisRay_val, residueFloorCharacter_basis]

theorem basisConeMultiplicationBasis_coordinate (fan : Fan embedding)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (positive : 0 < degree) (residue : Fin dimension → Fin degree) :
    fan.basisConeCoordinateRingEquiv 𝕜 basis
      (fan.basisConeMultiplicationBasis 𝕜 positive basis residue) =
      MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun index => (residue index).val)) 1 := by
  let : NeZero degree := ⟨positive.ne'⟩
  simp only [basisConeMultiplicationBasis, Module.Basis.mapCoeffs_apply,
    Module.Basis.map_apply]
  change (fan.basisConeCoordinateRingEquiv 𝕜 basis)
    ((fan.basisConeCoordinateRingEquiv 𝕜 basis).symm
      ((BondalThomsen.multiplicationPolynomialBasis degree 𝕜) residue)) = _
  rw [AlgEquiv.apply_symm_apply]
  simp only [BondalThomsen.multiplicationPolynomialBasis, Module.Basis.coe_ofRepr]
  change (BondalThomsen.multiplicationPolynomialResidueEquiv degree 𝕜).symm
    (Finsupp.single residue 1) = _
  rw [BondalThomsen.multiplicationPolynomialResidueEquiv_symm_single]
  simp

noncomputable def normalizedResidueMonomial (fan : Fan embedding)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (positive : 0 < degree) (character : Lattice →+ ℤ) :
    affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) :=
  MonoidAlgebra.single (Multiplicative.ofAdd
    ⟨normalizedResidueCharacter basis degree character,
      fan.normalizedResidueCharacter_mem_dualSemigroup basis positive character⟩) 1

theorem normalizedResidueMonomial_coordinate (fan : Fan embedding)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (positive : 0 < degree) (character : Lattice →+ ℤ) :
    fan.basisConeCoordinateRingEquiv 𝕜 basis
      (fan.normalizedResidueMonomial 𝕜 basis positive character) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm
        (fun index => (normalizedResidue basis positive character index).val)) 1 := by
  classical
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv 𝕜 𝕜 (Fin dimension →₀ ℕ)).injective
  simp only [basisConeCoordinateRingEquiv, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply, normalizedResidueMonomial,
    MonoidAlgebra.domCongr_single]
  change MonoidAlgebra.single
      ((fan.basisConeDualSemigroupEquiv basis).toMultiplicative
        (Multiplicative.ofAdd ⟨normalizedResidueCharacter basis degree character, _⟩)) 1 =
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv 𝕜 𝕜 (Fin dimension →₀ ℕ))
      (AddMonoidAlgebra.single (Finsupp.equivFunOnFinite.symm
        (fun index => (normalizedResidue basis positive character index).val)) 1)
  rw [AddMonoidAlgebra.toMultiplicativeAlgEquiv_single,
    AddEquiv.toMultiplicative_apply_apply]
  change MonoidAlgebra.single (Multiplicative.ofAdd
    ((fan.basisConeDualSemigroupEquiv basis)
      ⟨normalizedResidueCharacter basis degree character, _⟩)) (1 : 𝕜) =
    MonoidAlgebra.single (Multiplicative.ofAdd
      (Finsupp.equivFunOnFinite.symm
        (fun index => (normalizedResidue basis positive character index).val))) (1 : 𝕜)
  congr 2
  apply Finsupp.ext
  intro index
  simp [basisConeDualSemigroupEquiv, normalizedResidue, normalizedResidueCharacter_basis]

theorem basisConeMultiplicationBasis_normalized_eq (fan : Fan embedding)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (positive : 0 < degree) (character : Lattice →+ ℤ) :
    fan.basisConeMultiplicationBasis 𝕜 positive basis
        (normalizedResidue basis positive character) =
      fan.normalizedResidueMonomial 𝕜 basis positive character := by
  apply (fan.basisConeCoordinateRingEquiv 𝕜 basis).injective
  rw [fan.basisConeMultiplicationBasis_coordinate 𝕜,
    fan.normalizedResidueMonomial_coordinate 𝕜]

theorem basisConeResidueInclusion_apply (fan : Fan embedding)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (positive : 0 < degree) (character : Lattice →+ ℤ)
    (coefficient : affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :
    letI := Module.compHom
      (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
      (fan.toricMultiplicationRing 𝕜 degree
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))).toRingHom
    BondalThomsen.basisResidueInclusion (fan.basisConeMultiplicationBasis 𝕜 positive basis)
        (normalizedResidue basis positive character) coefficient =
      fan.toricMultiplicationRing 𝕜 degree _ coefficient *
        fan.normalizedResidueMonomial 𝕜 basis positive character := by
  let := Module.compHom
    (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
      (fan.toricMultiplicationRing 𝕜 degree
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))).toRingHom
  change (fan.basisConeMultiplicationBasis 𝕜 positive basis).repr.symm
    (Finsupp.single (normalizedResidue basis positive character) coefficient) = _
  rw [Module.Basis.repr_symm_single, fan.basisConeMultiplicationBasis_normalized_eq 𝕜]
  rfl

noncomputable def basisConeResidueSheaf (fan : Fan embedding)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (positive : 0 < degree)
    (character : Lattice →+ ℤ) : (fan.affineToricChart 𝕜 ⟨_, cone_basis⟩).Modules :=
  BondalThomsen.affineResidueSheaf
    (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree _).toRingHom)
    (fan.basisConeMultiplicationBasis 𝕜 positive basis)
    (normalizedResidue basis positive character)

noncomputable def basisConeResidueSheafUnitIso (fan : Fan embedding)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (positive : 0 < degree)
    (character : Lattice →+ ℤ) :
    SheafOfModules.unit (fan.affineToricChart 𝕜 ⟨_, cone_basis⟩).ringCatSheaf ≅
      fan.basisConeResidueSheaf 𝕜 basis cone_basis positive character :=
  BondalThomsen.affineResidueSheafUnitIso
    (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree _).toRingHom)
    (fan.basisConeMultiplicationBasis 𝕜 positive basis)
    (normalizedResidue basis positive character)

noncomputable def basisConeResidueSheafInclusion (fan : Fan embedding)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (positive : 0 < degree)
    (character : Lattice →+ ℤ) :
    fan.basisConeResidueSheaf 𝕜 basis cone_basis positive character ⟶
      (Scheme.Modules.pushforward (fan.toricMultiplicationChart 𝕜 degree ⟨_, cone_basis⟩)).obj
        (SheafOfModules.unit (fan.affineToricChart 𝕜 ⟨_, cone_basis⟩).ringCatSheaf) :=
  BondalThomsen.affineResidueSheafInclusion
    (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree _).toRingHom)
    (fan.basisConeMultiplicationBasis 𝕜 positive basis)
    (normalizedResidue basis positive character)

variable {𝕜} in
instance basisConeResidueSheafInclusion_mono (fan : Fan embedding)
    {dimension degree : ℕ} (basis : Module.Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (positive : 0 < degree)
    (character : Lattice →+ ℤ) :
    Mono (fan.basisConeResidueSheafInclusion 𝕜 basis cone_basis positive character) :=
  BondalThomsen.affineResidueSheafInclusion_mono
    (CommRingCat.ofHom (fan.toricMultiplicationRing 𝕜 degree _).toRingHom)
    (fan.basisConeMultiplicationBasis 𝕜 positive basis)
    (normalizedResidue basis positive character)

end TauCeti.Toric.Fan
