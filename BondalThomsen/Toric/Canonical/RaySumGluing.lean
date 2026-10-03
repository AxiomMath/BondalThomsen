module

public import BondalThomsen.Toric.Canonical.FanChartRestriction
public import BondalThomsen.Toric.Divisor.LineBundleGluing
public import BondalThomsen.DeepFan.SupportCriterion

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace Multiplicative

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CanonicalRaySum

universe baseUniverse ringUniverse

variable {Coefficient Functions Characters : Type*}
    [CommRing Coefficient] [CommRing Functions] [Algebra Coefficient Functions]
    [AddCommGroup Characters] {dimension : ℕ}

noncomputable def logarithmicCharacterSemilinear
    (characters : Multiplicative Characters →* Functionsˣ) :
    Characters →ₛₗ[Int.castRingHom Functions] KaehlerDifferential Coefficient Functions :=
  { (LogDifferential.characterMap (Coefficient := Coefficient) characters) with
    map_smul' := fun scalar character => by
      change LogDifferential.characterMap characters (scalar • character) = _
      rw [map_zsmul]
      exact (Int.cast_smul_eq_zsmul Functions scalar _).symm }

theorem logarithmicCharacterWedge_transition
    (characters : Multiplicative Characters →* Functionsˣ)
    (first second : Basis (Fin dimension) ℤ Characters) :
    exteriorPower.ιMulti Functions dimension
        (fun index => LogDifferential.ofUnit (Coefficient := Coefficient)
          (characters (ofAdd (second index)))) =
      (first.det second : Functions) • exteriorPower.ιMulti Functions dimension
        (fun index => LogDifferential.ofUnit (Coefficient := Coefficient)
          (characters (ofAdd (first index)))) := by
  let differential := logarithmicCharacterSemilinear (Coefficient := Coefficient) characters
  have transported := congrArg
    (SemilinearExterior.map dimension (Int.castRingHom Functions) differential)
    (TopExterior.wedge_eq_det_smul first second)
  rw [map_smulₛₗ, SemilinearExterior.map_wedge, SemilinearExterior.map_wedge] at transported
  exact transported

theorem characterUnit_prod (characters : Multiplicative Characters →* Functionsˣ)
    (vectors : Fin dimension → Characters) :
    (∏ index, characters (ofAdd (vectors index))) = characters (ofAdd (∑ index, vectors index)) := by
  rw [← map_prod]
  simp only [← ofAdd_sum]

noncomputable def integralDeterminantUnit
    (first second : Basis (Fin dimension) ℤ Characters) : ℤˣ where
  val := first.det second
  inv := second.det first
  val_inv := by rw [Basis.det_mul_det, Basis.det_self]
  inv_val := by rw [Basis.det_mul_det, Basis.det_self]

noncomputable def coordinateTopTransitionUnit
    (characters : Multiplicative Characters →* Functionsˣ)
    (first second : Basis (Fin dimension) ℤ Characters) : Functionsˣ :=
  Units.map (Int.castRingHom Functions).toMonoidHom (integralDeterminantUnit first second) *
    characters (ofAdd ((∑ index, second index) - ∑ index, first index))

theorem coordinateTopTransitionUnit_mul_prod
    (characters : Multiplicative Characters →* Functionsˣ)
    (first second : Basis (Fin dimension) ℤ Characters) :
    (coordinateTopTransitionUnit characters first second : Functions) *
        (∏ index, (characters (ofAdd (first index))).val) =
      (first.det second : Functions) * ∏ index, (characters (ofAdd (second index))).val := by
  have products :
      characters (ofAdd ((∑ index, second index) - ∑ index, first index)) *
          (∏ index, characters (ofAdd (first index))) =
        ∏ index, characters (ofAdd (second index)) := by
    rw [characterUnit_prod, characterUnit_prod, ← map_mul, ← ofAdd_add]
    congr 2
    abel
  have values := congrArg Units.val products
  change (first.det second : Functions) *
      (characters (ofAdd ((∑ index, second index) - ∑ index, first index))).val *
        (∏ index, (characters (ofAdd (first index))).val) = _
  rw [mul_assoc]
  exact congrArg (fun scalar => (first.det second : Functions) * scalar)
    (by simpa only [Units.val_mul, Units.coe_prod] using values)

theorem coordinateWedge_transition
    (characters : Multiplicative Characters →* Functionsˣ)
    (first second : Basis (Fin dimension) ℤ Characters) :
    exteriorPower.ιMulti Functions dimension
        (fun index => KaehlerDifferential.D Coefficient Functions
          (characters (ofAdd (second index))).val) =
      (coordinateTopTransitionUnit characters first second : Functions) •
        exteriorPower.ιMulti Functions dimension
          (fun index => KaehlerDifferential.D Coefficient Functions
            (characters (ofAdd (first index))).val) := by
  rw [LogDifferential.wedge_eq_prod_smul, LogDifferential.wedge_eq_prod_smul,
    logarithmicCharacterWedge_transition characters first second, smul_smul, smul_smul,
    coordinateTopTransitionUnit_mul_prod]
  rw [mul_comm]

theorem topExteriorMap_trivialization
    {SourceRing TargetRing SourceModule TargetModule : Type*}
    [CommRing SourceRing] [CommRing TargetRing]
    [AddCommGroup SourceModule] [Module SourceRing SourceModule]
    [AddCommGroup TargetModule] [Module TargetRing TargetModule]
    (coefficientMap : SourceRing →+* TargetRing)
    (moduleMap : SourceModule →ₛₗ[coefficientMap] TargetModule)
    (sourceBasis : Basis (Fin dimension) SourceRing SourceModule)
    (targetBasis : Basis (Fin dimension) TargetRing TargetModule)
    (basis_map : ∀ index, moduleMap (sourceBasis index) = targetBasis index)
    (vector : ⋀[SourceRing]^dimension SourceModule) :
    TopExterior.trivialization targetBasis
        (SemilinearExterior.map dimension coefficientMap moduleMap vector) =
      coefficientMap (TopExterior.trivialization sourceBasis vector) := by
  obtain ⟨scalar, rfl⟩ := (TopExterior.trivialization sourceBasis).symm.surjective vector
  change TopExterior.trivialization targetBasis
      (SemilinearExterior.map dimension coefficientMap moduleMap
        (scalar • exteriorPower.ιMulti SourceRing dimension sourceBasis)) = _
  rw [map_smulₛₗ, SemilinearExterior.map_wedge]
  have mappedBasis : moduleMap ∘ sourceBasis = targetBasis := funext basis_map
  rw [mappedBasis]
  rw [map_smul, TopExterior.trivialization_frame, smul_eq_mul, mul_one]
  rw [LinearEquiv.apply_symm_apply]

theorem topExteriorMap_injective
    {SourceRing TargetRing SourceModule TargetModule : Type*}
    [CommRing SourceRing] [CommRing TargetRing]
    [AddCommGroup SourceModule] [Module SourceRing SourceModule]
    [AddCommGroup TargetModule] [Module TargetRing TargetModule]
    (coefficientMap : SourceRing →+* TargetRing)
    (moduleMap : SourceModule →ₛₗ[coefficientMap] TargetModule)
    (sourceBasis : Basis (Fin dimension) SourceRing SourceModule)
    (targetBasis : Basis (Fin dimension) TargetRing TargetModule)
    (basis_map : ∀ index, moduleMap (sourceBasis index) = targetBasis index)
    (coefficient_injective : Function.Injective coefficientMap) :
    Function.Injective (SemilinearExterior.map dimension coefficientMap moduleMap) := by
  intro first second same
  apply (TopExterior.trivialization sourceBasis).injective
  apply coefficient_injective
  simpa only [topExteriorMap_trivialization coefficientMap moduleMap sourceBasis targetBasis
    basis_map] using congrArg (TopExterior.trivialization targetBasis) same

theorem differentialTopMap_injective_of_localization
    {BaseRing : Type baseUniverse} {SourceRing TargetRing : Type ringUniverse}
    [CommRing BaseRing] [CommRing SourceRing] [CommRing TargetRing]
    [Algebra BaseRing SourceRing] [Algebra BaseRing TargetRing]
    (restriction : SourceRing →ₐ[BaseRing] TargetRing)
    (basis : Basis (Fin dimension) SourceRing (KaehlerDifferential BaseRing SourceRing))
    (localizer : SourceRing)
    (localized : letI := restriction.toRingHom.toAlgebra;
      IsLocalization.Away localizer TargetRing)
    (restriction_injective : Function.Injective restriction) :
    Function.Injective (SemilinearExterior.map dimension restriction.toRingHom
      (DifferentialCoordinates.map restriction)) := by
  let := restriction.toRingHom.toAlgebra
  let : IsScalarTower BaseRing SourceRing TargetRing :=
    IsScalarTower.of_algebraMap_eq' restriction.comp_algebraMap.symm
  let := localized
  let targetBasis := Module.Basis.ofIsLocalizedModule TargetRing
    (Submonoid.powers localizer) (KaehlerDifferential.map BaseRing BaseRing SourceRing TargetRing)
    basis
  exact topExteriorMap_injective restriction.toRingHom
    (DifferentialCoordinates.map restriction) basis targetBasis
    (fun index => (Module.Basis.ofIsLocalizedModule_apply _ _ _ _ index).symm)
    restriction_injective

theorem orientationNormalizedForm_transition
    {FormModule : Type*} [AddCommGroup FormModule] [Module Functions FormModule]
    (reference first second : Basis (Fin dimension) ℤ Characters)
    (monomial : Functionsˣ) (firstForm secondForm : FormModule)
    (transition : secondForm =
      ((Units.map (Int.castRingHom Functions).toMonoidHom
        (integralDeterminantUnit first second) * monomial : Functionsˣ) : Functions) • firstForm) :
    ((Units.map (Int.castRingHom Functions).toMonoidHom
        (integralDeterminantUnit reference second))⁻¹ : Functionsˣ) • secondForm =
      (monomial : Functions) •
        (((Units.map (Int.castRingHom Functions).toMonoidHom
          (integralDeterminantUnit reference first))⁻¹ : Functionsˣ) • firstForm) := by
  have determinants : integralDeterminantUnit reference first * integralDeterminantUnit first second =
      integralDeterminantUnit reference second := by
    apply Units.ext
    exact Basis.det_mul_det reference first second
  have normalized :
      (Units.map (Int.castRingHom Functions).toMonoidHom
        (integralDeterminantUnit reference second))⁻¹ *
        (Units.map (Int.castRingHom Functions).toMonoidHom
          (integralDeterminantUnit first second) * monomial) =
      monomial * (Units.map (Int.castRingHom Functions).toMonoidHom
        (integralDeterminantUnit reference first))⁻¹ := by
    rw [← determinants, map_mul, mul_inv_rev]
    rw [mul_mul_mul_comm, inv_mul_cancel, one_mul, mul_comm]
  rw [transition]
  change (((Units.map (Int.castRingHom Functions).toMonoidHom
      (integralDeterminantUnit reference second))⁻¹ : Functionsˣ) : Functions) •
      (((Units.map (Int.castRingHom Functions).toMonoidHom
        (integralDeterminantUnit first second) * monomial : Functionsˣ) : Functions) • firstForm) =
    (monomial : Functions) •
      ((((Units.map (Int.castRingHom Functions).toMonoidHom
        (integralDeterminantUnit reference first))⁻¹ : Functionsˣ) : Functions) • firstForm)
  rw [smul_smul, smul_smul]
  exact congrArg (fun scalar => scalar • firstForm) (congrArg Units.val normalized)

end BondalThomsen.CanonicalRaySum

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient} {dimension : ℕ}

noncomputable def canonicalCharacterBasis (_fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) :
    Basis (Fin dimension) ℤ (Lattice →+ ℤ) :=
  basis.dualBasis.map
    ({ toFun := LinearMap.toAddMonoidHom
       invFun := AddMonoidHom.toIntLinearMap
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl
       map_add' := fun _ _ => rfl } :
      Module.Dual ℤ Lattice ≃+ (Lattice →+ ℤ)).toIntLinearEquiv

theorem canonicalCharacterBasis_apply (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice)
    (index coordinate : Fin dimension) :
    fan.canonicalCharacterBasis basis index (basis coordinate) =
      if index = coordinate then 1 else 0 := by
  classical
  simp [canonicalCharacterBasis, Finsupp.single_apply, eq_comm]

theorem canonicalCharacterBasis_eq_dualStep (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) (index : Fin dimension) :
    fan.canonicalCharacterBasis basis index = (fan.basisConeDualStep basis index : Lattice →+ ℤ) := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro coordinate
  exact (fan.canonicalCharacterBasis_apply basis index coordinate).trans
    (fan.basisConeDualStep_apply basis index coordinate).symm

theorem coneDivisorCharacter_negativeRaySum (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis) :
    fan.coneDivisorCharacter basis cone_basis (-fan.anticanonicalRayDivisor) =
      ∑ index, fan.canonicalCharacterBasis basis index := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply basis.ext
  intro coordinate
  change fan.coneDivisorCharacter basis cone_basis (-fan.anticanonicalRayDivisor) (basis coordinate) = _
  rw [fan.coneDivisorCharacter_basis]
  simp [canonicalCharacterBasis_apply]

noncomputable def canonicalTorusCharacterHom (fan : Fan embedding) :
    Multiplicative (Lattice →+ ℤ) →* (affineCoordinateRing 𝕜 fan.lattice ⊥)ˣ where
  toFun character := fan.denseTorusCharacterUnit 𝕜 character.toAdd
  map_one' := fan.denseTorusCharacterUnit_zero 𝕜
  map_mul' first second := fan.denseTorusCharacterUnit_add 𝕜 first.toAdd second.toAdd

noncomputable def canonicalTorusTopTransitionUnit (fan : Fan embedding)
    (first second : Basis (Fin dimension) ℤ Lattice) :
    (affineCoordinateRing 𝕜 fan.lattice ⊥)ˣ :=
  BondalThomsen.CanonicalRaySum.coordinateTopTransitionUnit (fan.canonicalTorusCharacterHom 𝕜)
    (fan.canonicalCharacterBasis first) (fan.canonicalCharacterBasis second)

theorem canonicalTorusCoordinateWedge_transition (fan : Fan embedding)
    (first second : Basis (Fin dimension) ℤ Lattice) :
    exteriorPower.ιMulti (affineCoordinateRing 𝕜 fan.lattice ⊥) dimension
        (fun index => KaehlerDifferential.D 𝕜 (affineCoordinateRing 𝕜 fan.lattice ⊥)
          (fan.denseTorusCharacterUnit 𝕜 (fan.canonicalCharacterBasis second index)).val) =
      (fan.canonicalTorusTopTransitionUnit 𝕜 first second : affineCoordinateRing 𝕜 fan.lattice ⊥) •
        exteriorPower.ιMulti (affineCoordinateRing 𝕜 fan.lattice ⊥) dimension
          (fun index => KaehlerDifferential.D 𝕜 (affineCoordinateRing 𝕜 fan.lattice ⊥)
            (fan.denseTorusCharacterUnit 𝕜 (fan.canonicalCharacterBasis first index)).val) :=
  BondalThomsen.CanonicalRaySum.coordinateWedge_transition (Coefficient := 𝕜)
    (fan.canonicalTorusCharacterHom 𝕜) (fan.canonicalCharacterBasis first)
    (fan.canonicalCharacterBasis second)

theorem canonicalTorusTopTransitionUnit_negativeRaySum (fan : Fan embedding)
    (first : Basis (Fin dimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin dimension) ℤ Lattice) (second_cone : fan.IsConeBasis second) :
    fan.canonicalTorusTopTransitionUnit 𝕜 first second =
      Units.map (Int.castRingHom (affineCoordinateRing 𝕜 fan.lattice ⊥)).toMonoidHom
          (BondalThomsen.CanonicalRaySum.integralDeterminantUnit
            (fan.canonicalCharacterBasis first) (fan.canonicalCharacterBasis second)) *
        fan.denseTorusCharacterUnit 𝕜
          (fan.coneDivisorCharacter second second_cone (-fan.anticanonicalRayDivisor) -
            fan.coneDivisorCharacter first first_cone (-fan.anticanonicalRayDivisor)) := by
  rw [fan.coneDivisorCharacter_negativeRaySum first first_cone,
    fan.coneDivisorCharacter_negativeRaySum second second_cone]
  rfl

theorem canonicalFaceCoordinateRingMap_injective (fan : Fan embedding)
    {cone face : PointedCone ℝ Ambient} (face_of : face.IsFaceOf cone) :
    Function.Injective (faceAffineCoordinateRingMap 𝕜 fan.lattice face_of) := by
  apply MonoidAlgebra.mapDomain_injective
  intro first second same
  apply (Multiplicative.toAdd).injective
  apply Subtype.ext
  have characters := congrArg
    (fun exponent : Multiplicative (dualSemigroup fan.lattice face) =>
      ((toAdd exponent).val : Lattice →+ ℤ)) same
  change ((dualSemigroupMap fan.lattice fan.lattice (AddMonoidHom.id Lattice)
      LinearMap.id (fun _ => rfl) (fun _ contains => face_of.le contains)
      (toAdd first) : dualSemigroup fan.lattice face) : Lattice →+ ℤ) =
    ((dualSemigroupMap fan.lattice fan.lattice (AddMonoidHom.id Lattice)
      LinearMap.id (fun _ => rfl) (fun _ contains => face_of.le contains)
      (toAdd second) : dualSemigroup fan.lattice face) : Lattice →+ ℤ) at characters
  simpa only [coe_dualSemigroupMap_id] using characters

noncomputable def canonicalFaceDifferentialBasis (fan : Fan embedding)
    (regular : fan.IsRegular) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) {face : PointedCone ℝ Ambient}
    (face_of : face.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :
    Basis (Fin dimension) (affineCoordinateRing 𝕜 fan.lattice face)
      (KaehlerDifferential 𝕜 (affineCoordinateRing 𝕜 fan.lattice face)) := by
  let restriction := faceAffineCoordinateRingMap 𝕜 fan.lattice face_of
  let localization :=
    (regular cone_basis).exists_isLocalization_away_faceAffineCoordinateRingMap 𝕜
      fan.lattice face_of
  let character := localization.choose
  letI := restriction.toRingHom.toAlgebra
  letI : IsScalarTower 𝕜 _ (affineCoordinateRing 𝕜 fan.lattice face) :=
    IsScalarTower.of_algebraMap_eq' restriction.comp_algebraMap.symm
  letI := localization.choose_spec
  exact Module.Basis.ofIsLocalizedModule (affineCoordinateRing 𝕜 fan.lattice face)
    (Submonoid.powers (MonoidAlgebra.single (ofAdd character) (1 : 𝕜)))
    (KaehlerDifferential.map 𝕜 𝕜 _ (affineCoordinateRing 𝕜 fan.lattice face))
    (fan.basisConeDifferentialBasis 𝕜 basis)

theorem canonicalFaceTopExteriorMap_injective (fan : Fan embedding)
    {cone face : PointedCone ℝ Ambient} (cone_regular : IsRegularCone embedding cone)
    (face_of : face.IsFaceOf cone)
    (basis : Basis (Fin dimension) (affineCoordinateRing 𝕜 fan.lattice cone)
      (KaehlerDifferential 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone))) :
    Function.Injective (BondalThomsen.SemilinearExterior.map dimension
      (faceAffineCoordinateRingMap 𝕜 fan.lattice face_of).toRingHom
      (BondalThomsen.DifferentialCoordinates.map (faceAffineCoordinateRingMap 𝕜 fan.lattice face_of))) := by
  obtain ⟨character, localized⟩ :=
    cone_regular.exists_isLocalization_away_faceAffineCoordinateRingMap 𝕜 fan.lattice face_of
  exact BondalThomsen.CanonicalRaySum.differentialTopMap_injective_of_localization
    (faceAffineCoordinateRingMap 𝕜 fan.lattice face_of) basis
    (MonoidAlgebra.single (ofAdd character) (1 : 𝕜)) localized
    (fan.canonicalFaceCoordinateRingMap_injective 𝕜 face_of)

noncomputable def canonicalFaceCoordinate (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) {face : PointedCone ℝ Ambient}
    (face_of : face.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (index : Fin dimension) : affineCoordinateRing 𝕜 fan.lattice face :=
  faceAffineCoordinateRingMap 𝕜 fan.lattice face_of
    (MonoidAlgebra.single (ofAdd (fan.basisConeDualStep basis index)) (1 : 𝕜))

noncomputable def canonicalFaceCoordinateWedge (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) {face : PointedCone ℝ Ambient}
    (face_of : face.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :
    ⋀[affineCoordinateRing 𝕜 fan.lattice face]^dimension
      (KaehlerDifferential 𝕜 (affineCoordinateRing 𝕜 fan.lattice face)) :=
  exteriorPower.ιMulti (affineCoordinateRing 𝕜 fan.lattice face) dimension
    (fun index => KaehlerDifferential.D 𝕜 _ (fan.canonicalFaceCoordinate 𝕜 basis face_of index))

theorem canonicalFaceCoordinate_torus (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) {face : PointedCone ℝ Ambient}
    (face_of : face.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (torus_face : (⊥ : PointedCone ℝ Ambient).IsFaceOf face) (index : Fin dimension) :
    faceAffineCoordinateRingMap 𝕜 fan.lattice torus_face
        (fan.canonicalFaceCoordinate 𝕜 basis face_of index) =
      (fan.denseTorusCharacterUnit 𝕜 (fan.canonicalCharacterBasis basis index)).val := by
  unfold canonicalFaceCoordinate
  rw [faceAffineCoordinateRingMap_single, faceAffineCoordinateRingMap_single]
  change MonoidAlgebra.single
      (ofAdd (⟨(fan.basisConeDualStep basis index).val, _⟩ : dualSemigroup fan.lattice ⊥)) 1 =
    MonoidAlgebra.single
      (ofAdd (⟨fan.canonicalCharacterBasis basis index, _⟩ : dualSemigroup fan.lattice ⊥)) 1
  congr 2
  apply Subtype.ext
  exact (fan.canonicalCharacterBasis_eq_dualStep basis index).symm

theorem canonicalFaceCoordinateWedge_torus (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) {face : PointedCone ℝ Ambient}
    (face_of : face.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
    (torus_face : (⊥ : PointedCone ℝ Ambient).IsFaceOf face) :
    BondalThomsen.SemilinearExterior.map dimension
        (faceAffineCoordinateRingMap 𝕜 fan.lattice torus_face).toRingHom
        (BondalThomsen.DifferentialCoordinates.map (faceAffineCoordinateRingMap 𝕜 fan.lattice torus_face))
        (fan.canonicalFaceCoordinateWedge 𝕜 basis face_of) =
      exteriorPower.ιMulti (affineCoordinateRing 𝕜 fan.lattice ⊥) dimension
        (fun index => KaehlerDifferential.D 𝕜 _
          (fan.denseTorusCharacterUnit 𝕜 (fan.canonicalCharacterBasis basis index)).val) := by
  unfold canonicalFaceCoordinateWedge
  rw [BondalThomsen.SemilinearExterior.map_wedge]
  congr 1
  funext index
  exact (BondalThomsen.DifferentialCoordinates.map_D _ _).trans
    (congrArg (KaehlerDifferential.D 𝕜 _) (fan.canonicalFaceCoordinate_torus 𝕜 basis face_of torus_face index))

noncomputable def canonicalOverlapTopTransitionUnit (fan : Fan embedding)
    (first : Basis (Fin dimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin dimension) ℤ Lattice) (second_cone : fan.IsConeBasis second) :
    (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
        PointedCone.hull ℝ (Set.range (fun index => embedding (second index)))))ˣ :=
  Units.map (Int.castRingHom _).toMonoidHom
      (BondalThomsen.CanonicalRaySum.integralDeterminantUnit
        (fan.canonicalCharacterBasis first) (fan.canonicalCharacterBasis second)) *
    (fan.coneDivisorTransitionUnit 𝕜 first first_cone second second_cone
      (-fan.anticanonicalRayDivisor))⁻¹

theorem canonicalOverlapTopTransitionUnit_torus (fan : Fan embedding)
    (first : Basis (Fin dimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin dimension) ℤ Lattice) (second_cone : fan.IsConeBasis second) :
    let torus_face := (fan.isToricCone (fan.inf_mem first_cone second_cone)).salient.bot_isFaceOf
    Units.map (faceAffineCoordinateRingMap 𝕜 fan.lattice torus_face).toMonoidHom
        (fan.canonicalOverlapTopTransitionUnit 𝕜 first first_cone second second_cone) =
      fan.canonicalTorusTopTransitionUnit 𝕜 first second := by
  dsimp only
  rw [fan.canonicalTorusTopTransitionUnit_negativeRaySum 𝕜 first first_cone second second_cone]
  unfold canonicalOverlapTopTransitionUnit
  rw [map_mul, map_inv]
  congr 1
  · apply Units.ext
    change faceAffineCoordinateRingMap 𝕜 fan.lattice
        ((fan.isToricCone (fan.inf_mem first_cone second_cone)).salient.bot_isFaceOf)
        (((fan.canonicalCharacterBasis first).det (fan.canonicalCharacterBasis second) : ℤ) :
          affineCoordinateRing 𝕜 fan.lattice _) =
      (((fan.canonicalCharacterBasis first).det (fan.canonicalCharacterBasis second) : ℤ) :
        affineCoordinateRing 𝕜 fan.lattice ⊥)
    exact map_intCast (faceAffineCoordinateRingMap 𝕜 fan.lattice _) _
  · have monomial := toricMonomialUnit_face_restriction 𝕜 fan.lattice
      ((fan.isToricCone (fan.inf_mem first_cone second_cone)).salient.bot_isFaceOf)
      (fan.coneDivisorCharacter first first_cone (-fan.anticanonicalRayDivisor) -
        fan.coneDivisorCharacter second second_cone (-fan.anticanonicalRayDivisor))
      (fan.coneDivisorCharacter_transition_dualSemigroup first first_cone second second_cone
        (-fan.anticanonicalRayDivisor)).1
      (fan.coneDivisorCharacter_transition_dualSemigroup first first_cone second second_cone
        (-fan.anticanonicalRayDivisor)).2
    rw [show Units.map (faceAffineCoordinateRingMap 𝕜 fan.lattice
        ((fan.isToricCone (fan.inf_mem first_cone second_cone)).salient.bot_isFaceOf)).toMonoidHom
        (fan.coneDivisorTransitionUnit 𝕜 first first_cone second second_cone
          (-fan.anticanonicalRayDivisor)) =
      fan.denseTorusCharacterUnit 𝕜
        (fan.coneDivisorCharacter first first_cone (-fan.anticanonicalRayDivisor) -
          fan.coneDivisorCharacter second second_cone (-fan.anticanonicalRayDivisor)) from monomial]
    change (fan.canonicalTorusCharacterHom 𝕜 (ofAdd _))⁻¹ = fan.canonicalTorusCharacterHom 𝕜 (ofAdd _)
    rw [← map_inv]
    congr 1
    exact congrArg ofAdd (neg_sub _ _)

theorem canonicalOverlapCoordinateWedge_transition (fan : Fan embedding)
    (regular : fan.IsRegular)
    (first : Basis (Fin dimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin dimension) ℤ Lattice) (second_cone : fan.IsConeBasis second) :
    let first_face := fan.inf_isFaceOf_left first_cone second_cone
    let second_face := fan.inf_isFaceOf_right first_cone second_cone
    (fan.canonicalFaceCoordinateWedge 𝕜) second second_face =
      (fan.canonicalOverlapTopTransitionUnit 𝕜 first first_cone second second_cone :
        affineCoordinateRing 𝕜 fan.lattice
          (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
            PointedCone.hull ℝ (Set.range (fun index => embedding (second index))))) •
        fan.canonicalFaceCoordinateWedge 𝕜 first first_face := by
  dsimp only
  let torus_face := (fan.isToricCone (fan.inf_mem first_cone second_cone)).salient.bot_isFaceOf
  apply fan.canonicalFaceTopExteriorMap_injective 𝕜 (regular (fan.inf_mem first_cone second_cone))
    torus_face (fan.canonicalFaceDifferentialBasis 𝕜 regular first first_cone
      (fan.inf_isFaceOf_left first_cone second_cone))
  rw [map_smulₛₗ, fan.canonicalFaceCoordinateWedge_torus 𝕜,
    fan.canonicalFaceCoordinateWedge_torus 𝕜]
  have transition := congrArg Units.val
    (fan.canonicalOverlapTopTransitionUnit_torus 𝕜 first first_cone second second_cone)
  simp only [Units.coe_map] at transition
  exact (fan.canonicalTorusCoordinateWedge_transition 𝕜 first second).trans
    (congrArg (fun scalar => scalar • exteriorPower.ιMulti
      (affineCoordinateRing 𝕜 fan.lattice ⊥) dimension
      (fun index => KaehlerDifferential.D 𝕜 _
        (fan.denseTorusCharacterUnit 𝕜 (fan.canonicalCharacterBasis first index)).val)) transition.symm)

noncomputable def canonicalOrientedFaceCoordinateWedge (fan : Fan embedding)
    (reference basis : Basis (Fin dimension) ℤ Lattice) {face : PointedCone ℝ Ambient}
    (face_of : face.IsFaceOf
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) :
    ⋀[affineCoordinateRing 𝕜 fan.lattice face]^dimension
      (KaehlerDifferential 𝕜 (affineCoordinateRing 𝕜 fan.lattice face)) :=
  ((Units.map (Int.castRingHom (affineCoordinateRing 𝕜 fan.lattice face)).toMonoidHom
    (BondalThomsen.CanonicalRaySum.integralDeterminantUnit
      (fan.canonicalCharacterBasis reference) (fan.canonicalCharacterBasis basis)))⁻¹ :
      (affineCoordinateRing 𝕜 fan.lattice face)ˣ) •
    fan.canonicalFaceCoordinateWedge 𝕜 basis face_of

theorem canonicalOverlapOrientedCoordinateWedge_transition (fan : Fan embedding)
    (regular : fan.IsRegular) (reference : Basis (Fin dimension) ℤ Lattice)
    (first : Basis (Fin dimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin dimension) ℤ Lattice) (second_cone : fan.IsConeBasis second) :
    let first_face := fan.inf_isFaceOf_left first_cone second_cone
    let second_face := fan.inf_isFaceOf_right first_cone second_cone
    (fan.canonicalOrientedFaceCoordinateWedge 𝕜) reference second second_face =
      ((fan.coneDivisorTransitionUnit 𝕜 first first_cone second second_cone
        (-fan.anticanonicalRayDivisor))⁻¹ :
          (affineCoordinateRing 𝕜 fan.lattice
            (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
              PointedCone.hull ℝ (Set.range (fun index => embedding (second index)))))ˣ) •
        fan.canonicalOrientedFaceCoordinateWedge 𝕜 reference first first_face := by
  dsimp only
  have transition :=
    fan.canonicalOverlapCoordinateWedge_transition 𝕜 regular first first_cone second second_cone
  dsimp only at transition
  unfold canonicalOverlapTopTransitionUnit at transition
  exact BondalThomsen.CanonicalRaySum.orientationNormalizedForm_transition
    (fan.canonicalCharacterBasis reference) (fan.canonicalCharacterBasis first)
    (fan.canonicalCharacterBasis second)
    (fan.coneDivisorTransitionUnit 𝕜 first first_cone second second_cone
      (-fan.anticanonicalRayDivisor))⁻¹
    (fan.canonicalFaceCoordinateWedge 𝕜 first (fan.inf_isFaceOf_left first_cone second_cone))
    (fan.canonicalFaceCoordinateWedge 𝕜 second (fan.inf_isFaceOf_right first_cone second_cone))
    transition

end TauCeti.Toric.Fan
