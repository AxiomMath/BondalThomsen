module

public import BondalThomsen.Toric.Canonical.Sheaf
public import BondalThomsen.Toric.Divisor.DivisorMonomialAffineEmbedding
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Derivation.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.SemilinearExterior

universe coefficientUniverse targetCoefficientUniverse moduleUniverse targetModuleUniverse

variable {Coefficient : Type coefficientUniverse} {TargetCoefficient : Type targetCoefficientUniverse}
    [CommRing Coefficient] [CommRing TargetCoefficient]
    {Source : Type moduleUniverse} {Target : Type targetModuleUniverse}
    [AddCommGroup Source] [Module Coefficient Source]
    [AddCommGroup Target] [Module TargetCoefficient Target]

noncomputable def map (degree : ℕ) (coefficientMap : Coefficient →+* TargetCoefficient)
    (moduleMap : Source →ₛₗ[coefficientMap] Target) :
    (⋀[Coefficient]^degree Source) →ₛₗ[coefficientMap]
      (⋀[TargetCoefficient]^degree Target) := by
  letI : Module Coefficient (⋀[TargetCoefficient]^degree Target) :=
    Module.compHom _ coefficientMap
  let alternating : Source [⋀^Fin degree]→ₗ[Coefficient]
      (⋀[TargetCoefficient]^degree Target) :=
    { toFun := fun vectors => exteriorPower.ιMulti TargetCoefficient degree (moduleMap ∘ vectors)
      map_update_add' := by
        intro decidable vectors index first second
        simp only [Function.comp_update, map_add]
        exact (exteriorPower.ιMulti TargetCoefficient degree).map_update_add _ _ _ _
      map_update_smul' := by
        intro decidable vectors index scalar vector
        simp only [Function.comp_update, map_smulₛₗ]
        exact (exteriorPower.ιMulti TargetCoefficient degree).map_update_smul _ _ _ _
      map_eq_zero_of_eq' := by
        intro vectors first second equal distinct
        exact (exteriorPower.ιMulti TargetCoefficient degree).map_eq_zero_of_eq _
          (congrArg moduleMap equal) distinct }
  let linear := exteriorPower.alternatingMapLinearEquiv alternating
  exact
    { toFun := linear
      map_add' := linear.map_add
      map_smul' := fun scalar vector => linear.map_smul scalar vector }

theorem map_wedge (degree : ℕ) (coefficientMap : Coefficient →+* TargetCoefficient)
    (moduleMap : Source →ₛₗ[coefficientMap] Target) (vectors : Fin degree → Source) :
    map degree coefficientMap moduleMap (exteriorPower.ιMulti Coefficient degree vectors) =
      exteriorPower.ιMulti TargetCoefficient degree (moduleMap ∘ vectors) := by
  let : Module Coefficient (⋀[TargetCoefficient]^degree Target) :=
    Module.compHom _ coefficientMap
  unfold map
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem ext {degree : ℕ} {coefficientMap : Coefficient →+* TargetCoefficient}
    {first second : (⋀[Coefficient]^degree Source) →ₛₗ[coefficientMap]
      (⋀[TargetCoefficient]^degree Target)}
    (onWedges : ∀ vectors, first (exteriorPower.ιMulti Coefficient degree vectors) =
      second (exteriorPower.ιMulti Coefficient degree vectors)) : first = second := by
  apply DFunLike.ext
  intro vector
  have membership : vector ∈ Submodule.span Coefficient
      (Set.range (exteriorPower.ιMulti Coefficient degree)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction membership using Submodule.span_induction with
  | mem vector membership =>
      obtain ⟨vectors, rfl⟩ := membership
      exact onWedges vectors
  | zero => simp only [map_zero]
  | add firstVector secondVector first_mem second_mem first_eq second_eq =>
      simp only [map_add, first_eq, second_eq]
  | smul scalar vector vector_mem vector_eq => simp only [map_smulₛₗ, vector_eq]

theorem map_id (degree : ℕ) :
    map degree (RingHom.id Coefficient) (LinearMap.id : Source →ₗ[Coefficient] Source) =
      LinearMap.id := by
  apply ext
  intro vectors
  simp only [map_wedge, LinearMap.id_coe, Function.id_comp, LinearMap.id_apply]

theorem map_comp {ThirdCoefficient : Type*} [CommRing ThirdCoefficient]
    {Third : Type*} [AddCommGroup Third] [Module ThirdCoefficient Third]
    (degree : ℕ) (firstCoefficient : Coefficient →+* TargetCoefficient)
    (secondCoefficient : TargetCoefficient →+* ThirdCoefficient)
    (firstMap : Source →ₛₗ[firstCoefficient] Target)
    (secondMap : Target →ₛₗ[secondCoefficient] Third) :
    letI : RingHomCompTriple firstCoefficient secondCoefficient
        (secondCoefficient.comp firstCoefficient) := ⟨rfl⟩
    map degree (secondCoefficient.comp firstCoefficient) (secondMap.comp firstMap) =
      (map degree secondCoefficient secondMap).comp (map degree firstCoefficient firstMap) := by
  let : RingHomCompTriple firstCoefficient secondCoefficient
      (secondCoefficient.comp firstCoefficient) := ⟨rfl⟩
  apply ext
  intro vectors
  simp only [map_wedge, LinearMap.comp_apply]
  rfl

end BondalThomsen.SemilinearExterior

namespace BondalThomsen

universe siteUniverse siteHomUniverse ringUniverse sectionUniverse

theorem exteriorLinear_ext {Coefficient : Type*} [CommRing Coefficient]
    {Source Target : Type*} [AddCommGroup Source] [Module Coefficient Source]
    [AddCommGroup Target] [Module Coefficient Target] {degree : ℕ}
    {first second : (⋀[Coefficient]^degree Source) →ₗ[Coefficient] Target}
    (onWedges : ∀ vectors, first (exteriorPower.ιMulti Coefficient degree vectors) =
      second (exteriorPower.ιMulti Coefficient degree vectors)) : first = second := by
  apply DFunLike.ext
  intro vector
  have membership : vector ∈ Submodule.span Coefficient
      (Set.range (exteriorPower.ιMulti Coefficient degree)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction membership using Submodule.span_induction with
  | mem vector membership =>
      obtain ⟨vectors, rfl⟩ := membership
      exact onWedges vectors
  | zero => simp only [map_zero]
  | add firstVector secondVector first_mem second_mem first_eq second_eq =>
      simp only [map_add, first_eq, second_eq]
  | smul scalar vector vector_mem vector_eq => simp only [map_smul, vector_eq]

noncomputable def exteriorPresheaf {Site : Type siteUniverse} [Category.{siteHomUniverse} Site]
    {Coefficients : Siteᵒᵖ ⥤ CommRingCat.{ringUniverse}}
    (modules : PresheafOfModules.{sectionUniverse} (Coefficients ⋙ forget₂ _ _))
    (degree : ℕ) : PresheafOfModules.{max sectionUniverse ringUniverse}
      (Coefficients ⋙ forget₂ _ _) where
  obj domain := ModuleCat.of (Coefficients.obj domain)
    (⋀[Coefficients.obj domain]^degree (modules.obj domain))
  map {domain smaller} inclusion := by
    exact ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (Coefficients.map inclusion).hom).obj
        (ModuleCat.of (Coefficients.obj smaller)
          (⋀[Coefficients.obj smaller]^degree (modules.obj smaller))))
      { toFun := SemilinearExterior.map degree (Coefficients.map inclusion).hom
          (modules.restrictₛₗ inclusion)
        map_add' := map_add _
        map_smul' := fun scalar vector =>
          (SemilinearExterior.map degree (Coefficients.map inclusion).hom
            (modules.restrictₛₗ inclusion)).map_smulₛₗ scalar vector }
  map_id domain := by
    apply ModuleCat.hom_ext
    apply exteriorLinear_ext
    intro vectors
    change SemilinearExterior.map degree (Coefficients.map (𝟙 domain)).hom
        (modules.restrictₛₗ (𝟙 domain)) (exteriorPower.ιMulti _ degree vectors) = _
    rw [SemilinearExterior.map_wedge]
    have vectors_eq : modules.restrictₛₗ (𝟙 domain) ∘ vectors = vectors := by
      funext index
      change modules.map (𝟙 domain) (vectors index) = vectors index
      rw [modules.map_id]
      rfl
    rw [vectors_eq]
    rfl
  map_comp {domain middle smaller} first second := by
    apply ModuleCat.hom_ext
    apply exteriorLinear_ext
    intro vectors
    change SemilinearExterior.map degree (Coefficients.map (first ≫ second)).hom
        (modules.restrictₛₗ (first ≫ second)) (exteriorPower.ιMulti _ degree vectors) =
      SemilinearExterior.map degree (Coefficients.map second).hom (modules.restrictₛₗ second)
        (SemilinearExterior.map degree (Coefficients.map first).hom (modules.restrictₛₗ first)
          (exteriorPower.ιMulti _ degree vectors))
    rw [SemilinearExterior.map_wedge, SemilinearExterior.map_wedge, SemilinearExterior.map_wedge]
    congr 1
    funext index
    exact modules.map_comp_apply first second (vectors index)

theorem exteriorPresheaf_map_wedge {Site : Type siteUniverse} [Category.{siteHomUniverse} Site]
    {Coefficients : Siteᵒᵖ ⥤ CommRingCat.{ringUniverse}}
    (modules : PresheafOfModules.{sectionUniverse} (Coefficients ⋙ forget₂ _ _))
    (degree : ℕ) {domain smaller : Siteᵒᵖ} (inclusion : domain ⟶ smaller)
    (vectors : Fin degree → modules.obj domain) :
    (exteriorPresheaf modules degree).map inclusion
        (exteriorPower.ιMulti (Coefficients.obj domain) degree vectors) =
      exteriorPower.ιMulti (M := modules.obj smaller) (Coefficients.obj smaller) degree
        (fun index => (modules.map inclusion (vectors index) : modules.obj smaller)) :=
  SemilinearExterior.map_wedge degree (Coefficients.map inclusion).hom
    (modules.restrictₛₗ inclusion) vectors

noncomputable def exteriorSheaf {SchemeModel : Scheme} (modules : SchemeModel.Modules)
    (degree : ℕ) : SchemeModel.Modules :=
  (PresheafOfModules.sheafification (𝟙 SchemeModel.ringCatSheaf.obj)).obj
    (exteriorPresheaf modules.val degree)

noncomputable def canonicalExteriorSheaf {SchemeModel Base : Scheme}
    (structureMap : SchemeModel ⟶ Base) (dimension : ℕ) : SchemeModel.Modules :=
  exteriorSheaf (cotangentSheaf structureMap) dimension

end BondalThomsen

namespace BondalThomsen.TopExterior

variable {Coefficient : Type*} [CommRing Coefficient]
    {Vectors : Type*} [AddCommGroup Vectors] [Module Coefficient Vectors] {dimension : ℕ}

theorem wedge_eq_det_smul (basis : Basis (Fin dimension) Coefficient Vectors)
    (vectors : Fin dimension → Vectors) :
    exteriorPower.ιMulti Coefficient dimension vectors =
      basis.det vectors • exteriorPower.ιMulti Coefficient dimension basis := by
  have alternating_eq : exteriorPower.ιMulti Coefficient dimension =
      basis.det.smulRight (exteriorPower.ιMulti Coefficient dimension basis) := by
    apply basis.ext_alternating
    intro indices injective
    let permutation : Equiv.Perm (Fin dimension) :=
      Equiv.ofBijective indices ⟨injective, Finite.surjective_of_injective injective⟩
    change exteriorPower.ιMulti Coefficient dimension (basis ∘ permutation) =
      basis.det (basis ∘ permutation) • exteriorPower.ιMulti Coefficient dimension basis
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm, Basis.det_self]
    simp
  exact DFunLike.congr_fun alternating_eq vectors

noncomputable def trivialization (basis : Basis (Fin dimension) Coefficient Vectors) :
    (⋀[Coefficient]^dimension Vectors) ≃ₗ[Coefficient] Coefficient where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv basis.det
  invFun scalar := scalar • exteriorPower.ιMulti Coefficient dimension basis
  left_inv := by
    intro vector
    have maps_eq :
        (LinearMap.toSpanSingleton Coefficient _
          (exteriorPower.ιMulti Coefficient dimension basis)).comp
          (exteriorPower.alternatingMapLinearEquiv basis.det) = LinearMap.id := by
      apply BondalThomsen.exteriorLinear_ext
      intro vectors
      simp only [LinearMap.comp_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
        LinearMap.toSpanSingleton_apply, LinearMap.id_apply]
      exact (wedge_eq_det_smul basis vectors).symm
    exact DFunLike.congr_fun maps_eq vector
  right_inv := by
    intro scalar
    change exteriorPower.alternatingMapLinearEquiv basis.det
      (scalar • exteriorPower.ιMulti Coefficient dimension basis) = scalar
    simp only [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      Basis.det_self, smul_eq_mul, mul_one]

theorem trivialization_wedge (basis : Basis (Fin dimension) Coefficient Vectors)
    (vectors : Fin dimension → Vectors) :
    trivialization basis (exteriorPower.ιMulti Coefficient dimension vectors) =
      basis.det vectors :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem trivialization_frame (basis : Basis (Fin dimension) Coefficient Vectors) :
    trivialization basis (exteriorPower.ιMulti Coefficient dimension basis) = 1 := by
  rw [trivialization_wedge, Basis.det_self]

end BondalThomsen.TopExterior

namespace BondalThomsen.DifferentialCoordinates

universe coordinateUniverse

variable {Coefficient Source : Type coordinateUniverse} [CommRing Coefficient] [CommRing Source]
    [Algebra Coefficient Source] {dimension : ℕ}

noncomputable def polynomialBasis
    (coordinates : Source ≃ₐ[Coefficient] MvPolynomial (Fin dimension) Coefficient) :
    Basis (Fin dimension) Source (KaehlerDifferential Coefficient Source) := by
  letI : Module Source
      (KaehlerDifferential Coefficient (MvPolynomial (Fin dimension) Coefficient)) :=
    Module.compHom _ coordinates.toRingHom
  letI := RingHomInvPair.of_ringEquiv coordinates.toRingEquiv
  letI := RingHomInvPair.of_ringEquiv_symm coordinates.toRingEquiv
  let transport := equiv coordinates
  let linear : KaehlerDifferential Coefficient Source ≃ₗ[Source]
      KaehlerDifferential Coefficient (MvPolynomial (Fin dimension) Coefficient) :=
    { transport.toAddEquiv with
      map_smul' := fun scalar vector => transport.map_smulₛₗ scalar vector }
  exact ((KaehlerDifferential.mvPolynomialBasis Coefficient (Fin dimension)).mapCoeffs
    coordinates.toRingEquiv.symm (fun scalar vector => by
      change coordinates (coordinates.symm scalar) • vector = scalar • vector
      rw [AlgEquiv.apply_symm_apply])).map linear.symm

theorem polynomialBasis_apply
    (coordinates : Source ≃ₐ[Coefficient] MvPolynomial (Fin dimension) Coefficient)
    (index : Fin dimension) :
    polynomialBasis coordinates index =
      KaehlerDifferential.D Coefficient Source (coordinates.symm (MvPolynomial.X index)) := by
  let : Module Source
      (KaehlerDifferential Coefficient (MvPolynomial (Fin dimension) Coefficient)) :=
    Module.compHom _ coordinates.toRingHom
  let := RingHomInvPair.of_ringEquiv coordinates.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm coordinates.toRingEquiv
  unfold polynomialBasis
  rw [Basis.map_apply, Basis.mapCoeffs_apply]
  change map coordinates.symm.toAlgHom
      (KaehlerDifferential.mvPolynomialBasis Coefficient (Fin dimension) index) = _
  rw [KaehlerDifferential.mvPolynomialBasis_apply, map_D]
  rfl

end BondalThomsen.DifferentialCoordinates

namespace BondalThomsen.LogDifferential

variable {Coefficient Functions : Type*} [CommRing Coefficient] [CommRing Functions]
    [Algebra Coefficient Functions]

noncomputable def ofUnit (unit : Functionsˣ) : KaehlerDifferential Coefficient Functions :=
  (unit⁻¹ : Functionsˣ).val • KaehlerDifferential.D Coefficient Functions unit.val

theorem ofUnit_mul (first second : Functionsˣ) :
    ofUnit (Coefficient := Coefficient) (first * second) = ofUnit first + ofUnit second := by
  unfold ofUnit
  simp only [Units.val_mul, mul_inv_rev, Derivation.leibniz, smul_add, smul_smul]
  have first_eq : (↑second⁻¹ * ↑first⁻¹) * ↑first = (↑second⁻¹ : Functions) := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  have second_eq : (↑second⁻¹ * ↑first⁻¹) * ↑second = (↑first⁻¹ : Functions) := by
    rw [mul_comm (↑second⁻¹ : Functions) (↑first⁻¹ : Functions), mul_assoc,
      Units.inv_mul, mul_one]
  rw [first_eq, second_eq, add_comm]

theorem ofUnit_one : ofUnit (Coefficient := Coefficient) (1 : Functionsˣ) = 0 := by
  simp [ofUnit]

noncomputable def characterMap {Characters : Type*} [AddCommGroup Characters]
    (characters : Multiplicative Characters →* Functionsˣ) :
    Characters →+ KaehlerDifferential Coefficient Functions where
  toFun character := ofUnit (characters (Multiplicative.ofAdd character))
  map_zero' := by
    change ofUnit (characters 1) = 0
    rw [map_one, ofUnit_one]
  map_add' first second := by
    change ofUnit (characters (Multiplicative.ofAdd first * Multiplicative.ofAdd second)) = _
    rw [map_mul, ofUnit_mul]

theorem wedge_eq_prod_smul {dimension : ℕ} (coordinates : Fin dimension → Functionsˣ) :
    exteriorPower.ιMulti Functions dimension
        (fun index => KaehlerDifferential.D Coefficient Functions (coordinates index).val) =
      (∏ index, (coordinates index).val) •
        exteriorPower.ιMulti Functions dimension (fun index => ofUnit (coordinates index)) := by
  have factor (index : Fin dimension) :
      KaehlerDifferential.D Coefficient Functions (coordinates index).val =
        (coordinates index).val • ofUnit (Coefficient := Coefficient) (coordinates index) := by
    unfold ofUnit
    rw [smul_smul, Units.mul_inv, one_smul]
  simp_rw [factor]
  exact AlternatingMap.map_smul_univ _ _ _

end BondalThomsen.LogDifferential

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def toricCanonicalExteriorSheaf (fan : Fan embedding) (regular : fan.IsRegular)
    (dimension : ℕ) : (fan.algebraicRealization 𝕜 regular).Modules :=
  BondalThomsen.canonicalExteriorSheaf (fan.structureMap 𝕜 regular) dimension

variable {dimension : ℕ}

noncomputable def basisConeDifferentialBasis (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) :
    Basis (Fin dimension)
      (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
      (KaehlerDifferential 𝕜 (affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))) :=
  BondalThomsen.DifferentialCoordinates.polynomialBasis (fan.basisConeCoordinateRingEquiv 𝕜 basis)

theorem basisConeDifferentialBasis_apply (fan : Fan embedding)
    (basis : Basis (Fin dimension) ℤ Lattice) (index : Fin dimension) :
    fan.basisConeDifferentialBasis 𝕜 basis index =
      KaehlerDifferential.D 𝕜 _
        (MonoidAlgebra.single (Multiplicative.ofAdd (fan.basisConeDualStep basis index)) (1 : 𝕜)) := by
  rw [basisConeDifferentialBasis, BondalThomsen.DifferentialCoordinates.polynomialBasis_apply,
    fan.basisConeDualStepMonomial_eq_variable 𝕜 basis index]

end TauCeti.Toric.Fan
