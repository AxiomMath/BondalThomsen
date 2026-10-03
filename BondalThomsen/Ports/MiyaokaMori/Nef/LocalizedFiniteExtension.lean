module

public import BondalThomsen.Ports.MiyaokaMori.Nef.FiniteFiberHeight
public import BondalThomsen.Ports.MiyaokaMori.Nef.OpenImmersionOrder
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Classical AlgebraicGeometry

universe u

noncomputable section

namespace FiniteLocalModel

variable {baseRing : Type u} (coordinateRing : Type u) [CommRing baseRing] [CommRing coordinateRing] [Algebra baseRing coordinateRing]
  (basePrime : Ideal baseRing) [basePrime.IsPrime]

abbrev LocB : Type u := Localization (Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl)

variable (localRing : Type u) [CommRing localRing] [Algebra baseRing localRing] [IsLocalization.AtPrime localRing basePrime]

@[instance_reducible] def algAB : Algebra localRing (LocB coordinateRing basePrime) :=
  (IsLocalization.map (M := basePrime.primeCompl) (T := Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl)
    (LocB coordinateRing basePrime) (algebraMap baseRing coordinateRing) (Submonoid.le_comap_map _)).toAlgebra

theorem algAB_algebraMap_comp :
    letI := algAB coordinateRing basePrime localRing
    (algebraMap localRing (LocB coordinateRing basePrime)).comp (algebraMap baseRing localRing) =
      (algebraMap coordinateRing (LocB coordinateRing basePrime)).comp (algebraMap baseRing coordinateRing) :=
  IsLocalization.map_comp _

theorem tower_RAB :
    letI := algAB coordinateRing basePrime localRing
    IsScalarTower baseRing localRing (LocB coordinateRing basePrime) := by
  let := algAB coordinateRing basePrime localRing
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [algAB_algebraMap_comp, IsScalarTower.algebraMap_eq baseRing coordinateRing (LocB coordinateRing basePrime)]

theorem finite_AB [Module.Finite baseRing coordinateRing] :
    letI := algAB coordinateRing basePrime localRing
    Module.Finite localRing (LocB coordinateRing basePrime) := by
  let := algAB coordinateRing basePrime localRing
  have := tower_RAB coordinateRing basePrime localRing
  exact Module.Finite.of_isLocalization baseRing coordinateRing basePrime.primeCompl

theorem injective_AB (hinj : Function.Injective (algebraMap baseRing coordinateRing)) :
    letI := algAB coordinateRing basePrime localRing
    Function.Injective (algebraMap localRing (LocB coordinateRing basePrime)) :=
  haveI : IsLocalization (basePrime.primeCompl.map (algebraMap baseRing coordinateRing)) (LocB coordinateRing basePrime) :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl) (LocB coordinateRing basePrime))
  IsLocalization.map_injective_of_injective basePrime.primeCompl localRing (LocB coordinateRing basePrime) hinj

theorem isDomain_B [IsDomain coordinateRing] (hinj : Function.Injective (algebraMap baseRing coordinateRing)) :
    IsDomain (LocB coordinateRing basePrime) := by
  refine IsLocalization.isDomain_localization ?_
  rintro _ ⟨scalar, hr, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun equality ↦ hr ?_
  have : scalar = 0 := hinj (by rw [equality, map_zero])
  rw [this]; exact basePrime.zero_mem

section Frac

variable (functionField : Type u) [Field functionField] [Algebra coordinateRing functionField] [IsFractionRing coordinateRing functionField] [IsDomain coordinateRing]

theorem isUnit_of_mem (hinj : Function.Injective (algebraMap baseRing coordinateRing))
    (coordinate : Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl) : IsUnit (algebraMap coordinateRing functionField coordinate) := by
  obtain ⟨_, scalar, hr, rfl⟩ := coordinate
  refine IsUnit.mk0 _ fun equality ↦ hr ?_
  have h1 : algebraMap baseRing coordinateRing scalar = 0 := IsFractionRing.injective coordinateRing functionField (by rw [equality, map_zero])
  have : scalar = 0 := hinj (by rw [h1, map_zero])
  rw [this]; exact basePrime.zero_mem

@[instance_reducible] def algBL (hinj : Function.Injective (algebraMap baseRing coordinateRing)) : Algebra (LocB coordinateRing basePrime) functionField :=
  (IsLocalization.lift (M := Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl)
    (g := algebraMap coordinateRing functionField) (isUnit_of_mem coordinateRing basePrime functionField hinj)).toAlgebra

theorem tower_CBL (hinj : Function.Injective (algebraMap baseRing coordinateRing)) :
    letI := algBL coordinateRing basePrime functionField hinj
    IsScalarTower coordinateRing (LocB coordinateRing basePrime) functionField := by
  let := algBL coordinateRing basePrime functionField hinj
  refine IsScalarTower.of_algebraMap_eq fun coordinate ↦ ?_
  exact (IsLocalization.lift_eq (isUnit_of_mem coordinateRing basePrime functionField hinj) coordinate).symm

theorem isFractionRing_BL (hinj : Function.Injective (algebraMap baseRing coordinateRing)) :
    letI := algBL coordinateRing basePrime functionField hinj
    IsFractionRing (LocB coordinateRing basePrime) functionField := by
  let := algBL coordinateRing basePrime functionField hinj
  have := tower_CBL coordinateRing basePrime functionField hinj
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl) (LocB coordinateRing basePrime) functionField

theorem tower_ABL (hinj : Function.Injective (algebraMap baseRing coordinateRing)) [Algebra localRing functionField]
    (equality : (algebraMap localRing functionField).comp (algebraMap baseRing localRing) = (algebraMap coordinateRing functionField).comp (algebraMap baseRing coordinateRing)) :
    letI := algAB coordinateRing basePrime localRing
    letI := algBL coordinateRing basePrime functionField hinj
    IsScalarTower localRing (LocB coordinateRing basePrime) functionField := by
  let := algAB coordinateRing basePrime localRing
  let := algBL coordinateRing basePrime functionField hinj
  have := tower_CBL coordinateRing basePrime functionField hinj
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine IsLocalization.ringHom_ext basePrime.primeCompl ?_
  rw [equality, RingHom.comp_assoc, algAB_algebraMap_comp, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq coordinateRing (LocB coordinateRing basePrime) functionField]

end Frac

section Max

theorem disjoint_of_comap_eq {coordinatePrime : Ideal coordinateRing} (equality : coordinatePrime.comap (algebraMap baseRing coordinateRing) = basePrime) :
    Disjoint (Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl : Set coordinateRing) (coordinatePrime : Set coordinateRing) := by
  rw [Set.disjoint_left]
  rintro _ ⟨scalar, hr, rfl⟩ hmem
  exact hr (equality ▸ (Ideal.mem_comap.mpr hmem))

variable [IsLocalRing localRing] [Module.Finite baseRing coordinateRing]

include localRing

theorem comap_A_of_isMaximal (maximalIdeal : Ideal (LocB coordinateRing basePrime)) [hm : maximalIdeal.IsMaximal] :
    letI := algAB coordinateRing basePrime localRing
    maximalIdeal.comap (algebraMap localRing (LocB coordinateRing basePrime)) = IsLocalRing.maximalIdeal localRing := by
  let := algAB coordinateRing basePrime localRing
  have := finite_AB coordinateRing basePrime localRing
  have : Algebra.IsIntegral localRing (LocB coordinateRing basePrime) := Algebra.IsIntegral.of_finite _ _
  exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (algebraMap localRing (LocB coordinateRing basePrime))
    (Algebra.IsIntegral.isIntegral (R := localRing)) maximalIdeal)

theorem comap_R_of_isMaximal (maximalIdeal : Ideal (LocB coordinateRing basePrime)) [hm : maximalIdeal.IsMaximal] :
    (maximalIdeal.comap (algebraMap coordinateRing (LocB coordinateRing basePrime))).comap (algebraMap baseRing coordinateRing) = basePrime := by
  let := algAB coordinateRing basePrime localRing
  rw [Ideal.comap_comap, ← algAB_algebraMap_comp coordinateRing basePrime localRing, ← Ideal.comap_comap,
    comap_A_of_isMaximal coordinateRing basePrime localRing maximalIdeal]
  exact IsLocalization.AtPrime.under_maximalIdeal localRing basePrime

theorem isMaximal_map {coordinatePrime : Ideal coordinateRing} [h𝔮 : coordinatePrime.IsPrime] (equality : coordinatePrime.comap (algebraMap baseRing coordinateRing) = basePrime) :
    (coordinatePrime.map (algebraMap coordinateRing (LocB coordinateRing basePrime))).IsMaximal := by
  let := algAB coordinateRing basePrime localRing
  have := finite_AB coordinateRing basePrime localRing
  have : Algebra.IsIntegral localRing (LocB coordinateRing basePrime) := Algebra.IsIntegral.of_finite _ _
  have hdisj := disjoint_of_comap_eq coordinateRing basePrime equality
  have hprime : (coordinatePrime.map (algebraMap coordinateRing (LocB coordinateRing basePrime))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ coordinatePrime h𝔮 hdisj
  have hcomap : (coordinatePrime.map (algebraMap coordinateRing (LocB coordinateRing basePrime))).comap (algebraMap coordinateRing (LocB coordinateRing basePrime)) = coordinatePrime :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ h𝔮 hdisj
  set primeIdeal := (coordinatePrime.map (algebraMap coordinateRing (LocB coordinateRing basePrime))).comap (algebraMap localRing (LocB coordinateRing basePrime)) with hP
  have hPR : primeIdeal.comap (algebraMap baseRing localRing) = basePrime := by
    rw [hP, Ideal.comap_comap, algAB_algebraMap_comp coordinateRing basePrime localRing, ← Ideal.comap_comap, hcomap, equality]
  have hPmax : primeIdeal = IsLocalRing.maximalIdeal localRing := by
    rw [← IsLocalization.map_under basePrime.primeCompl localRing primeIdeal, Ideal.under_def, hPR]
    exact IsLocalization.AtPrime.map_eq_maximalIdeal basePrime localRing
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
    (algebraMap localRing (LocB coordinateRing basePrime))
    (Algebra.IsIntegral.isIntegral (R := localRing)) _
    (by rw [← hP, hPmax]; exact IsLocalRing.maximalIdeal.isMaximal localRing)

def maxEquiv : MaximalSpectrum (LocB coordinateRing basePrime) ≃
    {coordinatePrime : PrimeSpectrum coordinateRing // coordinatePrime.asIdeal.comap (algebraMap baseRing coordinateRing) = basePrime} where
  toFun maximalIdeal := ⟨⟨maximalIdeal.asIdeal.comap (algebraMap coordinateRing (LocB coordinateRing basePrime)), inferInstance⟩,
    haveI := maximalIdeal.isMaximal; comap_R_of_isMaximal coordinateRing basePrime localRing maximalIdeal.asIdeal⟩
  invFun coordinatePrime := ⟨coordinatePrime.1.asIdeal.map (algebraMap coordinateRing (LocB coordinateRing basePrime)), isMaximal_map coordinateRing basePrime localRing coordinatePrime.2⟩
  left_inv maximalIdeal := MaximalSpectrum.ext
    (IsLocalization.map_under (Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl) _ maximalIdeal.asIdeal)
  right_inv coordinatePrime := Subtype.ext (PrimeSpectrum.ext
    (IsLocalization.under_map_of_isPrime_disjoint _ _ coordinatePrime.1.isPrime
      (disjoint_of_comap_eq coordinateRing basePrime coordinatePrime.2)))

end Max

section PerMax

variable [IsLocalRing localRing] [Module.Finite baseRing coordinateRing]
variable (maximalIdeal : Ideal (LocB coordinateRing basePrime)) [hm : maximalIdeal.IsMaximal]
variable (pointRing : Type u) [CommRing pointRing] [Algebra coordinateRing pointRing] [IsLocalRing pointRing]
  [IsLocalization.AtPrime pointRing (maximalIdeal.comap (algebraMap coordinateRing (LocB coordinateRing basePrime)))]

include localRing maximalIdeal

theorem isUnit_algebraMap_S (coordinate : Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl) :
    IsUnit (algebraMap coordinateRing pointRing coordinate) := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff pointRing (maximalIdeal.comap (algebraMap coordinateRing (LocB coordinateRing basePrime)))]
  exact Set.disjoint_left.mp (disjoint_of_comap_eq coordinateRing basePrime (comap_R_of_isMaximal coordinateRing basePrime localRing maximalIdeal)) coordinate.2

def toS : LocB coordinateRing basePrime →+* pointRing :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl)
    (g := algebraMap coordinateRing pointRing) (isUnit_algebraMap_S coordinateRing basePrime localRing maximalIdeal pointRing)

theorem toS_comp_algebraMap :
    (toS coordinateRing basePrime localRing maximalIdeal pointRing).comp (algebraMap coordinateRing (LocB coordinateRing basePrime)) = algebraMap coordinateRing pointRing :=
  IsLocalization.lift_comp _

theorem le_comap_toS : maximalIdeal ≤ (IsLocalRing.maximalIdeal pointRing).comap (toS coordinateRing basePrime localRing maximalIdeal pointRing) := by
  intro element hb
  obtain ⟨coordinate, denominator, rfl⟩ := IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl) element
  have hc : coordinate ∈ maximalIdeal.comap (algebraMap coordinateRing (LocB coordinateRing basePrime)) :=
    (IsLocalization.mk'_mem_iff (M := Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl)
      (S := LocB coordinateRing basePrime)).mp hb
  rw [Ideal.mem_comap, toS, IsLocalization.lift_mk']
  exact Ideal.mul_mem_right _ _
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff pointRing _ coordinate).mpr hc)

theorem inertiaDeg_eq (localMap : localRing →+* pointRing)
    (hφ : localMap.comp (algebraMap baseRing localRing) = (algebraMap coordinateRing pointRing).comp (algebraMap baseRing coordinateRing)) [IsLocalHom localMap] :
    letI := algAB coordinateRing basePrime localRing
    maximalIdeal.inertiaDeg localRing =
      letI := (IsLocalRing.ResidueField.map localMap).toAlgebra
      Module.finrank (IsLocalRing.ResidueField localRing) (IsLocalRing.ResidueField pointRing) := by
  let := algAB coordinateRing basePrime localRing
  have : maximalIdeal.LiesOver (IsLocalRing.maximalIdeal localRing) := ⟨(comap_A_of_isMaximal coordinateRing basePrime localRing maximalIdeal).symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal localRing)]
  let := (IsLocalRing.ResidueField.map localMap).toAlgebra
  set liftedMap := toS coordinateRing basePrime localRing maximalIdeal pointRing with hψdef
  have hψ : liftedMap.comp (algebraMap localRing (LocB coordinateRing basePrime)) = localMap := by
    refine IsLocalization.ringHom_ext basePrime.primeCompl ?_
    rw [RingHom.comp_assoc, algAB_algebraMap_comp, ← RingHom.comp_assoc,
      toS_comp_algebraMap, hφ]
  let j0 : LocB coordinateRing basePrime ⧸ maximalIdeal →+* IsLocalRing.ResidueField pointRing :=
    Ideal.Quotient.lift maximalIdeal ((IsLocalRing.residue pointRing).comp liftedMap) fun element hb ↦
      (IsLocalRing.residue_eq_zero_iff _).mpr (le_comap_toS coordinateRing basePrime localRing maximalIdeal pointRing hb)
  let : Field (LocB coordinateRing basePrime ⧸ maximalIdeal) := Ideal.Quotient.field maximalIdeal
  have hj0 : ∀ coordinate : coordinateRing, j0 (Ideal.Quotient.mk maximalIdeal (algebraMap coordinateRing _ coordinate)) =
      IsLocalRing.residue pointRing (algebraMap coordinateRing pointRing coordinate) := fun coordinate ↦ by
    simp only [j0, Ideal.Quotient.lift_mk, RingHom.comp_apply]
    rw [← RingHom.comp_apply liftedMap, toS_comp_algebraMap]
  have hinj : Function.Injective j0 := j0.injective
  have hsurj : Function.Surjective j0 := by
    intro residueElement
    obtain ⟨pointElement, rfl⟩ := IsLocalRing.residue_surjective residueElement
    obtain ⟨⟨coordinate, denominator⟩, hst⟩ := IsLocalization.surj (maximalIdeal.comap (algebraMap coordinateRing (LocB coordinateRing basePrime))).primeCompl pointElement
    have ht : IsLocalRing.residue pointRing (algebraMap coordinateRing pointRing denominator) ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff pointRing
        (maximalIdeal.comap (algebraMap coordinateRing (LocB coordinateRing basePrime)))]
      exact denominator.2
    refine ⟨Ideal.Quotient.mk maximalIdeal (algebraMap coordinateRing _ coordinate) * (Ideal.Quotient.mk maximalIdeal (algebraMap coordinateRing _ denominator))⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hj0, hj0, ← hst, map_mul, mul_assoc, mul_inv_cancel₀ ht, mul_one]
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _) (RingEquiv.ofBijective j0 ⟨hinj, hsurj⟩) ?_
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun scalar ↦ ?_)
  show IsLocalRing.ResidueField.map localMap (IsLocalRing.residue localRing scalar) =
    j0 (algebraMap (localRing ⧸ IsLocalRing.maximalIdeal localRing) (LocB coordinateRing basePrime ⧸ maximalIdeal) (Ideal.Quotient.mk _ scalar))
  rw [IsLocalRing.ResidueField.map_residue, Ideal.Quotient.algebraMap_mk_of_liesOver]
  simp only [j0, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  rw [← RingHom.comp_apply liftedMap, hψ]

theorem exists_ord_eq (functionField : Type u) [Field functionField] [Algebra coordinateRing functionField] [IsFractionRing coordinateRing functionField] [IsDomain coordinateRing]
    (hinj : Function.Injective (algebraMap baseRing coordinateRing)) [Algebra pointRing functionField] [IsScalarTower coordinateRing pointRing functionField]
    (element : LocB coordinateRing basePrime) :
    letI := algBL coordinateRing basePrime functionField hinj
    ∃ pointElement : pointRing, algebraMap pointRing functionField pointElement = algebraMap (LocB coordinateRing basePrime) functionField element ∧
      Ring.ord pointRing pointElement = Ring.ord (Localization.AtPrime maximalIdeal) (algebraMap (LocB coordinateRing basePrime) _ element) := by
  let := algBL coordinateRing basePrime functionField hinj
  have := tower_CBL coordinateRing basePrime functionField hinj
  let localizedPointRing := Localization.AtPrime maximalIdeal
  let equivalence : pointRing ≃ₐ[coordinateRing] localizedPointRing :=
    IsLocalization.algEquiv (maximalIdeal.comap (algebraMap coordinateRing (LocB coordinateRing basePrime))).primeCompl pointRing localizedPointRing
  refine ⟨equivalence.symm (algebraMap (LocB coordinateRing basePrime) localizedPointRing element), ?_, ?_⟩
  · have key : ((algebraMap pointRing functionField).comp (equivalence.symm : localizedPointRing →+* pointRing)).comp (algebraMap (LocB coordinateRing basePrime) localizedPointRing) =
        algebraMap (LocB coordinateRing basePrime) functionField := by
      refine IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid coordinateRing basePrime.primeCompl) ?_
      ext coordinate
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply coordinateRing (LocB coordinateRing basePrime) localizedPointRing,
        ← IsScalarTower.algebraMap_apply coordinateRing (LocB coordinateRing basePrime) functionField]
      show algebraMap pointRing functionField (equivalence.symm (algebraMap coordinateRing localizedPointRing coordinate)) = _
      rw [equivalence.symm.commutes, ← IsScalarTower.algebraMap_apply coordinateRing pointRing functionField]
    exact congr($key element)
  · have := Ring.ord_ringEquiv equivalence.toRingEquiv (equivalence.symm (algebraMap (LocB coordinateRing basePrime) localizedPointRing element))
    rw [← this]
    congr 1
    exact equivalence.apply_symm_apply _

end PerMax

theorem height_eq_one_of_comap_eq [IsDomain baseRing] [IsNoetherianRing baseRing] [IsDomain coordinateRing]
    [Module.Finite baseRing coordinateRing] (hinj : Function.Injective (algebraMap baseRing coordinateRing)) (h𝔭 : basePrime.height = 1)
    {coordinatePrime : Ideal coordinateRing} [coordinatePrime.IsPrime] (equality : coordinatePrime.comap (algebraMap baseRing coordinateRing) = basePrime) : coordinatePrime.height = 1 := by
  have : IsNoetherianRing coordinateRing := IsNoetherianRing.of_finite baseRing coordinateRing
  have : coordinatePrime.LiesOver basePrime := ⟨equality.symm⟩
  refine le_antisymm (h𝔭 ▸ Ideal.height_le_of_liesOver_of_finite_fiber basePrime coordinatePrime) ?_
  rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  rintro rfl
  rw [Ideal.comap_bot_of_injective _ hinj] at equality
  exact Ideal.ne_bot_of_height_eq_one h𝔭 equality.symm

end FiniteLocalModel

end
