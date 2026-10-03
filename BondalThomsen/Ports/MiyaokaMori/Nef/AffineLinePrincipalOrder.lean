module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LocalUniformizerOrder
public import BondalThomsen.Ports.MiyaokaMori.Nef.SpecResidueDegree
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.LinearAlgebra.FreeModule.Norm

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical BigOperators

universe u

noncomputable section

namespace AlgebraicGeometry.AffineLinePrincipalOrder

variable (baseField : Type u) [Field baseField]

def polyToFunctionField : Polynomial baseField →+*
    (Spec (CommRingCat.of (Polynomial baseField))).functionField :=
  @algebraMap _ _ _ _ (instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Polynomial baseField)))

def structureMap : Spec (CommRingCat.of (Polynomial baseField)) ⟶ Spec (CommRingCat.of baseField) :=
  Spec.map (CommRingCat.ofHom (algebraMap baseField (Polynomial baseField)))

def spanPoint {polynomial : Polynomial baseField} (irreducible : Irreducible polynomial) :
    Spec (CommRingCat.of (Polynomial baseField)) :=
  ⟨Ideal.span {polynomial}, (Ideal.span_singleton_prime irreducible.ne_zero).mpr irreducible.prime⟩

def originPoint : Spec (CommRingCat.of (Polynomial baseField)) :=
  spanPoint baseField Polynomial.irreducible_X

theorem polyToFunctionField_injective : Function.Injective (polyToFunctionField baseField) := by
  let _ := instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Polynomial baseField))
  have _ := functionField_isFractionRing_of_affine (CommRingCat.of (Polynomial baseField))
  exact IsFractionRing.injective (CommRingCat.of (Polynomial baseField))
    (Spec (CommRingCat.of (Polynomial baseField))).functionField

theorem polyToFunctionField_ne_zero {polynomial : Polynomial baseField} (nonzero : polynomial ≠ 0) :
    polyToFunctionField baseField polynomial ≠ 0 :=
  (map_ne_zero_iff _ (polyToFunctionField_injective baseField)).mpr nonzero

theorem polyToFunctionField_eq_germ (polynomial : Polynomial baseField) :
    polyToFunctionField baseField polynomial =
      (Spec (CommRingCat.of (Polynomial baseField))).presheaf.germ ⊤ (genericPoint _) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial baseField))).inv polynomial) := rfl

theorem ord_polyToFunctionField_eq_zero_of_not_mem
    (point : Spec (CommRingCat.of (Polynomial baseField))) {polynomial : Polynomial baseField}
    (notMember : polynomial ∉ point.asIdeal) :
    (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField polynomial) point = 0 := by
  have contains : point ∈ (Spec (CommRingCat.of (Polynomial baseField))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial baseField))).inv polynomial) := by
    rw [basicOpen_eq_of_affine]
    exact notMember
  let : Nonempty ((Spec (CommRingCat.of (Polynomial baseField))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial baseField))).inv polynomial)) := ⟨⟨point, contains⟩⟩
  have restriction : polyToFunctionField baseField polynomial =
      (Spec (CommRingCat.of (Polynomial baseField))).germToFunctionField
        ((Spec (CommRingCat.of (Polynomial baseField))).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial baseField))).inv polynomial))
        ((Spec (CommRingCat.of (Polynomial baseField))).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial baseField))).inv polynomial)) := by
    rw [polyToFunctionField_eq_germ]
    exact ((Spec (CommRingCat.of (Polynomial baseField))).presheaf.germ_res_apply (homOfLE le_top)
      (genericPoint _) _ _).symm
  rw [restriction]
  exact Scheme.ord_of_isUnit (U := (Spec (CommRingCat.of (Polynomial baseField))).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial baseField))).inv polynomial))
    (RingedSpace.isUnit_res_basicOpen (Spec (CommRingCat.of (Polynomial baseField))).toRingedSpace _) contains

theorem height_span_singleton_eq_one {polynomial : Polynomial baseField}
    (irreducible : Irreducible polynomial) : (Ideal.span {polynomial}).height = 1 := by
  have : (Ideal.span {polynomial}).IsPrime :=
    (Ideal.span_singleton_prime irreducible.ne_zero).mpr irreducible.prime
  have upper : (Ideal.span {polynomial}).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {polynomial}) (Ideal.span {polynomial})
      (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
  have nonzero : (Ideal.span {polynomial}).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]
    exact irreducible.ne_zero
  exact le_antisymm upper (Order.one_le_iff_ne_zero.mpr nonzero)

theorem coheight_spanPoint {polynomial : Polynomial baseField} (irreducible : Irreducible polynomial) :
    Order.coheight (spanPoint baseField irreducible) = 1 := by
  rw [← idealHeight_eq_coheight]
  exact height_span_singleton_eq_one baseField irreducible

theorem ord_polyToFunctionField_spanPoint {polynomial : Polynomial baseField}
    (irreducible : Irreducible polynomial) :
    (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField polynomial)
      (spanPoint baseField irreducible) = 1 := by
  let : Nonempty (⊤ : (Spec (CommRingCat.of (Polynomial baseField))).Opens) :=
    ⟨⟨spanPoint baseField irreducible, trivial⟩⟩
  have : (spanPoint baseField irreducible).asIdeal.IsPrime := (spanPoint baseField irreducible).isPrime
  let _ : Algebra (Polynomial baseField)
      ((Spec (CommRingCat.of (Polynomial baseField))).presheaf.stalk (spanPoint baseField irreducible)) :=
    StructureSheaf.stalkAlgebra (Polynomial baseField) (spanPoint baseField irreducible)
  have : IsLocalization.AtPrime
      ((Spec (CommRingCat.of (Polynomial baseField))).presheaf.stalk (spanPoint baseField irreducible))
      (spanPoint baseField irreducible).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (Polynomial baseField) (spanPoint baseField irreducible)
  have : IsDiscreteValuationRing
      ((Spec (CommRingCat.of (Polynomial baseField))).presheaf.stalk (spanPoint baseField irreducible)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial baseField)
      (P := (spanPoint baseField irreducible).asIdeal) (by
        show Ideal.span {polynomial} ≠ ⊥
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact irreducible.ne_zero) _
  have generates : Ideal.span
      {(Spec (CommRingCat.of (Polynomial baseField))).presheaf.germ ⊤
        (spanPoint baseField irreducible) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial baseField))).inv polynomial)} =
      IsLocalRing.maximalIdeal
        ((Spec (CommRingCat.of (Polynomial baseField))).presheaf.stalk (spanPoint baseField irreducible)) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (spanPoint baseField irreducible).asIdeal]
    show Ideal.span {algebraMap (Polynomial baseField) _ polynomial} =
      Ideal.map (algebraMap (Polynomial baseField) _) (Ideal.span {polynomial})
    rw [Ideal.map_span, Set.image_singleton]
  exact Scheme.ord_germToFunctionField_eq_one_of_span_germ_eq_maximalIdeal (region := ⊤) trivial
    (coheight_spanPoint baseField irreducible) _ generates

theorem residueDegree_spanPoint {polynomial : Polynomial baseField} (irreducible : Irreducible polynomial) :
    (structureMap baseField).residueDegree (spanPoint baseField irreducible) = polynomial.natDegree := by
  have : (spanPoint baseField irreducible).asIdeal.IsPrime := (spanPoint baseField irreducible).isPrime
  have : (Ideal.span {polynomial}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible irreducible
  rw [structureMap, Scheme.Hom.residueDegree_specMap]
  have : ((Spec.map (CommRingCat.ofHom (algebraMap baseField (Polynomial baseField))))
      (spanPoint baseField irreducible)).asIdeal.IsPrime :=
    ((Spec.map (CommRingCat.ofHom (algebraMap baseField (Polynomial baseField))))
      (spanPoint baseField irreducible)).isPrime
  let _ : Algebra ((Spec.map (CommRingCat.ofHom (algebraMap baseField (Polynomial baseField))))
      (spanPoint baseField irreducible)).asIdeal.ResidueField (spanPoint baseField irreducible).asIdeal.ResidueField :=
    (Ideal.ResidueField.map _ _ (CommRingCat.ofHom (algebraMap baseField (Polynomial baseField))).hom rfl).toAlgebra
  change Module.finrank ((Spec.map (CommRingCat.ofHom (algebraMap baseField (Polynomial baseField))))
    (spanPoint baseField irreducible)).asIdeal.ResidueField
    (spanPoint baseField irreducible).asIdeal.ResidueField = polynomial.natDegree
  let sourceEquiv : ((Spec.map (CommRingCat.ofHom (algebraMap baseField (Polynomial baseField))))
      (spanPoint baseField irreducible)).asIdeal.ResidueField ≃+* baseField :=
    (Ideal.algEquivResidueFieldOfField _).symm.toRingEquiv
  let targetEquiv : (spanPoint baseField irreducible).asIdeal.ResidueField ≃+*
      (Polynomial baseField ⧸ Ideal.span {polynomial}) :=
    (RingEquiv.ofBijective
      (algebraMap (Polynomial baseField ⧸ Ideal.span {polynomial}) (Ideal.span {polynomial}).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField _)).symm
  rw [Algebra.finrank_eq_of_equiv_equiv sourceEquiv targetEquiv ?_]
  · exact finrank_quotient_span_eq_natDegree
  · ext scalar
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have sourceEquation : sourceEquiv (algebraMap baseField _ scalar) = scalar :=
      AlgEquiv.symm_apply_apply (Ideal.algEquivResidueFieldOfField _) scalar
    rw [sourceEquation]
    have mapEquation : algebraMap _ (spanPoint baseField irreducible).asIdeal.ResidueField
        (algebraMap baseField ((Spec.map (CommRingCat.ofHom (algebraMap baseField (Polynomial baseField))))
          (spanPoint baseField irreducible)).asIdeal.ResidueField scalar) =
        algebraMap (Polynomial baseField) (Ideal.span {polynomial}).ResidueField
          (algebraMap baseField (Polynomial baseField) scalar) :=
      Ideal.ResidueField.map_algebraMap _ _ _ rfl scalar
    rw [mapEquation, ← Ideal.algebraMap_quotient_residueField_mk]
    exact (RingEquiv.symm_apply_apply (RingEquiv.ofBijective
      (algebraMap (Polynomial baseField ⧸ Ideal.span {polynomial}) (Ideal.span {polynomial}).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField _))
      (Ideal.Quotient.mk _ (algebraMap baseField (Polynomial baseField) scalar))).symm

theorem residueDegree_originPoint : (structureMap baseField).residueDegree (originPoint baseField) = 1 := by
  rw [originPoint, residueDegree_spanPoint, Polynomial.natDegree_X]

theorem ord_polyToFunctionField_of_ne_spanPoint {polynomial : Polynomial baseField}
    (irreducible : Irreducible polynomial) (point : Spec (CommRingCat.of (Polynomial baseField)))
    (distinct : point ≠ spanPoint baseField irreducible) :
    (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField polynomial) point = 0 := by
  apply ord_polyToFunctionField_eq_zero_of_not_mem
  intro member
  apply distinct
  have subset : Ideal.span {polynomial} ≤ point.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr member
  have maximal : (Ideal.span {polynomial}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible irreducible
  exact PrimeSpectrum.ext (maximal.eq_of_le point.isPrime.ne_top subset).symm

theorem ord_pow_eq {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]
    {rational : scheme.functionField} (nonzero : rational ≠ 0) (exponent : ℕ) (point : scheme) :
    scheme.ord (rational ^ exponent) point = exponent * scheme.ord rational point := by
  induction exponent with
  | zero => simp [Scheme.ord_one_eq_zero]
  | succ exponent inductionHypothesis =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ nonzero) nonzero, inductionHypothesis]
    push_cast
    ring

theorem reciprocal_polynomial_ord_originPoint (polynomial : Polynomial baseField) (nonzero : polynomial ≠ 0) :
    (Spec (CommRingCat.of (Polynomial baseField))).ord
      (polyToFunctionField baseField polynomial.reverse /
        polyToFunctionField baseField Polynomial.X ^ polynomial.natDegree)
      (originPoint baseField) = -(polynomial.natDegree : ℤ) := by
  have reverseNonzero : polyToFunctionField baseField polynomial.reverse ≠ 0 :=
    polyToFunctionField_ne_zero baseField (Polynomial.reverse_eq_zero.not.mpr nonzero)
  have coordinateNonzero : polyToFunctionField baseField (Polynomial.X : Polynomial baseField) ≠ 0 :=
    polyToFunctionField_ne_zero baseField Polynomial.X_ne_zero
  rw [Scheme.ord_div_eq_sub reverseNonzero (pow_ne_zero _ coordinateNonzero), ord_pow_eq coordinateNonzero,
    originPoint, ord_polyToFunctionField_spanPoint baseField Polynomial.irreducible_X,
    ord_polyToFunctionField_eq_zero_of_not_mem]
  · ring
  · show polynomial.reverse ∉ Ideal.span {Polynomial.X}
    rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff, Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr nonzero

theorem finite_support_and_finsum (polynomial : Polynomial baseField) (nonzero : polynomial ≠ 0) :
    (Function.support fun point : Spec (CommRingCat.of (Polynomial baseField)) =>
      (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField polynomial) point).Finite ∧
    ∑ᶠ point : Spec (CommRingCat.of (Polynomial baseField)),
      (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField polynomial) point *
        ((structureMap baseField).residueDegree point : ℤ) = polynomial.natDegree := by
  induction polynomial using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl nonzero
  | h₂ polynomial unitProof =>
    have vanishes : ∀ point : Spec (CommRingCat.of (Polynomial baseField)),
        (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField polynomial) point = 0 :=
      fun point => ord_polyToFunctionField_eq_zero_of_not_mem baseField point
        (fun member => point.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ member unitProof))
    refine ⟨?_, ?_⟩
    · simp [vanishes]
    · simp [vanishes, Polynomial.natDegree_eq_zero_of_isUnit unitProof]
  | h₃ polynomial prime polynomialNonzero primeProof inductionHypothesis =>
    have irreducible : Irreducible prime := primeProof.irreducible
    obtain ⟨finiteSupport, weightedSum⟩ := inductionHypothesis polynomialNonzero
    have additive : ∀ point : Spec (CommRingCat.of (Polynomial baseField)),
        (Spec (CommRingCat.of (Polynomial baseField))).ord
            (polyToFunctionField baseField (prime * polynomial)) point =
          (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField prime) point +
            (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField polynomial) point := by
      intro point
      rw [map_mul, Scheme.ord_mul (polyToFunctionField_ne_zero baseField irreducible.ne_zero)
        (polyToFunctionField_ne_zero baseField polynomialNonzero)]
    have primeFiniteSupport : (Function.support fun point : Spec (CommRingCat.of (Polynomial baseField)) =>
        (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField prime) point).Finite := by
      refine (Set.finite_singleton (spanPoint baseField irreducible)).subset ?_
      intro point nonzeroOrder
      by_contra distinct
      exact nonzeroOrder (ord_polyToFunctionField_of_ne_spanPoint baseField irreducible point distinct)
    refine ⟨?_, ?_⟩
    · refine (primeFiniteSupport.union finiteSupport).subset ?_
      intro point nonzeroOrder
      rw [Function.mem_support, additive] at nonzeroOrder
      by_contra outside
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at outside
      exact nonzeroOrder (by rw [outside.1, outside.2, add_zero])
    · have primeWeightedFiniteSupport : (Function.support fun point : Spec (CommRingCat.of (Polynomial baseField)) =>
          (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField prime) point *
            ((structureMap baseField).residueDegree point : ℤ)).Finite :=
        primeFiniteSupport.subset (Function.support_mul_subset_left _ _)
      have weightedFiniteSupport : (Function.support fun point : Spec (CommRingCat.of (Polynomial baseField)) =>
          (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField polynomial) point *
            ((structureMap baseField).residueDegree point : ℤ)).Finite :=
        finiteSupport.subset (Function.support_mul_subset_left _ _)
      rw [finsum_congr (fun point => by rw [additive point, add_mul]),
        finsum_add_distrib primeWeightedFiniteSupport weightedFiniteSupport, weightedSum,
        finsum_eq_single _ (spanPoint baseField irreducible)
          (fun point distinct => by
            rw [ord_polyToFunctionField_of_ne_spanPoint baseField irreducible point distinct, zero_mul]),
        ord_polyToFunctionField_spanPoint, residueDegree_spanPoint,
        Polynomial.natDegree_mul irreducible.ne_zero polynomialNonzero]
      push_cast
      ring

theorem finite_support_ord (polynomial : Polynomial baseField) (nonzero : polynomial ≠ 0) :
    (Function.support fun point : Spec (CommRingCat.of (Polynomial baseField)) =>
      (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField polynomial) point).Finite :=
  (finite_support_and_finsum baseField polynomial nonzero).1

theorem finsum_ord_mul_residueDegree (polynomial : Polynomial baseField) (nonzero : polynomial ≠ 0) :
    ∑ᶠ point : Spec (CommRingCat.of (Polynomial baseField)),
      (Spec (CommRingCat.of (Polynomial baseField))).ord (polyToFunctionField baseField polynomial) point *
        ((structureMap baseField).residueDegree point : ℤ) = polynomial.natDegree :=
  (finite_support_and_finsum baseField polynomial nonzero).2

end AlgebraicGeometry.AffineLinePrincipalOrder
