module

public import BondalThomsen.Ports.MiyaokaMori.Nef.CartierFiniteSupport
public import BondalThomsen.Ports.MiyaokaMori.Nef.ZeroCycleDegreeAdditivity

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical BigOperators

universe u

noncomputable section

namespace AlgebraicGeometry.Intersection

section Local

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]

def principalCartierData (rational : scheme.functionFieldˣ) : CartierLocalData scheme where
  index := ULift.{u} (Fin 1)
  opens := fun _ => ⊤
  cover := by ext point; simp
  locallyFinite := locallyFinite_of_finite _
  equation := fun _ => (rational : scheme.functionField)
  equation_ne_zero := fun _ => rational.ne_zero
  ratio_unit := by
    intro first second nonempty
    let : Nonempty ↑((⊤ : scheme.Opens) ⊓ ⊤) := nonempty
    refine ⟨1, isUnit_one, ?_⟩
    simp [rational.ne_zero]

@[simp] theorem principalCartierData_coefficient (rational : scheme.functionFieldˣ) (point : scheme) :
    (principalCartierData rational).coefficient point = scheme.ord (rational : scheme.functionField) point := by
  by_cases coheightOne : coheight point = 1
  · rw [CartierLocalData.coefficient_eq_ord _ point coheightOne]
    rfl
  · rw [CartierLocalData.coefficient_eq_zero_of_coheight_ne_one _ point coheightOne,
      Scheme.ord_eq_zero_of_coheight_neq_one coheightOne]

@[simp] theorem principalCartierData_coefficient_one (point : scheme) :
    (principalCartierData (1 : scheme.functionFieldˣ)).coefficient point = 0 := by
  rw [principalCartierData_coefficient]
  have : Nonempty ↑(⊤ : scheme.Opens) := ⟨⟨point, Set.mem_univ point⟩⟩
  have unitOrder := Scheme.ord_of_isUnit (X := scheme) (U := ⊤) (f := (1 : Γ(scheme, ⊤)))
    isUnit_one (x := point) (by trivial)
  simpa only [map_one, Units.val_one] using unitOrder

end Local

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsNoetherian scheme]

@[simp] theorem principalCartierData_zeroCycle_apply (dimensionBound : topologicalKrullDim scheme ≤ 1)
    (rational : scheme.functionFieldˣ) (point : scheme) :
    ((principalCartierData rational).zeroCycle dimensionBound).1 point =
      scheme.ord (rational : scheme.functionField) point :=
  principalCartierData_coefficient rational point

theorem principalCartierData_zeroCycle_eq_zero_of_dim_lt_one
    (dimensionBound : topologicalKrullDim scheme < 1) (rational : scheme.functionFieldˣ) :
    (principalCartierData rational).zeroCycle dimensionBound.le = DimensionCycle.zero scheme 0 := by
  have krullBound : Order.krullDim scheme < 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := scheme))]
    exact dimensionBound
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro point
  apply (principalCartierData rational).coefficient_eq_zero_of_coheight_ne_one point
  intro coheightOne
  have coheightBound := Order.coheight_le_krullDim point
  rw [coheightOne] at coheightBound
  exact (not_le_of_gt krullBound) coheightBound

theorem rawZeroCycleDegree_principal_eq_sum {baseField : Type u} [Field baseField]
    (structureMap : scheme ⟶ Spec (CommRingCat.of baseField)) [IsProper structureMap]
    (dimensionBound : topologicalKrullDim scheme ≤ 1) (rational : scheme.functionFieldˣ) :
    rawZeroCycleDegree structureMap ((principalCartierData rational).zeroCycle dimensionBound) =
      ∑ point ∈ (AlgebraicGeometry.Divisors.finite_support_ord scheme
        (rational : scheme.functionField) rational.ne_zero).toFinset,
        scheme.ord (rational : scheme.functionField) point * (residueFieldDegree structureMap point : ℤ) := by
  rw [rawZeroCycleDegree_eq_sum_on structureMap _
    (AlgebraicGeometry.Divisors.finite_support_ord scheme
      (rational : scheme.functionField) rational.ne_zero).toFinset (by
      intro point absent
      rw [principalCartierData_zeroCycle_apply]
      by_contra nonzero
      exact absent ((AlgebraicGeometry.Divisors.finite_support_ord scheme
        (rational : scheme.functionField) rational.ne_zero).mem_toFinset.mpr nonzero))]
  exact Finset.sum_congr rfl fun point _ => by rw [principalCartierData_zeroCycle_apply]

end AlgebraicGeometry.Intersection
