module

public import BondalThomsen.Ports.MiyaokaMori.Nef.DimensionCycle
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical

universe u

noncomputable section

namespace AlgebraicGeometry.Intersection

structure LocalPrincipalEquation (scheme : Scheme.{u}) [IsIntegral scheme]
    [IsLocallyNoetherian scheme] (point : scheme) where
  function : scheme.functionField
  ne_zero : function ≠ 0

namespace LocalPrincipalEquation

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme] {point : scheme}

def order (_coheightOne : coheight point = 1) (equation : LocalPrincipalEquation scheme point) : ℤ :=
  Scheme.ord equation.function point

@[simp] theorem order_eq_ord (coheightOne : coheight point = 1)
    (equation : LocalPrincipalEquation scheme point) :
    equation.order coheightOne = Scheme.ord equation.function point := rfl

def mul (first second : LocalPrincipalEquation scheme point) : LocalPrincipalEquation scheme point :=
  ⟨first.function * second.function, mul_ne_zero first.ne_zero second.ne_zero⟩

end LocalPrincipalEquation

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]

def IsUnitRatioOn (region : scheme.Opens) (first second : scheme.functionField) : Prop :=
  ∀ (nonempty : Nonempty region),
    letI : Nonempty region := nonempty
    ∃ sectionValue : Γ(scheme, region), IsUnit sectionValue ∧
      scheme.germToFunctionField region sectionValue = first / second

structure CartierLocalData (scheme : Scheme.{u}) [IsIntegral scheme]
    [IsLocallyNoetherian scheme] where
  index : Type u
  opens : index → scheme.Opens
  cover : ⋃ chart, (opens chart : Set scheme) = Set.univ
  locallyFinite : LocallyFinite (fun chart => (opens chart : Set scheme))
  equation : index → scheme.functionField
  equation_ne_zero : ∀ chart, equation chart ≠ 0
  ratio_unit : ∀ first second,
    IsUnitRatioOn (opens first ⊓ opens second) (equation first) (equation second)

namespace CartierLocalData

def indexAt (datum : CartierLocalData scheme) (point : scheme) : datum.index :=
  let contains : point ∈ ⋃ chart, (datum.opens chart : Set scheme) := by
    rw [datum.cover]
    exact Set.mem_univ point
  Classical.choose (Set.mem_iUnion.mp contains)

theorem indexAt_mem (datum : CartierLocalData scheme) (point : scheme) :
    point ∈ datum.opens (datum.indexAt point) := by
  let contains : point ∈ ⋃ chart, (datum.opens chart : Set scheme) := by
    rw [datum.cover]
    exact Set.mem_univ point
  exact Classical.choose_spec (Set.mem_iUnion.mp contains)

def coefficient (datum : CartierLocalData scheme) (point : scheme) : ℤ :=
  if _coheightOne : coheight point = 1 then Scheme.ord (datum.equation (datum.indexAt point)) point else 0

@[simp] theorem coefficient_eq_ord (datum : CartierLocalData scheme) (point : scheme)
    (coheightOne : coheight point = 1) :
    datum.coefficient point = Scheme.ord (datum.equation (datum.indexAt point)) point := by
  simp [coefficient, coheightOne]

@[simp] theorem coefficient_eq_zero_of_coheight_ne_one (datum : CartierLocalData scheme)
    (point : scheme) (different : coheight point ≠ 1) : datum.coefficient point = 0 := by
  simp [coefficient, different]

theorem coefficient_eq_of_mem (datum : CartierLocalData scheme) (point : scheme)
    (_coheightOne : coheight point = 1) (first second : datum.index)
    (firstContains : point ∈ datum.opens first) (secondContains : point ∈ datum.opens second) :
    Scheme.ord (datum.equation first) point = Scheme.ord (datum.equation second) point := by
  have overlapNonempty : Nonempty ↑(datum.opens first ⊓ datum.opens second) :=
    ⟨⟨point, firstContains, secondContains⟩⟩
  let : Nonempty ↑(datum.opens first ⊓ datum.opens second) := overlapNonempty
  obtain ⟨sectionValue, unitProof, ratioEquation⟩ := datum.ratio_unit first second overlapNonempty
  have contains : point ∈ datum.opens first ⊓ datum.opens second := ⟨firstContains, secondContains⟩
  have unitOrder : Scheme.ord (datum.equation first / datum.equation second) point = 0 := by
    rw [← ratioEquation]
    exact Scheme.ord_of_isUnit unitProof contains
  calc
    Scheme.ord (datum.equation first) point =
        Scheme.ord ((datum.equation first / datum.equation second) * datum.equation second) point := by
      rw [div_mul_cancel₀ _ (datum.equation_ne_zero second)]
    _ = Scheme.ord (datum.equation first / datum.equation second) point +
        Scheme.ord (datum.equation second) point :=
      Scheme.ord_mul (x := point)
        (div_ne_zero (datum.equation_ne_zero first) (datum.equation_ne_zero second))
        (datum.equation_ne_zero second)
    _ = Scheme.ord (datum.equation second) point := by rw [unitOrder, zero_add]

end CartierLocalData

structure FiniteCartierDivisor (scheme : Scheme.{u}) [IsIntegral scheme]
    [IsLocallyNoetherian scheme] extends CartierLocalData scheme where
  finite_support : (Function.support toCartierLocalData.coefficient).Finite

namespace FiniteCartierDivisor

@[simp] theorem coefficient_eq_ord (divisor : FiniteCartierDivisor scheme) (point : scheme)
    (coheightOne : coheight point = 1) : divisor.toCartierLocalData.coefficient point =
      Scheme.ord (divisor.equation (divisor.indexAt point)) point :=
  divisor.toCartierLocalData.coefficient_eq_ord point coheightOne

structure ZeroDimensionalSupport (divisor : FiniteCartierDivisor scheme) : Prop where
  pointClosureDimension_zero : ∀ point, divisor.toCartierLocalData.coefficient point ≠ 0 →
    pointClosureDimension scheme point = 0

def zeroCycle (divisor : FiniteCartierDivisor scheme) (support : divisor.ZeroDimensionalSupport) :
    DimensionCycle scheme 0 :=
  ⟨{
      toFun := divisor.toCartierLocalData.coefficient
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := by
        intro point _
        exact ⟨Set.univ, Filter.univ_mem, by simpa using divisor.finite_support⟩ },
    isDimensionCycle_of_pointClosureDimension fun point nonzero =>
      support.pointClosureDimension_zero point nonzero⟩

@[simp] theorem zeroCycle_apply (divisor : FiniteCartierDivisor scheme)
    (support : divisor.ZeroDimensionalSupport) (point : scheme) :
    (divisor.zeroCycle support).1 point = divisor.toCartierLocalData.coefficient point := rfl

end FiniteCartierDivisor

end AlgebraicGeometry.Intersection
