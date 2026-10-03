module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.Intersection

abbrev pointClosureDimension (scheme : Scheme.{u}) (point : scheme) : WithBot ℕ∞ :=
  ((Order.height point : ℕ∞) : WithBot ℕ∞)

theorem _root_.topologicalKrullDim_closure_singleton_eq_height
    {space : Type*} [TopologicalSpace space] [QuasiSober space] [T0Space space]
    (point : space) :
    topologicalKrullDim (closure ({point} : Set space)) =
      ((@Order.height space (specializationPreorder space) point : ℕ∞) : WithBot ℕ∞) := by
  let orderSpace : Preorder space := specializationPreorder space
  have : QuasiSober (closure ({point} : Set space)) :=
    (isClosed_closure.isClosedEmbedding_subtypeVal).quasiSober
  have contains : ∀ element : space,
      element ∈ closure ({point} : Set space) ↔ element ∈ Set.Iic point := fun element =>
    specializes_iff_mem_closure.symm
  let equivalence : @OrderIso (closure ({point} : Set space)) (Set.Iic point)
      (specializationOrder (closure ({point} : Set space))).toLE _ :=
    { toFun := fun element => ⟨element.1, (contains _).mp element.2⟩
      invFun := fun element => ⟨element.1, (contains _).mpr element.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := fun {first second} =>
        show (second : space) ⤳ (first : space) ↔ second ⤳ first from
          (subtype_specializes_iff second first).symm }
  rw [topologicalKrullDim, Order.height_eq_krullDim_Iic]
  exact @Order.krullDim_eq_of_orderIso _ _ _ _
    (@OrderIso.trans _ _ _ _ (specializationOrder (closure ({point} : Set space))).toLE _
      irreducibleSetEquivPoints equivalence)

theorem pointClosureDimension_eq_height (scheme : Scheme.{u}) (point : scheme) :
    pointClosureDimension scheme point = ((Order.height point : ℕ∞) : WithBot ℕ∞) :=
  rfl

theorem pointClosureDimension_eq_topologicalKrullDim_closure
    (scheme : Scheme.{u}) (point : scheme) :
    pointClosureDimension scheme point = topologicalKrullDim (closure ({point} : Set scheme)) :=
  (topologicalKrullDim_closure_singleton_eq_height point).symm

theorem pointClosureDimension_eq_natCast_iff
    (scheme : Scheme.{u}) (point : scheme) (dimension : ℕ) :
    pointClosureDimension scheme point = (dimension : WithBot ℕ∞) ↔
      Order.height point = (dimension : ℕ∞) := by
  rw [pointClosureDimension_eq_height]
  exact_mod_cast Iff.rfl

def _root_.AlgebraicGeometry.cycleSubgroup (scheme : Scheme.{u}) (dimension : ℕ) :
    AddSubgroup (AlgebraicCycle scheme ℤ) where
  carrier := {cycle | ∀ point : scheme, cycle point ≠ 0 → Order.height point = (dimension : ℕ∞)}
  add_mem' := by
    intro first second firstDimension secondDimension point nonzero
    by_cases zero : first point = 0
    · exact secondDimension point (by simpa [zero] using nonzero)
    · exact firstDimension point zero
  zero_mem' := fun _ nonzero => (nonzero rfl).elim
  neg_mem' := by
    intro cycle dimensionProof point nonzero
    exact dimensionProof point (by simpa using nonzero)

theorem _root_.AlgebraicGeometry.mem_cycleSubgroup_iff_pointClosureDimension
    {scheme : Scheme.{u}} {dimension : ℕ} (cycle : AlgebraicCycle scheme ℤ) :
    cycle ∈ AlgebraicGeometry.cycleSubgroup scheme dimension ↔
      ∀ point : scheme, cycle point ≠ 0 →
        pointClosureDimension scheme point = (dimension : WithBot ℕ∞) :=
  forall_congr' fun point => imp_congr_right fun _ =>
    (pointClosureDimension_eq_natCast_iff scheme point dimension).symm

abbrev IsDimensionCycle (scheme : Scheme.{u}) (dimension : ℕ)
    (cycle : AlgebraicCycle scheme ℤ) : Prop :=
  cycle ∈ AlgebraicGeometry.cycleSubgroup scheme dimension

abbrev DimensionCycle (scheme : Scheme.{u}) (dimension : ℕ) :=
  ↥(AlgebraicGeometry.cycleSubgroup scheme dimension)

theorem isDimensionCycle_of_pointClosureDimension {scheme : Scheme.{u}} {dimension : ℕ}
    {cycle : AlgebraicCycle scheme ℤ}
    (dimensionProof : ∀ point : scheme, cycle point ≠ 0 →
      pointClosureDimension scheme point = (dimension : WithBot ℕ∞)) :
    IsDimensionCycle scheme dimension cycle :=
  (AlgebraicGeometry.mem_cycleSubgroup_iff_pointClosureDimension cycle).mpr dimensionProof

end AlgebraicGeometry.Intersection
