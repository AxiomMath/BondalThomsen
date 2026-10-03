module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Set

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {scheme : Scheme.{u}} [IsIntegral scheme] [IsLocallyNoetherian scheme]

theorem finite_ord_ne_zero_inter_opens (region : scheme.Opens)
    [TopologicalSpace.NoetherianSpace region] (rational : scheme.functionField) :
    {point : scheme | point ∈ region ∧ scheme.ord rational point ≠ 0}.Finite := by
  classical
  by_cases zero : rational = 0
  · refine Set.Finite.subset Set.finite_empty ?_
    intro point contains
    exact absurd (by rw [zero]; simp) contains.2
  obtain ⟨unitRegion, -, unitSection, regionNonempty, germEquation, unitProof⟩ :=
    AlgebraicGeometry.exists_isUnit_germ_eq scheme rational zero
  have : Nonempty unitRegion := regionNonempty
  have genericContains : (⊤ : scheme) ∈ unitRegion := by
    obtain ⟨point, contains⟩ := (inferInstance : Nonempty unitRegion)
    exact (genericPoint_specializes point).mem_open unitRegion.isOpen contains
  set complement : Set region := {point : region | (point : scheme) ∉ unitRegion}
  have complementClosed : IsClosed complement := by
    have equation : complement = ((↑) : region → scheme) ⁻¹' ((unitRegion : Set scheme)ᶜ) := rfl
    rw [equation]
    exact (isClosed_compl_iff.mpr unitRegion.isOpen).preimage continuous_subtype_val
  obtain ⟨components, finiteComponents, closedComponents, irreducibleComponents, cover⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible complementClosed
  have : Finite components := finiteComponents
  let genericPoints : components → scheme := fun component =>
    ((irreducibleComponents component.1 component.2).genericPoint).val
  apply (Set.finite_range genericPoints).subset
  rintro point ⟨contains, orderNonzero⟩
  have unitAbsent : point ∉ unitRegion := by
    intro unitContains
    exact orderNonzero (germEquation ▸ Scheme.ord_of_isUnit unitProof unitContains)
  have coheightOne : Order.coheight point = 1 := by
    by_contra different
    exact orderNonzero (Scheme.ord_eq_zero_of_coheight_neq_one different rational)
  have complementContains : (⟨point, contains⟩ : region) ∈ complement := unitAbsent
  obtain ⟨component, componentContains, pointContains⟩ := Set.mem_sUnion.mp (cover ▸ complementContains)
  refine ⟨⟨component, componentContains⟩, ?_⟩
  show ((irreducibleComponents component componentContains).genericPoint).val = point
  set generic := (irreducibleComponents component componentContains).genericPoint
  have genericProof : IsGenericPoint generic component :=
    (irreducibleComponents component componentContains).isGenericPoint_genericPoint
      (closedComponents component componentContains)
  have componentSubset : component ⊆ complement := by
    intro element contains
    rw [cover]
    exact Set.subset_sUnion_of_mem componentContains contains
  have genericAbsent : generic.val ∉ unitRegion := componentSubset genericProof.mem
  have genericNotTop : ¬(⊤ : scheme) ≤ generic.val := by
    intro specialization
    exact genericAbsent ((Scheme.le_iff_specializes.mp specialization).mem_open
      unitRegion.isOpen genericContains)
  have coheightPositive : 0 < Order.coheight generic.val :=
    Order.coheight_pos_of_lt_top (lt_of_le_not_ge le_top genericNotTop)
  have specialization : generic.val ⤳ point :=
    (genericProof.specializes pointContains).map continuous_subtype_val
  have pointBelow : point ≤ generic.val := Scheme.le_iff_specializes.mpr specialization
  have coheightBound : Order.coheight generic.val ≤ 1 := by
    rw [← coheightOne]
    exact Order.coheight_anti pointBelow
  by_cases genericBelow : generic.val ≤ point
  · exact ((Scheme.le_iff_specializes.mp pointBelow).antisymm
      (Scheme.le_iff_specializes.mp genericBelow)).eq
  · exfalso
    have strictlyBelow : point < generic.val := lt_of_le_not_ge pointBelow genericBelow
    have coheightStrict : Order.coheight generic.val < Order.coheight point :=
      Order.coheight_strictAnti strictlyBelow (coheightBound.trans_lt (by simp))
    rw [coheightOne] at coheightStrict
    exact absurd (Order.lt_one_iff.mp coheightStrict) (ne_of_gt coheightPositive)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Divisors

theorem finite_support_ord (scheme : Scheme.{u}) [IsIntegral scheme] [IsNoetherian scheme]
    (rational : scheme.functionField) (_nonzero : rational ≠ 0) :
    (Function.support (scheme.ord rational)).Finite := by
  have : TopologicalSpace.NoetherianSpace (⊤ : scheme.Opens) :=
    TopologicalSpace.NoetherianSpace.set ((⊤ : scheme.Opens) : Set scheme)
  refine (Scheme.finite_ord_ne_zero_inter_opens (⊤ : scheme.Opens) rational).subset ?_
  intro point nonzero
  exact ⟨trivial, nonzero⟩

end AlgebraicGeometry.Divisors
