module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Face.Finite

@[expose] public section

namespace PointedCone

variable {R M ι : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  {v : ι → M} {A : Set ι} {x : M}

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]

theorem mem_hull_image_iff_linearCombination :
    x ∈ hull R (v '' A) ↔
      ∃ c ∈ Finsupp.supported R R A, (∀ j, 0 ≤ c j) ∧ Finsupp.linearCombination R v c = x := by
  constructor
  · intro hx
    obtain ⟨c, hcA, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hx
    refine ⟨c.mapRange Subtype.val rfl, ?_, fun j ↦ (c j).2, ?_⟩
    · exact (Finsupp.mem_supported _ _).2 <| (Finset.coe_subset.2 Finsupp.support_mapRange).trans
        ((Finsupp.mem_supported _ _).1 hcA)
    · rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index (by simp)]
      exact Finsupp.sum_congr fun j _ ↦ Nonneg.coe_smul _ _
  · rintro ⟨c, hcA, hc0, rfl⟩
    rw [Finsupp.mem_supported] at hcA
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun j hj ↦ smul_mem _ (hc0 j) ?_
    exact subset_hull ⟨j, hcA hj, rfl⟩

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module R M] {C : PointedCone R M}

theorem isFaceOf_hull_image [NoZeroDivisors R] (hv : LinearIndependent R v)
    (hC : C = hull R (Set.range v)) (A : Set ι) : (hull R (v '' A)).IsFaceOf C := by
  subst hC
  refine ⟨Submodule.span_mono (Set.image_subset_range v A), ?_⟩
  intro x y a hx hy ha hxy
  rw [← Set.image_univ] at hx hy
  obtain ⟨c, -, hc0, rfl⟩ := mem_hull_image_iff_linearCombination.1 hx
  obtain ⟨d, -, hd0, rfl⟩ := mem_hull_image_iff_linearCombination.1 hy
  obtain ⟨e, heA, -, he⟩ := mem_hull_image_iff_linearCombination.1 hxy
  rw [Finsupp.mem_supported] at heA
  have hcd : a • c + d = e :=
    hv.finsuppLinearCombination_injective (by rw [map_add, map_smul, he])
  refine mem_hull_image_iff_linearCombination.2
    ⟨c, (Finsupp.mem_supported R c).2 fun j hj ↦ ?_, hc0, rfl⟩
  by_contra hjA
  have hej : e j = 0 := by
    by_contra hne
    exact hjA (heA (Finsupp.mem_support_iff.2 hne))
  have hsum : a * c j + d j = 0 := by
    simpa [hej] using congrArg (fun f : ι →₀ R ↦ f j) hcd
  have hac : a * c j = 0 :=
    ((add_eq_zero_iff_of_nonneg (mul_nonneg ha.le (hc0 j)) (hd0 j)).1 hsum).1
  exact (Finsupp.mem_support_iff.1 hj) ((mul_eq_zero.1 hac).resolve_left ha.ne')

theorem Face.eq_hull_image (F : C.Face) (hC : C = hull R (Set.range v)) :
    F.toPointedCone = hull R (v '' {j | v j ∈ F}) := by
  rw [F.eq_hull_inter_of_eq_hull (Set.range v) hC]
  refine congrArg (hull R) (Set.ext fun y ↦ ⟨?_, ?_⟩)
  · rintro ⟨⟨j, rfl⟩, hy⟩
    exact ⟨j, hy, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, rfl⟩, hj⟩

end AddCommGroup

end PointedCone

