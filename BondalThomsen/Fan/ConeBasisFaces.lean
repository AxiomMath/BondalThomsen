module

public import BondalThomsen.Fan.ConeCoordinates
public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Face.Exposed
public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Face.Finite

@[expose] public section

namespace BondalThomsen

open Set Module

variable {Ambient Index : Type*} [AddCommGroup Ambient] [Module ℝ Ambient]
    [Fintype Index]

omit [Fintype Index] in

theorem basisSubsetCone_isFaceOf (basis : Basis Index ℝ Ambient)
    (selected : Set Ambient) (subset : selected ⊆ Set.range basis) :
    (PointedCone.hull ℝ selected).IsFaceOf (PointedCone.hull ℝ (Set.range basis)) := by
  classical
  let functional := basis.constr ℝ (fun index => if basis index ∈ selected then (0 : ℝ) else 1)
  have on_basis : ∀ index, functional (basis index) =
      if basis index ∈ selected then 0 else 1 := by
    intro index
    exact basis.constr_basis ℝ _ index
  have nonnegative : ∀ point ∈ PointedCone.hull ℝ (Set.range basis), 0 ≤ functional point := by
    intro point member
    induction member using Submodule.span_induction with
    | mem vector member =>
      obtain ⟨index, rfl⟩ := member
      rw [on_basis]
      split_ifs <;> norm_num
    | zero => simp
    | add first second _ _ first_nonnegative second_nonnegative =>
      rw [map_add]
      exact add_nonneg first_nonnegative second_nonnegative
    | smul scalar vector _ nonnegative =>
      change 0 ≤ functional ((scalar : ℝ) • vector)
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg scalar.property nonnegative
  have face := PointedCone.isFaceOf_inf_ker nonnegative
  have generating_intersection : Set.range basis ∩
      ((PointedCone.hull ℝ (Set.range basis) ⊓
        PointedCone.ofSubmodule functional.ker : PointedCone ℝ Ambient) : Set Ambient) =
      selected := by
    ext point
    constructor
    · rintro ⟨⟨index, rfl⟩, _, vanishes⟩
      change functional (basis index) = 0 at vanishes
      rw [on_basis] at vanishes
      split_ifs at vanishes with member
      · exact member
      · norm_num at vanishes
    · intro member
      obtain ⟨index, rfl⟩ := subset member
      refine ⟨⟨index, rfl⟩, PointedCone.subset_hull ⟨index, rfl⟩, ?_⟩
      change functional (basis index) = 0
      simp [on_basis, member]
  have face_eq := PointedCone.Face.eq_hull_inter_of_eq_hull
    ⟨_, face⟩ (Set.range basis) rfl
  change PointedCone.hull ℝ (Set.range basis) ⊓ PointedCone.ofSubmodule functional.ker =
    PointedCone.hull ℝ (Set.range basis ∩
      ((PointedCone.hull ℝ (Set.range basis) ⊓
        PointedCone.ofSubmodule functional.ker : PointedCone ℝ Ambient) : Set Ambient)) at face_eq
  rw [generating_intersection] at face_eq
  exact face_eq ▸ face

end BondalThomsen
