module

public import BondalThomsen.Fan.StarRays
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem star_finrank_add_one (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    finrank ℝ (fan.StarAmbient ray) + 1 = finrank ℝ Ambient := by
  have nonzero : embedding ray.val ≠ 0 := by
    simpa only [map_zero] using fan.lattice.injective.ne ray.property.1.ne_zero
  simpa only [finrank_span_singleton nonzero] using
    (Submodule.span ℝ {embedding ray.val}).finrank_quotient_add_finrank

theorem star_isDeep_in_coneBasis (fan : TauCeti.Toric.Fan embedding) {dimension size : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (ray : fan.Ray)
    (star_basis : Basis (Fin size) ℤ (fan.StarLattice ray))
    (star_cone_basis : (fan.star ray).IsConeBasis star_basis) (other : (fan.star ray).Ray) :
    DeepCoordinates (fun index => star_basis.repr other.val index) := by
  classical
  let star_cone := PointedCone.hull ℝ
    (Set.range (fun index => fan.starEmbedding ray (star_basis index)))
  obtain ⟨original, ⟨original_member, contains⟩, projected_eq⟩ := star_cone_basis
  obtain ⟨source_size, basis, cone_basis, removed, equality, original_face⟩ :=
    fan.exists_coneBasis_above_containing_ray complete regular ray original original_member contains
  have source_size_eq : source_size = dimension := by
    have ranks := (finrank_eq_card_basis basis).symm.trans (finrank_eq_card_basis reference)
    simpa only [Fintype.card_fin] using ranks
  subst source_size
  let quotient_basis := basisVectorQuotient basis removed ray.val equality
  have descends := rayQuotient_map_isFaceOf _ original_face contains
  change (PointedCone.map (fan.starProjection ray) original).IsFaceOf
    (PointedCone.map (fan.starProjection ray) _) at descends
  rw [projected_eq, fan.starConeBasis_eq_hull basis ray removed equality] at descends
  have full_span : Submodule.span ℝ (star_cone : Set (fan.StarAmbient ray)) = ⊤ := by
    let real_basis := (fan.star ray).lattice.isBaseChange.basis star_basis
    have real_range : Set.range (fun index => fan.starEmbedding ray (star_basis index)) =
        Set.range real_basis := by
      apply congrArg Set.range
      funext index
      exact ((fan.star ray).lattice.isBaseChange.basis_apply star_basis index).symm
    apply top_unique
    rw [← real_basis.span_eq, ← real_range]
    exact Submodule.span_mono PointedCone.subset_hull
  have same_cone := face_eq_of_fullSpan descends full_span
  obtain ⟨matching, injective, coordinates⟩ := TauCeti.Toric.basisCone_change_coordinates
    (fan.star ray).lattice star_basis quotient_basis same_cone
    ((fan.star ray).isToricCone
      (show star_cone ∈ (fan.star ray).cones from
        ⟨original, ⟨original_member, contains⟩, projected_eq⟩)).salient
  have quotient_deep := fan.starRay_deep_in_quotientBasis complete regular deep basis
    cone_basis ray removed equality other
  have restricted := quotient_deep.comp matching injective
  convert restricted using 1
  funext index
  exact coordinates other.val index

theorem star_isDeep (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (ray : fan.Ray) :
    (fan.star ray).IsDeep (dimension - 1) := by
  intro basis cone_basis other
  exact fan.star_isDeep_in_coneBasis complete regular deep reference ray basis cone_basis other

theorem star_complete_regular_deep (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (ray : fan.Ray) :
    (fan.star ray).IsComplete ∧ (fan.star ray).IsRegular ∧
      (fan.star ray).IsDeep (dimension - 1) :=
  ⟨fan.star_isComplete complete regular deep reference ray,
    fan.star_isRegular complete regular ray,
    fan.star_isDeep complete regular deep reference ray⟩

end TauCeti.Toric.Fan
