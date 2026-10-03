module

public import BondalThomsen.Toric.Divisor.DivisorLineBundle

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CartierEquationAtlas

universe schemeUniverse

variable {SchemeModel : Scheme.{schemeUniverse}} [IsIntegral SchemeModel]

theorem cartierDivisor_eq_of_overlap_units
    (first second : CartierEquationAtlas SchemeModel)
    (ratios : ∀ firstIndex secondIndex,
      letI := first.nonempty_chart firstIndex
      letI := second.nonempty_chart secondIndex
      letI := nonempty_integral_open_intersection
        (first.chart firstIndex) (second.chart secondIndex)
      ∃ unit : Γ(SchemeModel, first.chart firstIndex ⊓ second.chart secondIndex)ˣ,
        TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField SchemeModel
          (first.chart firstIndex ⊓ second.chart secondIndex) unit *
          second.equation secondIndex = first.equation firstIndex) :
    first.cartierDivisor = second.cartierDivisor := by
  apply first.existsUnique_cartierDivisor.unique
  · exact first.cartierDivisor_restrict
  · intro firstIndex
    let common := fun secondIndex => first.chart firstIndex ⊓ second.chart secondIndex
    apply (TauCeti.AlgebraicGeometry.Scheme.cartierDivisorSheaf SchemeModel).eq_of_locally_eq'
      common (first.chart firstIndex) (fun _ => homOfLE inf_le_left)
    · intro point contains
      have covered : point ∈ iSup second.chart := by
        rw [second.covers.iSup_eq_top]
        trivial
      obtain ⟨secondIndex, member⟩ := Opens.mem_iSup.mp covered
      exact Opens.mem_iSup.mpr ⟨secondIndex, contains, member⟩
    · intro secondIndex
      let := first.nonempty_chart firstIndex
      let := second.nonempty_chart secondIndex
      let := nonempty_integral_open_intersection
        (first.chart firstIndex) (second.chart secondIndex)
      change second.cartierDivisor |_ first.chart firstIndex |_ common secondIndex =
        first.localClass firstIndex |_ common secondIndex
      rw [TopCat.Presheaf.restrict_restrict inf_le_left le_top]
      have restriction := congrArg (fun localSection => localSection |_ common secondIndex)
        (second.cartierDivisor_restrict secondIndex)
      rw [TopCat.Presheaf.restrict_restrict inf_le_right le_top] at restriction
      rw [restriction]
      unfold localClass
      rw [TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_restrict SchemeModel
        inf_le_right, TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_restrict
        SchemeModel inf_le_left]
      exact ((TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
        SchemeModel _ (first.equation firstIndex) (second.equation secondIndex)).mpr
          (ratios firstIndex secondIndex)).symm

end BondalThomsen.CartierEquationAtlas

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem realCharacter_eqOn_cone_of_ray_eq (fan : Fan embedding)
    (cone : fan.cones) (first second : Lattice →+ ℤ)
    (agree : ∀ ray : fan.Ray, embedding ray.val ∈ cone.val →
      first ray.val = second ray.val) :
    Set.EqOn (fan.lattice.realCharacter first) (fan.lattice.realCharacter second) cone.val := by
  let toric := fan.isToricCone cone.property
  have generators_agree : Set.EqOn (fan.lattice.realCharacter first)
      (fan.lattice.realCharacter second)
      (embedding '' Set.range (primitiveGenerator fan.lattice toric)) := by
    rintro vector ⟨generator, ⟨ray, rfl⟩, rfl⟩
    let actual : fan.Ray := ⟨primitiveGenerator fan.lattice toric ray,
      primitiveGenerator_isPrimitive fan.lattice toric ray, by
        have singleton := ray.eq_hull_singleton (toric.salient.anti ray.1.isFaceOf.le)
          (primitiveGenerator_mem fan.lattice toric ray)
          (by simpa only [map_zero] using
            (fan.lattice.injective.ne (primitiveGenerator_ne_zero fan.lattice toric ray)))
        rw [← singleton]
        exact fan.mem_of_isFaceOf cone.property ray.1.isFaceOf⟩
    have in_cone : embedding actual.val ∈ cone.val :=
      ray.1.isFaceOf.le (primitiveGenerator_mem fan.lattice toric ray)
    change fan.lattice.realCharacter first (embedding actual.val) =
      fan.lattice.realCharacter second (embedding actual.val)
    rw [fan.lattice.realCharacter_apply, fan.lattice.realCharacter_apply, agree actual in_cone]
  intro point contains
  have hull_member : point ∈ PointedCone.hull ℝ
      (embedding '' Set.range (primitiveGenerator fan.lattice toric)) := by
    rwa [toric.hull_primitiveGenerator fan.lattice]
  exact LinearMap.eqOn_span generators_agree (PointedCone.hull_le_span ℝ _ hull_member)

theorem rationalCharacterUnit_class_eq_of_eqOn_cone (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (first second : Lattice →+ ℤ)
    (agree : Set.EqOn (fan.lattice.realCharacter first)
      (fan.lattice.realCharacter second) cone.val) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    letI := fan.chartOpen_nonempty 𝕜 regular cone
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
        (fan.affineToricChartι 𝕜 regular cone).opensRange
        (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular nonempty first)) =
      TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass (fan.algebraicRealization 𝕜 regular)
        (fan.affineToricChartι 𝕜 regular cone).opensRange
        (Additive.ofMul (fan.rationalCharacterUnit 𝕜 regular nonempty second)) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  let := fan.chartOpen_nonempty 𝕜 regular cone
  have positive : first - second ∈ dualSemigroup fan.lattice cone.val := by
    rw [mem_dualSemigroup]
    intro point contains
    simp only [map_sub, LinearMap.sub_apply, agree contains, sub_self, le_refl]
  have negative : -(first - second) ∈ dualSemigroup fan.lattice cone.val := by
    rw [mem_dualSemigroup]
    intro point contains
    simp only [map_neg, map_sub, LinearMap.neg_apply, LinearMap.sub_apply,
      agree contains, sub_self, neg_zero, le_refl]
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
    (fan.algebraicRealization 𝕜 regular) _ _ _).mpr
  refine ⟨Units.map (fan.chartCoordinateSectionsEquiv 𝕜 regular cone).toMonoidHom
    (toricMonomialUnit 𝕜 fan.lattice cone.val (first - second) positive negative), ?_⟩
  rw [fan.chartCoordinateGerm_regularUnit 𝕜 regular nonempty cone,
    fan.chartCoordinateGerm_monomialUnit 𝕜 regular nonempty cone]
  exact fan.rationalCharacterUnit_sub_mul 𝕜 regular nonempty first second

namespace CharacterEquationAtlas

variable {fan : Fan embedding} {regular : fan.IsRegular}

def PresentsDivisor (atlas : CharacterEquationAtlas 𝕜 fan regular)
    (divisor : fan.InvariantRayDivisor) : Prop :=
  ∀ index (ray : fan.Ray), embedding ray.val ∈ (atlas.cone index).val →
    atlas.character index ray.val = -divisor ray

theorem cartierDivisor_eq_of_presentsDivisor
    (first second : CharacterEquationAtlas 𝕜 fan regular) (nonempty : Nonempty fan.cones)
    (divisor : fan.InvariantRayDivisor)
    (first_presents : first.PresentsDivisor 𝕜 divisor)
    (second_presents : second.PresentsDivisor 𝕜 divisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
    ((first.neg 𝕜).cartierEquationAtlas 𝕜 nonempty).cartierDivisor =
      ((second.neg 𝕜).cartierEquationAtlas 𝕜 nonempty).cartierDivisor := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular nonempty
  apply BondalThomsen.CartierEquationAtlas.cartierDivisor_eq_of_overlap_units
  intro firstIndex secondIndex
  change first.Index at firstIndex
  change second.Index at secondIndex
  let := fan.chartOpen_nonempty 𝕜 regular (first.cone firstIndex)
  let := fan.chartOpen_nonempty 𝕜 regular (second.cone secondIndex)
  let := BondalThomsen.nonempty_integral_open_intersection
    (fan.affineToricChartι 𝕜 regular (first.cone firstIndex)).opensRange
    (fan.affineToricChartι 𝕜 regular (second.cone secondIndex)).opensRange
  change ∃ unit : Γ(fan.algebraicRealization 𝕜 regular,
      (fan.affineToricChartι 𝕜 regular (first.cone firstIndex)).opensRange ⊓
        (fan.affineToricChartι 𝕜 regular (second.cone secondIndex)).opensRange)ˣ,
    TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField
        (fan.algebraicRealization 𝕜 regular) _ unit *
        fan.rationalCharacterUnit 𝕜 regular nonempty (-second.character secondIndex) =
      fan.rationalCharacterUnit 𝕜 regular nonempty (-first.character firstIndex)
  let := fan.chartOpen_nonempty 𝕜 regular (first.cone firstIndex ⊓ second.cone secondIndex)
  have agree := fan.realCharacter_eqOn_cone_of_ray_eq
    (first.cone firstIndex ⊓ second.cone secondIndex)
    (-first.character firstIndex) (-second.character secondIndex) (by
      intro ray contains
      change -(first.character firstIndex ray.val) = -(second.character secondIndex ray.val)
      exact congrArg Neg.neg ((first_presents firstIndex ray contains.1).trans
        (second_presents secondIndex ray contains.2).symm))
  have equal_classes := fan.rationalCharacterUnit_class_eq_of_eqOn_cone 𝕜
    regular nonempty (first.cone firstIndex ⊓ second.cone secondIndex)
    (-first.character firstIndex) (-second.character secondIndex) agree
  obtain ⟨unit, equation⟩ :=
    (TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
      (fan.algebraicRealization 𝕜 regular) _ _ _).mp equal_classes
  refine ⟨Units.map ((fan.algebraicRealization 𝕜 regular).presheaf.map
    (eqToHom (fan.chart_opensRange_intersection 𝕜 regular
      (first.cone firstIndex) (second.cone secondIndex)).symm).op).hom.toMonoidHom unit, ?_⟩
  rw [BondalThomsen.regularUnitGerm_eqToHom
    (fan.chart_opensRange_intersection 𝕜 regular (first.cone firstIndex) (second.cone secondIndex))]
  exact equation

end CharacterEquationAtlas

variable [FiniteDimensional ℝ Ambient]

theorem invariantDivisorCharacterAtlas_presentsDivisor (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) :
    (fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).PresentsDivisor 𝕜 divisor := by
  intro index ray contains
  change Fin (Nat.card fan.cones) at index
  change fan.coneDivisorCharacter
      (fan.divisorChartBasis complete regular ((Finite.equivFin fan.cones).symm index)).val.2
      (fan.divisorChartBasis complete regular
        ((Finite.equivFin fan.cones).symm index)).property.1 divisor ray.val = -divisor ray
  exact fan.coneDivisorCharacter_ray _ _ divisor ray contains

namespace CharacterEquationAtlas

variable {fan : Fan embedding} {regular : fan.IsRegular}

theorem cartierDivisor_eq_invariantDivisorCartier
    (atlas : CharacterEquationAtlas 𝕜 fan regular) (complete : fan.IsComplete)
    (divisor : fan.InvariantRayDivisor) (presents : atlas.PresentsDivisor 𝕜 divisor) :
    letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
    ((atlas.neg 𝕜).cartierEquationAtlas 𝕜 (fan.completeFan_nonemptyCones complete)).cartierDivisor =
      fan.invariantDivisorCartier 𝕜 complete regular divisor := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact atlas.cartierDivisor_eq_of_presentsDivisor 𝕜
    (fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor)
    (fan.completeFan_nonemptyCones complete) divisor presents
    (fan.invariantDivisorCharacterAtlas_presentsDivisor 𝕜 complete regular divisor)

theorem invertibleSheaf_eq_invariantDivisorLineBundle
    (atlas : CharacterEquationAtlas 𝕜 fan regular) (complete : fan.IsComplete)
    (divisor : fan.InvariantRayDivisor) (presents : atlas.PresentsDivisor 𝕜 divisor) :
    (atlas.neg 𝕜).invertibleSheaf 𝕜 (fan.completeFan_nonemptyCones complete) =
      fan.invariantDivisorLineBundle 𝕜 complete regular divisor := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  exact congrArg TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.toInvertibleSheaf
    (atlas.cartierDivisor_eq_invariantDivisorCartier 𝕜 complete divisor presents)

noncomputable def invariantDivisorLineBundleIso
    (atlas : CharacterEquationAtlas 𝕜 fan regular) (complete : fan.IsComplete)
    (divisor : fan.InvariantRayDivisor) (presents : atlas.PresentsDivisor 𝕜 divisor) :
    ((atlas.neg 𝕜).invertibleSheaf 𝕜 (fan.completeFan_nonemptyCones complete)).obj ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj :=
  eqToIso (congrArg (fun bundle => bundle.obj)
    (atlas.invertibleSheaf_eq_invariantDivisorLineBundle 𝕜 complete divisor presents))

end CharacterEquationAtlas

end TauCeti.Toric.Fan
