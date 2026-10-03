module

public import BondalThomsen.Rarity.FanClassTransport
public import BondalThomsen.Rarity.DeepFanUnconditionalCounting

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module Set
open BondalThomsen.ToricTransport
open scoped Classical

namespace BondalThomsen

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem integralFanClass_eq_of_ternaryRayCode_eq
    (source target : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (sourceComplete : source.IsComplete) (sourceRegular : source.IsRegular)
    (sourceDeep : source.IsDeep dimension) (targetComplete : target.IsComplete)
    (targetRegular : target.IsRegular) (targetDeep : target.IsDeep dimension)
    (sourceBasis targetBasis : Basis (Fin dimension) ℤ Lattice)
    (sourceConeBasis : source.IsConeBasis sourceBasis)
    (targetConeBasis : target.IsConeBasis targetBasis)
    (codeEquality : source.ternaryRayCode sourceBasis = target.ternaryRayCode targetBasis) :
    integralFanClass source = integralFanClass target := by
  classical
  let lattice := sourceBasis.equivFun.trans targetBasis.equivFun.symm
  have coordinateEquality {sourceRay : source.Ray} {targetRay : target.Ray}
      (equal : TauCeti.Toric.Fan.ternaryCoordinates sourceBasis sourceRay.val =
        TauCeti.Toric.Fan.ternaryCoordinates targetBasis targetRay.val) :
      lattice sourceRay.val = targetRay.val := by
    apply targetBasis.equivFun.injective
    ext index
    have entry := congrArg (fun coordinate : Fin dimension → SignType =>
      (coordinate index : ℤ)) equal
    rw [source.ternaryCoordinates_cast sourceComplete sourceRegular sourceDeep
        sourceBasis sourceConeBasis,
      target.ternaryCoordinates_cast targetComplete targetRegular targetDeep
        targetBasis targetConeBasis] at entry
    simpa only [lattice, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      Basis.equivFun_apply] using entry
  have raySets : Set.range (fun ray : source.Ray => lattice ray.val) =
      Set.range (fun ray : target.Ray => ray.val) := by
    ext vector
    constructor
    · rintro ⟨sourceRay, rfl⟩
      have member : TauCeti.Toric.Fan.ternaryCoordinates sourceBasis sourceRay.val ∈
          target.ternaryRayCode targetBasis := by
        rw [← codeEquality]
        simp only [TauCeti.Toric.Fan.ternaryRayCode, Set.Finite.mem_toFinset]
        exact ⟨sourceRay, rfl⟩
      simp only [TauCeti.Toric.Fan.ternaryRayCode, Set.Finite.mem_toFinset] at member
      obtain ⟨targetRay, equal⟩ := member
      exact ⟨targetRay, (coordinateEquality equal.symm).symm⟩
    · rintro ⟨targetRay, rfl⟩
      have member : TauCeti.Toric.Fan.ternaryCoordinates targetBasis targetRay.val ∈
          source.ternaryRayCode sourceBasis := by
        rw [codeEquality]
        simp only [TauCeti.Toric.Fan.ternaryRayCode, Set.Finite.mem_toFinset]
        exact ⟨targetRay, rfl⟩
      simp only [TauCeti.Toric.Fan.ternaryRayCode, Set.Finite.mem_toFinset] at member
      obtain ⟨sourceRay, equal⟩ := member
      exact ⟨sourceRay, coordinateEquality equal⟩
  exact (integralFanClass_eq_iff source target).mpr
    (nonempty_integralRayFanEquiv_of_primitive_ray_sets source target sourceComplete sourceRegular
      sourceDeep targetComplete targetRegular targetDeep sourceBasis lattice raySets)

theorem deep_integralFanFamilyClasses_finite_and_card_le_ternary
    {Index : Type*} {dimension : ℕ} (fans : Index → TauCeti.Toric.Fan embedding)
    (complete : ∀ index, (fans index).IsComplete)
    (regular : ∀ index, (fans index).IsRegular)
    (deep : ∀ index, (fans index).IsDeep dimension)
    (bases : Index → Basis (Fin dimension) ℤ Lattice)
    (coneBases : ∀ index, (fans index).IsConeBasis (bases index)) :
    (Set.range (fun index => integralFanClass (fans index))).Finite ∧
      Nat.card ↥(Set.range (fun index => integralFanClass (fans index))) ≤
        2 ^ (3 ^ dimension) := by
  classical
  let classify := fun index => integralFanClass (fans index)
  let code := fun index => (fans index).ternaryRayCode (bases index)
  have constancy : ∀ first second, code first = code second → classify first = classify second := by
    intro first second equal
    exact integralFanClass_eq_of_ternaryRayCode_eq (fans first) (fans second)
      (complete first) (regular first) (deep first) (complete second) (regular second) (deep second)
      (bases first) (bases second) (coneBases first) (coneBases second) equal
  choose representative representativeEquality using
    (fun fanClass : Set.range classify => fanClass.property)
  let encode : Set.range classify → Finset (Fin dimension → SignType) :=
    fun fanClass => code (representative fanClass)
  have injective : Function.Injective encode := by
    intro first second equal
    apply Subtype.ext
    rw [← representativeEquality first, ← representativeEquality second]
    exact constancy _ _ equal
  let : Finite (Set.range classify) := Finite.of_injective encode injective
  refine ⟨Set.toFinite _, ?_⟩
  have bound := Nat.card_le_card_of_injective encode injective
  have signCard : Fintype.card SignType = 3 := by decide
  simpa only [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fun,
    Fintype.card_fin, signCard] using bound

theorem deep_integralFanFamilyClasses_finite_and_card_le_ternary_of_basis
    {Index : Type*} {dimension : ℕ} (fans : Index → TauCeti.Toric.Fan embedding)
    (complete : ∀ index, (fans index).IsComplete)
    (regular : ∀ index, (fans index).IsRegular)
    (deep : ∀ index, (fans index).IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) :
    (Set.range (fun index => integralFanClass (fans index))).Finite ∧
      Nat.card ↥(Set.range (fun index => integralFanClass (fans index))) ≤
        2 ^ (3 ^ dimension) := by
  classical
  have adapted : ∀ index, ∃ basis : Basis (Fin dimension) ℤ Lattice,
      (fans index).IsConeBasis basis := by
    intro index
    obtain ⟨size, basis, coneBasis, _⟩ :=
      (fans index).exists_coneBasis_containing (complete index) (regular index) (0 : Ambient)
    have sizeEquality : size = dimension := by
      have coneRank := finrank_eq_card_basis basis
      have referenceRank := finrank_eq_card_basis reference
      simp only [Fintype.card_fin] at coneRank referenceRank
      omega
    subst size
    exact ⟨basis, coneBasis⟩
  choose bases coneBases using adapted
  exact deep_integralFanFamilyClasses_finite_and_card_le_ternary
    fans complete regular deep bases coneBases

theorem card_le_two_pow_of_actual_deep_integralFan_tree_fiber
    {Classes : Type*} [Fintype Classes] {dimension : ℕ}
    (tree : BinaryTree TreeMark) (valid : ComponentTreeShape tree)
    (fans : Classes → TauCeti.Toric.Fan embedding)
    (complete : ∀ configuration, (fans configuration).IsComplete)
    (regular : ∀ configuration, (fans configuration).IsRegular)
    (deep : ∀ configuration, (fans configuration).IsDeep dimension)
    (bases : Classes → Basis (Fin dimension) ℤ Lattice)
    (coneBases : ∀ configuration, (fans configuration).IsConeBasis (bases configuration))
    (isomorphisms : ∀ configuration,
      Matroid.Iso (componentTreeMatroid tree valid) (fans configuration).rayMatroid)
    (classInjective : Function.Injective (fun configuration => integralFanClass (fans configuration))) :
    Fintype.card Classes ≤ 2 ^ tree.numLeaves := by
  classical
  by_cases empty : IsEmpty Classes
  · let := empty
    simp
  let referenceClass := Classical.choice (not_isEmpty_iff.mp empty)
  let labels := fun configuration => MatroidIso.univLabelEquiv (isomorphisms configuration)
    (componentTreeMatroid_ground tree valid) (rayMatroid_ground _)
  let representative := fun configuration =>
    (bases configuration).toMatrix (fun leaf => (labels configuration leaf).val)
  have tu : ∀ configuration, (representative configuration).IsTotallyUnimodular := by
    intro configuration
    exact ((fans configuration).deep_rayMatrix_totallyUnimodular (complete configuration)
      (regular configuration) (deep configuration) (bases configuration)
      (coneBases configuration)).submatrix id (labels configuration)
  have matching : ∀ configuration,
      rayMatroid (Field := ℚ) (fun leaf row => (representative referenceClass row leaf : ℚ)) =
        rayMatroid (Field := ℚ) (fun leaf row => (representative configuration row leaf : ℚ)) := by
    intro configuration
    exact ((fans referenceClass).labelledRayMatroid_eq_tree (bases referenceClass) tree valid
      (isomorphisms referenceClass)).trans
        ((fans configuration).labelledRayMatroid_eq_tree (bases configuration) tree valid
          (isomorphisms configuration)).symm
  have rank : ((representative referenceClass).map (Int.castRingHom ℚ)).rank =
      Fintype.card (Fin dimension) := by
    simpa only [Fintype.card_fin] using (fans referenceClass).labelledRayMatrix_rational_rank
      (bases referenceClass) (coneBases referenceClass) (labels referenceClass)
  have bound := card_le_two_pow_of_tu_matroid_model (representative referenceClass) representative
    (tu referenceClass) tu rank matching (by
      intro first second operation equality
      apply classInjective
      exact integralFanClass_eq_of_rayMatrix_row_equivalence (fans first) (fans second)
        (complete first) (regular first) (deep first) (complete second) (regular second) (deep second)
        (bases first) (bases second) (labels first) (labels second) operation equality)
  simpa only [treeLeaf_card] using bound

theorem deep_integralFanFamilyClasses_card_le_signedTreeCount_of_actual_tree_isos
    {Index : Type*} {dimension elements : ℕ} (fans : Index → TauCeti.Toric.Fan embedding)
    (complete : ∀ index, (fans index).IsComplete)
    (regular : ∀ index, (fans index).IsRegular)
    (deep : ∀ index, (fans index).IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice)
    (trees : Index → MarkedLeafTree elements)
    (valid : ∀ index, ComponentTreeShape (trees index).val)
    (isomorphisms : ∀ index,
      Matroid.Iso (componentTreeMatroid (trees index).val (valid index)) (fans index).rayMatroid) :
    (Set.range (fun index => integralFanClass (fans index))).Finite ∧
      Nat.card ↥(Set.range (fun index => integralFanClass (fans index))) ≤ signedTreeCount elements := by
  classical
  let classify := fun index => integralFanClass (fans index)
  have finiteClasses := deep_integralFanFamilyClasses_finite_and_card_le_ternary_of_basis
    fans complete regular deep reference
  let := finiteClasses.1.fintype
  have adapted : ∀ index, ∃ basis : Basis (Fin dimension) ℤ Lattice,
      (fans index).IsConeBasis basis := by
    intro index
    obtain ⟨size, basis, coneBasis, _⟩ :=
      (fans index).exists_coneBasis_containing (complete index) (regular index) (0 : Ambient)
    have sizeEquality : size = dimension := by
      have coneRank := finrank_eq_card_basis basis
      have referenceRank := finrank_eq_card_basis reference
      simp only [Fintype.card_fin] at coneRank referenceRank
      omega
    subst size
    exact ⟨basis, coneBasis⟩
  choose bases coneBases using adapted
  choose representative representativeEquality using
    (fun fanClass : Set.range classify => fanClass.property)
  let encode := fun fanClass : Set.range classify => trees (representative fanClass)
  let Fiber := fun tree : MarkedLeafTree elements =>
    {fanClass : Set.range classify // encode fanClass = tree}
  have fiberBound : ∀ tree, Fintype.card (Fiber tree) ≤ 2 ^ elements := by
    intro tree
    let fiberFans := fun fanClass : Fiber tree => fans (representative fanClass.val)
    by_cases empty : IsEmpty (Fiber tree)
    · let := empty
      simp
    have treeValid : ComponentTreeShape tree.val := by
      let selected := Classical.choice (not_isEmpty_iff.mp empty)
      have equality : (trees (representative selected.val)).val = tree.val :=
        congrArg Subtype.val selected.property
      exact equality ▸ valid (representative selected.val)
    have fiberIsos : ∀ fanClass : Fiber tree,
        Matroid.Iso (componentTreeMatroid tree.val treeValid) (fiberFans fanClass).rayMatroid := by
      intro fanClass
      have same := congrArg Subtype.val fanClass.property
      let treeIso := Classical.choice (componentTreeMatroid_iso_of_tree_eq same.symm treeValid
        (valid (representative fanClass.val)))
      exact treeIso.trans (isomorphisms (representative fanClass.val))
    have bound := card_le_two_pow_of_actual_deep_integralFan_tree_fiber tree.val treeValid fiberFans
      (fun fanClass => complete (representative fanClass.val))
      (fun fanClass => regular (representative fanClass.val))
      (fun fanClass => deep (representative fanClass.val))
      (fun fanClass => bases (representative fanClass.val))
      (fun fanClass => coneBases (representative fanClass.val)) fiberIsos (by
        intro first second equality
        apply Subtype.ext
        apply Subtype.ext
        simpa only [fiberFans, ← representativeEquality] using equality)
    simpa only [tree.property] using bound
  refine ⟨finiteClasses.1, ?_⟩
  rw [Nat.card_eq_fintype_card, ← Fintype.card_congr (Equiv.sigmaFiberEquiv encode),
    Fintype.card_sigma]
  calc
    ∑ tree, Fintype.card (Fiber tree) ≤ ∑ _tree : MarkedLeafTree elements, 2 ^ elements :=
      Finset.sum_le_sum fun tree _ => fiberBound tree
    _ = Fintype.card (MarkedLeafTree elements) * 2 ^ elements := by simp
    _ = Fintype.card (SignedMarkedTree elements) := by
      simpa only [Nat.mul_comm] using (signedMarkedTree_card_mul elements).symm
    _ ≤ signedTreeCount elements := signedMarkedTree_card_le elements

theorem deep_integralFanFamilyClasses_card_le_signedTree_sum_of_actual_tree_coverage
    {Index : Type*} {dimension : ℕ} (fans : Index → TauCeti.Toric.Fan embedding)
    (complete : ∀ index, (fans index).IsComplete)
    (regular : ∀ index, (fans index).IsRegular)
    (deep : ∀ index, (fans index).IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice)
    (coverage : ∀ index, ∃ tree : BinaryTree TreeMark, ∃ valid : ComponentTreeShape tree,
      Nonempty (Matroid.Iso (componentTreeMatroid tree valid) (fans index).rayMatroid) ∧
        tree.numLeaves ≤ 4 * dimension) :
    (Set.range (fun index => integralFanClass (fans index))).Finite ∧
      Nat.card ↥(Set.range (fun index => integralFanClass (fans index))) ≤ 48 ^ (4 * dimension) := by
  classical
  choose trees valid isomorphisms leafBounds using coverage
  let actualIso := fun index => Classical.choice (isomorphisms index)
  let classify := fun index => integralFanClass (fans index)
  let Slice := fun elements : Fin (4 * dimension + 1) =>
    {index : Index // (trees index).numLeaves = elements.val}
  let sliceClasses := fun elements : Fin (4 * dimension + 1) =>
    Set.range (fun index : Slice elements => classify index.val)
  have sliceBounds : ∀ elements, (sliceClasses elements).Finite ∧
      (sliceClasses elements).ncard ≤ signedTreeCount elements.val := by
    intro elements
    exact deep_integralFanFamilyClasses_card_le_signedTreeCount_of_actual_tree_isos
      (fun index : Slice elements => fans index.val)
      (fun index => complete index.val) (fun index => regular index.val)
      (fun index => deep index.val) reference
      (fun index => (⟨trees index.val, index.property⟩ : MarkedLeafTree elements.val))
      (fun index => valid index.val) (fun index => actualIso index.val)
  have classesUnion : Set.range classify = ⋃ elements, sliceClasses elements := by
    ext fanClass
    constructor
    · rintro ⟨index, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨(trees index).numLeaves, by have := leafBounds index; omega⟩,
        ⟨⟨index, rfl⟩, rfl⟩⟩
    · intro member
      obtain ⟨elements, index, equality⟩ := Set.mem_iUnion.mp member
      exact ⟨index.val, equality⟩
  refine ⟨classesUnion ▸ Set.finite_iUnion (fun elements => (sliceBounds elements).1), ?_⟩
  change (Set.range classify).ncard ≤ _
  rw [classesUnion]
  calc
    (⋃ elements, sliceClasses elements).ncard ≤ ∑ elements, (sliceClasses elements).ncard :=
      Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ elements : Fin (4 * dimension + 1), signedTreeCount elements.val :=
      Finset.sum_le_sum fun elements _ => (sliceBounds elements).2
    _ = ∑ elements ∈ Finset.range (4 * dimension + 1), signedTreeCount elements := by
      rw [Fin.sum_univ_eq_sum_range]
    _ ≤ 48 ^ (4 * dimension) := signedTreeCount_sum_le dimension

theorem deep_integralFanFamilyClasses_card_le_tree_bound
    {Index : Type*} {dimension : ℕ} (fans : Index → TauCeti.Toric.Fan embedding)
    (complete : ∀ index, (fans index).IsComplete)
    (regular : ∀ index, (fans index).IsRegular)
    (deep : ∀ index, (fans index).IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (positiveDimension : 0 < dimension) :
    (Set.range (fun index => integralFanClass (fans index))).Finite ∧
      Nat.card ↥(Set.range (fun index => integralFanClass (fans index))) ≤ 48 ^ (4 * dimension) := by
  apply deep_integralFanFamilyClasses_card_le_signedTree_sum_of_actual_tree_coverage
    fans complete regular deep reference
  intro index
  obtain ⟨tree, valid, isomorphism, _, bound⟩ := (fans index).deep_rayMatroid_single_tree
    (complete index) (regular index) (deep index) reference positiveDimension
  exact ⟨tree, valid, isomorphism, bound⟩

end BondalThomsen
