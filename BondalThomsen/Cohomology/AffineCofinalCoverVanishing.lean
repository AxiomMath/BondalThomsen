module

public import BondalThomsen.Cohomology.AffineCechDerivedComparison
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.EpiMono

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace BondalThomsen.AffineCofinalCoverVanishing

universe spaceUniverse

noncomputable section

section LocalZero

variable {space : Type spaceUniverse} [TopologicalSpace space]

local instance : EnoughInjectives
    (Sheaf (Opens.grothendieckTopology space) AddCommGrpCat.{spaceUniverse}) :=
  (Sheaf.instIsGrothendieckAbelian
    (Opens.grothendieckTopology space) AddCommGrpCat.{spaceUniverse}).enoughInjectives

theorem abelianCohomology_locally_zero (degree : ℕ) :
    ∀ (coefficient : Sheaf (Opens.grothendieckTopology space)
      AddCommGrpCat.{spaceUniverse}) (open_set : Opens space)
      (element : coefficient.H' (degree + 1) open_set) (point : space),
      point ∈ open_set →
      ∃ (neighborhood : Opens space) (inclusion : neighborhood ≤ open_set),
        point ∈ neighborhood ∧
          (coefficient.cohomologyPresheaf (degree + 1)).map
            (homOfLE inclusion).op element = 0 := by
  induction degree with
  | zero =>
    intro coefficient open_set element point membership
    let sequence := ShortComplex.cokernelSequence (Injective.ι coefficient)
    have exact_sequence : sequence.ShortExact :=
      ⟨ShortComplex.cokernelSequence_exact (Injective.ι coefficient)⟩
    obtain ⟨previous, previous_boundary⟩ := Abelian.Ext.covariant_sequence_exact₁
      ((TauCeti.CategoryTheory.freeYonedaSheafFunctor
        (Opens.grothendieckTopology space)).obj open_set)
      exact_sequence element (Abelian.Ext.eq_zero_of_injective _) rfl
    obtain ⟨section_map, rfl⟩ := Abelian.Ext.addEquiv₀.symm.surjective previous
    let section_value := TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv
      (Opens.grothendieckTopology space) open_set sequence.X₃ section_map
    have locally_surjective : Sheaf.IsLocallySurjective sequence.g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat sequence.g).mpr inferInstance
    letI := locally_surjective
    obtain ⟨neighborhood, restriction, preimage_exists, neighborhood_membership⟩ :=
      (Opens.mem_grothendieckTopology space).mp
        (locally_surjective.1 section_value) point membership
    obtain ⟨preimage, preimage_equation⟩ := preimage_exists
    let lift_map := (TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv
      (Opens.grothendieckTopology space) neighborhood sequence.X₂).symm preimage
    have lift_equation : lift_map ≫ sequence.g =
        (TauCeti.CategoryTheory.freeYonedaSheafFunctor
          (Opens.grothendieckTopology space)).map restriction ≫ section_map := by
      apply (TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv
        (Opens.grothendieckTopology space) neighborhood sequence.X₃).injective
      rw [TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv_naturality_right,
        TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv_naturality_left]
      simpa only [lift_map, AddEquiv.apply_symm_apply] using preimage_equation
    refine ⟨neighborhood, restriction.le, neighborhood_membership, ?_⟩
    rw [← previous_boundary]
    change (Abelian.Ext.mk₀
      ((TauCeti.CategoryTheory.freeYonedaSheafFunctor
        (Opens.grothendieckTopology space)).map restriction)).comp
      ((Abelian.Ext.mk₀ section_map).comp exact_sequence.extClass rfl) (zero_add 1) = 0
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      ← lift_equation, ← Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.comp_assoc_of_second_deg_zero,
      ShortComplex.ShortExact.comp_extClass, Abelian.Ext.comp_zero]
  | succ degree induction_hypothesis =>
    intro coefficient open_set element point membership
    let sequence := ShortComplex.cokernelSequence (Injective.ι coefficient)
    have exact_sequence : sequence.ShortExact :=
      ⟨ShortComplex.cokernelSequence_exact (Injective.ι coefficient)⟩
    obtain ⟨previous, previous_boundary⟩ := Abelian.Ext.covariant_sequence_exact₁
      ((TauCeti.CategoryTheory.freeYonedaSheafFunctor
        (Opens.grothendieckTopology space)).obj open_set)
      exact_sequence element (Abelian.Ext.eq_zero_of_injective _) rfl
    obtain ⟨neighborhood, inclusion, neighborhood_membership, restriction_zero⟩ :=
      induction_hypothesis sequence.X₃ open_set previous point membership
    refine ⟨neighborhood, inclusion, neighborhood_membership, ?_⟩
    rw [← previous_boundary]
    change (Abelian.Ext.mk₀
      ((TauCeti.CategoryTheory.freeYonedaSheafFunctor
        (Opens.grothendieckTopology space)).map (homOfLE inclusion))).comp
      (previous.comp exact_sequence.extClass rfl) (zero_add _) = 0
    change (Abelian.Ext.mk₀
      ((TauCeti.CategoryTheory.freeYonedaSheafFunctor
        (Opens.grothendieckTopology space)).map (homOfLE inclusion))).comp
      previous (zero_add _) = 0 at restriction_zero
    rw [← Abelian.Ext.comp_assoc _ _ _ (zero_add _) rfl (by omega),
      restriction_zero, Abelian.Ext.zero_comp]

end LocalZero

section PrincipalCofinality

variable {ring : Type spaceUniverse} [CommRing ring]

theorem exists_finite_principal_cover
    (open_set : Opens (PrimeSpectrum ring))
    (compact : IsCompact (open_set : Set (PrimeSpectrum ring)))
    (property : ring → Prop)
    (local_property : ∀ point ∈ open_set, ∃ generator : ring,
      point ∈ PrimeSpectrum.basicOpen generator ∧
        PrimeSpectrum.basicOpen generator ≤ open_set ∧ property generator) :
    ∃ generators : Finset ring,
      (∀ generator ∈ generators,
        PrimeSpectrum.basicOpen generator ≤ open_set ∧ property generator) ∧
      (⨆ generator ∈ generators, PrimeSpectrum.basicOpen generator) = open_set := by
  classical
  let eligible := {generator : ring //
    PrimeSpectrum.basicOpen generator ≤ open_set ∧ property generator}
  obtain ⟨finite_cover, covers⟩ := compact.elim_finite_subcover
    (fun generator : eligible =>
      (PrimeSpectrum.basicOpen generator.val : Set (PrimeSpectrum ring)))
    (fun generator => (PrimeSpectrum.basicOpen generator.val).isOpen) (by
      intro point membership
      obtain ⟨generator, generator_membership, inclusion, satisfies⟩ :=
        local_property point membership
      exact Set.mem_iUnion.mpr ⟨⟨generator, inclusion, satisfies⟩,
        generator_membership⟩)
  refine ⟨finite_cover.image Subtype.val, ?_, le_antisymm ?_ ?_⟩
  · intro generator membership
    obtain ⟨eligible_generator, _, rfl⟩ := Finset.mem_image.mp membership
    exact eligible_generator.property
  · refine iSup_le fun generator => iSup_le fun membership => ?_
    obtain ⟨eligible_generator, _, rfl⟩ := Finset.mem_image.mp membership
    exact eligible_generator.property.1
  · intro point membership
    obtain ⟨generator, generator_membership⟩ :=
      Set.mem_iUnion.mp (covers membership)
    obtain ⟨finite_membership, principal_membership⟩ :=
      Set.mem_iUnion.mp generator_membership
    exact Opens.mem_iSup.mpr ⟨generator.val, Opens.mem_iSup.mpr
      ⟨Finset.mem_image.mpr ⟨generator, finite_membership, rfl⟩,
        principal_membership⟩⟩

theorem abelianCohomology_finite_principal_local_zero
    (coefficient : Sheaf (Opens.grothendieckTopology (PrimeSpectrum ring))
      AddCommGrpCat.{spaceUniverse})
    (degree : ℕ) (positive : 0 < degree)
    (open_set : Opens (PrimeSpectrum ring))
    (compact : IsCompact (open_set : Set (PrimeSpectrum ring)))
    (element : coefficient.H' degree open_set) :
    ∃ generators : Finset ring,
      (⨆ generator ∈ generators, PrimeSpectrum.basicOpen generator) = open_set ∧
      ∀ generator ∈ generators,
        ∃ inclusion : PrimeSpectrum.basicOpen generator ≤ open_set,
          (coefficient.cohomologyPresheaf degree).map
            (homOfLE inclusion).op element = 0 := by
  obtain ⟨previous_degree, rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  apply (exists_finite_principal_cover open_set compact
    (fun generator => ∃ inclusion : PrimeSpectrum.basicOpen generator ≤ open_set,
      (coefficient.cohomologyPresheaf (previous_degree + 1)).map
        (homOfLE inclusion).op element = 0) ?_).imp
  · intro generators result
    exact ⟨result.2, fun generator membership => (result.1 generator membership).2⟩
  · intro point membership
    obtain ⟨neighborhood, inclusion, neighborhood_membership, locally_zero⟩ :=
      abelianCohomology_locally_zero previous_degree coefficient
        open_set element point membership
    obtain ⟨principal, ⟨generator, rfl⟩, principal_membership, principal_inclusion⟩ :=
      (Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens)
        neighborhood_membership
    refine ⟨generator, principal_membership, principal_inclusion.trans inclusion,
      principal_inclusion.trans inclusion, ?_⟩
    rw [← homOfLE_comp principal_inclusion inclusion, op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply, locally_zero, map_zero]

end PrincipalCofinality

end

end BondalThomsen.AffineCofinalCoverVanishing
