module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.Exact

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace BondalThomsen.Ports.LeanPool

universe u

noncomputable section

variable {scheme : Scheme.{u}} {sequence : ShortComplex scheme.Modules}

def schemeSectionsConnecting (exact_sequence : sequence.ShortExact) :
    sequence.X₃.presheaf.obj (op ⊤) ⟶ AddCommGrpCat.of (Cohomology sequence.X₁ 1) :=
  AddCommGrpCat.ofHom (cohomologyZeroEquiv sequence.X₃).symm.toAddMonoidHom ≫
    AddCommGrpCat.ofHom (cohomologyδ exact_sequence 0 1 rfl)

theorem schemeSectionsConnecting_zero (exact_sequence : sequence.ShortExact) :
    sequence.g.app ⊤ ≫ schemeSectionsConnecting exact_sequence = 0 := by
  ext section_value
  change cohomologyδ exact_sequence 0 1 rfl
    ((cohomologyZeroEquiv sequence.X₃).symm (sequence.g.app ⊤ section_value)) = 0
  have naturality :
      (cohomologyZeroEquiv sequence.X₃).symm (sequence.g.app ⊤ section_value) =
        cohomologyMap sequence.g 0 ((cohomologyZeroEquiv sequence.X₂).symm section_value) := by
    apply (cohomologyZeroEquiv sequence.X₃).injective
    simp only [AddEquiv.apply_symm_apply, cohomologyZeroEquiv_cohomologyMap]
  rw [naturality]
  exact (exact_cohomologyMap_cohomologyδ exact_sequence 0 1 rfl).apply_apply_eq_zero _

theorem schemeSectionsConnecting_exact (exact_sequence : sequence.ShortExact) :
    (ShortComplex.mk (sequence.g.app ⊤) (schemeSectionsConnecting exact_sequence)
      (schemeSectionsConnecting_zero exact_sequence)).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro section_value vanishes
  change cohomologyδ exact_sequence 0 1 rfl
    ((cohomologyZeroEquiv sequence.X₃).symm section_value) = 0 at vanishes
  obtain ⟨previous, previous_image⟩ :=
    (exact_cohomologyMap_cohomologyδ exact_sequence 0 1 rfl _).mp vanishes
  refine ⟨cohomologyZeroEquiv sequence.X₂ previous, ?_⟩
  rw [← cohomologyZeroEquiv_cohomologyMap, previous_image, AddEquiv.apply_symm_apply]

theorem schemeSectionsConnecting_epi (exact_sequence : sequence.ShortExact)
    (middle_zero : Subsingleton (Cohomology sequence.X₂ 1)) :
    Epi (schemeSectionsConnecting exact_sequence) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro extension
  obtain ⟨previous, previous_image⟩ :=
    (exact_cohomologyδ_cohomologyMap exact_sequence 0 1 rfl extension).mp
      (middle_zero.elim _ _)
  refine ⟨cohomologyZeroEquiv sequence.X₃ previous, ?_⟩
  change cohomologyδ exact_sequence 0 1 rfl
    ((cohomologyZeroEquiv sequence.X₃).symm (cohomologyZeroEquiv sequence.X₃ previous)) = extension
  simpa only [AddEquiv.symm_apply_apply] using previous_image

def schemeCohomologyOneCokernelIso (exact_sequence : sequence.ShortExact)
    (middle_zero : Subsingleton (Cohomology sequence.X₂ 1)) :
    cokernel (sequence.g.app ⊤) ≅ AddCommGrpCat.of (Cohomology sequence.X₁ 1) := by
  letI := schemeSectionsConnecting_epi exact_sequence middle_zero
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (sequence.g.app ⊤))
    (schemeSectionsConnecting_exact exact_sequence).gIsCokernel

end

end BondalThomsen.Ports.LeanPool
