module

public import BondalThomsen.Ports.Matroid.Simplification

@[expose] public section

namespace BondalThomsen

open Submodule Set

variable {Label Field Vector : Type*} [_root_.Field Field]
    [AddCommGroup Vector] [Module Field Vector]

theorem exists_unit_smul_of_span_eq (first second : Vector) (nonzero : second ≠ 0)
    (same_span : span Field {first} = span Field {second}) :
    ∃ scalar : Fieldˣ, (scalar : Field) • first = second := by
  have member : second ∈ span Field {first} := by
    rw [same_span]
    exact subset_span (Set.mem_singleton _)
  obtain ⟨scalar, equality⟩ := mem_span_singleton.mp member
  have scalar_nonzero : scalar ≠ 0 := by
    intro zero
    apply nonzero
    rw [← equality, zero, zero_smul]
  exact ⟨Units.mk0 scalar scalar_nonzero, equality⟩

theorem linearIndepOn_iff_of_span_eq (first second : Label → Vector) (selected : Set Label)
    (nonzero : ∀ label ∈ selected, second label ≠ 0)
    (same_span : ∀ label ∈ selected, span Field {first label} = span Field {second label}) :
    LinearIndepOn Field first selected ↔ LinearIndepOn Field second selected := by
  classical
  let scalars := fun label : selected =>
    (exists_unit_smul_of_span_eq (first label.val) (second label.val)
      (nonzero label.val label.property) (same_span label.val label.property)).choose
  have compatible : (scalars • (fun label : selected => first label.val)) =
      (fun label : selected => second label.val) := by
    funext label
    exact (exists_unit_smul_of_span_eq (first label.val) (second label.val)
      (nonzero label.val label.property) (same_span label.val label.property)).choose_spec
  change LinearIndependent Field (fun label : selected => first label.val) ↔
    LinearIndependent Field (fun label : selected => second label.val)
  rw [← compatible]
  exact (LinearIndependent.units_smul_iff _ scalars).symm

end BondalThomsen
