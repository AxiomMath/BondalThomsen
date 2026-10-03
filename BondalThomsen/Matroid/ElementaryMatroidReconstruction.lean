module

public import BondalThomsen.Ports.Matroid.LoopExtension
public import BondalThomsen.DeepFan.ElementaryClassification

@[expose] public section

namespace Matroid

open Set BondalThomsen

variable {Ground : Type*}

inductive ElementaryExtensionInstruction (Ground : Type*)
  | loop (added : Ground)
  | coloop (added : Ground)
  | parallel (existing added : Ground)
  | series (existing added : Ground)

namespace ElementaryExtensionInstruction

def added : ElementaryExtensionInstruction Ground → Ground
  | .loop label => label
  | .coloop label => label
  | .parallel _ label => label
  | .series _ label => label

def apply [DecidableEq Ground] (instruction : ElementaryExtensionInstruction Ground)
    (source : Matroid Ground) : Matroid Ground :=
  match instruction with
  | .loop label => source.addLoop label
  | .coloop label => source.addColoop label
  | .parallel existing label => source.parallelExtend existing label
  | .series existing label => source.seriesExtend existing label

def Valid (instruction : ElementaryExtensionInstruction Ground)
    (source : Matroid Ground) : Prop :=
  instruction.added ∉ source.E ∧
    match instruction with
    | .loop _ => True
    | .coloop _ => True
    | .parallel existing _ => source.IsNonloop existing
    | .series existing _ => source✶.IsNonloop existing

theorem ground [DecidableEq Ground]
    (instruction : ElementaryExtensionInstruction Ground) (source : Matroid Ground) :
    (instruction.apply source).E = insert instruction.added source.E := by
  cases instruction <;> simp [apply, added]

theorem ground_ncard [DecidableEq Ground]
    (instruction : ElementaryExtensionInstruction Ground) (source : Matroid Ground)
    [source.Finite] (valid : instruction.Valid source) :
    (instruction.apply source).E.ncard = source.E.ncard + 1 := by
  rw [ground, Set.ncard_insert_of_notMem valid.1 source.ground_finite]

end ElementaryExtensionInstruction

def runElementaryExtensions [DecidableEq Ground] :
    List (ElementaryExtensionInstruction Ground) → Matroid Ground → Matroid Ground
  | [], initial => initial
  | instruction :: previous, initial =>
    instruction.apply (runElementaryExtensions previous initial)

def ValidElementaryExtensions [DecidableEq Ground] :
    List (ElementaryExtensionInstruction Ground) → Matroid Ground → Prop
  | [], _ => True
  | instruction :: previous, initial =>
    ValidElementaryExtensions previous initial ∧
      instruction.Valid (runElementaryExtensions previous initial)

namespace ElementaryExtensionInstruction

theorem reduction [DecidableEq Ground]
    (instruction : ElementaryExtensionInstruction Ground) (source : Matroid Ground)
    (valid : instruction.Valid source) :
    ElementarySeriesParallelReduction (instruction.apply source) source := by
  cases instruction with
  | loop label =>
    have actual := ElementarySeriesParallelReduction.loop label (addLoop_isLoop valid.1)
    simpa only [apply, addLoop_delete_eq (added := label) source valid.1] using actual
  | coloop label =>
    have actual := ElementarySeriesParallelReduction.coloop label (addColoop_isColoop valid.1)
    simpa only [apply, addColoop_delete_eq (added := label) source valid.1] using actual
  | parallel existing label =>
    have distinct : label ≠ existing := fun equality =>
      valid.1 (equality.symm ▸ valid.2.mem_ground)
    have actual := ElementarySeriesParallelReduction.parallel label existing distinct
      (parallelExtend_parallel valid.2 label).symm
    simpa only [apply, parallelExtend_delete_eq (added := label) source existing valid.1] using actual
  | series existing label =>
    have distinct : label ≠ existing := fun equality =>
      valid.1 (equality.symm ▸ valid.2.mem_ground)
    have actual := ElementarySeriesParallelReduction.series label existing distinct
      (seriesExtend_dual_parallel valid.2 label).symm
    simpa only [apply, seriesExtend_contract_eq (added := label) source existing valid.1] using actual

end ElementaryExtensionInstruction

theorem runElementaryExtensions_finite [DecidableEq Ground]
    (program : List (ElementaryExtensionInstruction Ground)) (initial : Matroid Ground)
    [initial.Finite] : (runElementaryExtensions program initial).Finite := by
  induction program with
  | nil => change initial.Finite; infer_instance
  | cons instruction previous induction =>
    let := induction
    exact ⟨by
      change (instruction.apply (runElementaryExtensions previous initial)).E.Finite
      rw [instruction.ground]
      exact (runElementaryExtensions previous initial).ground_finite.insert _⟩

theorem ValidElementaryExtensions.ground_ncard [DecidableEq Ground]
    {program : List (ElementaryExtensionInstruction Ground)} {initial : Matroid Ground}
    [initial.Finite] (valid : ValidElementaryExtensions program initial) :
    (runElementaryExtensions program initial).E.ncard =
      initial.E.ncard + program.length := by
  induction program with
  | nil => simp [runElementaryExtensions]
  | cons instruction previous induction =>
    let := runElementaryExtensions_finite previous initial
    change (instruction.apply (runElementaryExtensions previous initial)).E.ncard = _
    rw [instruction.ground_ncard _ valid.2, induction valid.1, List.length_cons]
    omega

end Matroid

