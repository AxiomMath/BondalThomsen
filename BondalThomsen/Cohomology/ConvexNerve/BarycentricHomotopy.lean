module

public import BondalThomsen.Cohomology.ConvexNerve.ClosedComparison
public import BondalThomsen.Ports.TauCeti.AlgebraicTopology.SimplicialComplex.Realization
public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Order.Preorder.Chain

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open BondalThomsen.ClosedConvexNerveComparison
open scoped Classical

namespace BondalThomsen.ConvexNerveBarycentricHomotopy

variable {Index : Type} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def nerveBarycentricComplex (patches : Index → Set E) :
    AbstractSimplicialComplex (NerveFace patches) where
  faces := {vertices | vertices.Nonempty ∧ IsChain (· ≤ ·) (vertices : Set (NerveFace patches))}
  isRelLowerSet_faces := by
    rintro vertices ⟨nonempty, chain⟩
    refine ⟨nonempty, ?_⟩
    intro smaller contained smaller_nonempty
    exact ⟨smaller_nonempty, chain.mono contained⟩
  singleton_mem := by
    intro face
    exact ⟨Finset.singleton_nonempty face, by simp⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mem_nerveBarycentricComplex_iff (patches : Index → Set E)
    (vertices : Finset (NerveFace patches)) :
    vertices ∈ nerveBarycentricComplex patches ↔
      vertices.Nonempty ∧ IsChain (· ≤ ·) (vertices : Set (NerveFace patches)) :=
  Iff.rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem barycentricFace_has_minimum (patches : Index → Set E)
    (vertices : Finset (NerveFace patches)) (member : vertices ∈ nerveBarycentricComplex patches) :
    ∃ least ∈ vertices, ∀ larger ∈ vertices, least.val ⊆ larger.val := by
  obtain ⟨nonempty, chain⟩ := (mem_nerveBarycentricComplex_iff patches vertices).mp member
  obtain ⟨least, present, minimal⟩ := vertices.exists_min_image (fun face => face.val.card) nonempty
  refine ⟨least, present, ?_⟩
  intro larger larger_present
  rcases chain.total present larger_present with contained | reverse
  · exact contained
  · have same : larger.val = least.val :=
      Finset.eq_of_subset_of_card_le reverse (minimal larger larger_present)
    rw [same]

noncomputable def witnessEvaluation (patches : Index → Set E)
    (point : AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) : E :=
  point.val.sum (fun face weight => weight • intersectionWitness patches face)

theorem witnessEvaluation_mem_core (patches : Index → Set E)
    (point : AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches)) :
    witnessEvaluation patches point ∈ compactCore patches := by
  let simplex : AbstractSimplicialComplex.StandardSimplex point.val.support :=
    ⟨point.val, AbstractSimplicialComplex.mem_convexHull_carrier _ point⟩
  apply (compactCore_convex patches).sum_mem
    (fun face _ => AbstractSimplicialComplex.StandardSimplex.nonneg simplex face)
    (AbstractSimplicialComplex.StandardSimplex.sum_eq_one simplex)
  intro face _
  exact intersectionWitness_mem_core patches face

theorem witnessEvaluation_face_formula (patches : Index → Set E)
    (face : TauCeti.SetLike.Face (nerveBarycentricComplex patches))
    (point : AbstractSimplicialComplex.StandardSimplex face.val) :
    witnessEvaluation patches (AbstractSimplicialComplex.faceInclusion _ face point) =
      ∑ vertex ∈ face.val, point.val vertex • intersectionWitness patches vertex := by
  unfold witnessEvaluation
  rw [AbstractSimplicialComplex.faceInclusion_val]
  exact point.val.sum_of_support_subset
    (AbstractSimplicialComplex.StandardSimplex.support_subset point)
    _ (fun _ _ => zero_smul ℝ _)

theorem witnessEvaluation_continuous (patches : Index → Set E) :
    Continuous (witnessEvaluation patches) := by
  apply AbstractSimplicialComplex.continuous_iff_faceInclusion.mpr
  intro face
  have continuous_sum : Continuous (fun point : AbstractSimplicialComplex.StandardSimplex face.val =>
      ∑ vertex ∈ face.val, point.val vertex • intersectionWitness patches vertex) := by
    apply continuous_finsetSum
    intro vertex _
    have coordinate : Continuous (fun point : AbstractSimplicialComplex.StandardSimplex face.val =>
        point.val vertex) :=
      (continuous_apply vertex).comp (continuous_induced_dom :
        Continuous (fun point : AbstractSimplicialComplex.StandardSimplex face.val =>
          (point.val : NerveFace patches → ℝ)))
    exact coordinate.smul continuous_const
  exact continuous_sum.congr fun point => (witnessEvaluation_face_formula patches face point).symm

noncomputable def barycentricWitnessMap (patches : Index → Set E) :
    C(AbstractSimplicialComplex.Realization (nerveBarycentricComplex patches), compactCore patches) where
  toFun point := ⟨witnessEvaluation patches point, witnessEvaluation_mem_core patches point⟩
  continuous_toFun := (witnessEvaluation_continuous patches).subtype_mk _

theorem witnessEvaluation_face_mem_carrier (patches : Index → Set E)
    (face : TauCeti.SetLike.Face (nerveBarycentricComplex patches))
    (least : NerveFace patches) (contained : ∀ vertex ∈ face.val, least.val ⊆ vertex.val)
    (point : AbstractSimplicialComplex.StandardSimplex face.val) :
    witnessEvaluation patches (AbstractSimplicialComplex.faceInclusion _ face point) ∈
      cofaceWitnessCarrier patches least := by
  rw [witnessEvaluation_face_formula]
  have sum_one : ∑ vertex ∈ face.val, point.val vertex = 1 := by
    rw [← point.val.sum_of_support_subset
      (AbstractSimplicialComplex.StandardSimplex.support_subset point) (fun _ weight => weight)
      (fun _ _ => rfl)]
    exact AbstractSimplicialComplex.StandardSimplex.sum_eq_one point
  exact barycentricWitness_mem_carrier patches least face.val id (fun vertex => point.val vertex)
    contained (fun vertex _ => AbstractSimplicialComplex.StandardSimplex.nonneg point vertex) sum_one

end BondalThomsen.ConvexNerveBarycentricHomotopy
