module

public import BondalThomsen.Cohomology.ConvexNerve.ReducedCochainAcyclicity
public import BondalThomsen.Ports.TauCeti.AlgebraicTopology.SimplicialComplex.IsCone
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical Simplicial

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveIncidenceHomologyComparison

section IncidenceChains

variable {Ray : Type*} {Chart : Type}

def incidenceSimplicialSet (incidence : Ray → Chart → Prop) (negative : Ray → Prop) : SSet.{0} where
  obj simplex := forbiddenTuple incidence negative simplex.unop.len
  map selection := ↾fun tuple => ⟨tuple.val ∘ selection.unop.toOrderHom,
    tupleForbidden_precomp incidence negative selection.unop.toOrderHom tuple.val tuple.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable abbrev incidenceChains (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    ChainComplex AddCommGrpCat.{0} ℕ :=
  (incidenceSimplicialSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)

noncomputable def incidenceChainInclusion (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    AddCommGrpCat.of ℤ ⟶ (incidenceChains incidence negative).X degree :=
  (incidenceSimplicialSet incidence negative).ιChainComplex (R := AddCommGrpCat.of ℤ) tuple

variable [Finite Chart]

noncomputable def affineSingularSimplicialMap (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    incidenceSimplicialSet incidence negative ⟶
      TopCat.toSSet.obj (TopCat.of (incidenceRealization incidence negative)) where
  app simplex := ↾tupleSingularSimplex incidence negative simplex.unop.len
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    exact (tupleSingularSimplex_precomp incidence negative selection.unop tuple).symm

noncomputable def affineSingularChainMap (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    incidenceChains incidence negative ⟶ integralSingularChains (incidenceRealization incidence negative) :=
  SSet.chainComplexMap (affineSingularSimplicialMap incidence negative) (AddCommGrpCat.of ℤ)

end IncidenceChains

section DualIdentification

variable {Ray : Type*} {Chart : Type}

noncomputable def incidenceDualEvaluation (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    (dualChainComplex 𝕜 (incidenceChains incidence negative)).X degree ⟶
      (negativeComplex 𝕜 incidence negative).X degree :=
  AddCommGrpCat.ofHom {
    toFun := fun cochain tuple => (incidenceChainInclusion incidence negative degree tuple ≫ cochain) (1 : ℤ)
    map_zero' := by funext tuple; simp
    map_add' := by intro first second; funext tuple; simp
  }

noncomputable def incidenceDualExtension (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ)
    (cochain : (negativeComplex 𝕜 incidence negative).X degree) :
    (dualChainComplex 𝕜 (incidenceChains incidence negative)).X degree :=
  Sigma.desc (fun tuple => AddCommGrpCat.ofHom (zmultiplesHom 𝕜 (cochain tuple)))

theorem incidenceDualEvaluation_extension (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ)
    (cochain : (negativeComplex 𝕜 incidence negative).X degree) :
    incidenceDualEvaluation 𝕜 incidence negative degree
      (incidenceDualExtension 𝕜 incidence negative degree cochain) = cochain := by
  funext tuple
  change (incidenceChainInclusion incidence negative degree tuple ≫
    incidenceDualExtension 𝕜 incidence negative degree cochain) (1 : ℤ) = cochain tuple
  rw [incidenceChainInclusion, incidenceDualExtension, SSet.ιChainComplex, Sigma.ι_comp_desc]
  change (zmultiplesHom 𝕜 (cochain tuple)) (1 : ℤ) = cochain tuple
  exact one_zsmul _

theorem incidenceDualEvaluation_injective (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    Function.Injective (incidenceDualEvaluation 𝕜 incidence negative degree) := by
  intro first second equal
  apply SSet.chainComplex_hom_ext
  intro tuple
  apply AddCommGrpCat.hom_ext
  have values : (incidenceChainInclusion incidence negative degree tuple ≫ first) (1 : ℤ) =
      (incidenceChainInclusion incidence negative degree tuple ≫ second) (1 : ℤ) := congrFun equal tuple
  exact (zmultiplesHom 𝕜).symm.injective values

noncomputable def incidenceDualDegreeIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    (dualChainComplex 𝕜 (incidenceChains incidence negative)).X degree ≅
      (negativeComplex 𝕜 incidence negative).X degree := by
  letI : IsIso (incidenceDualEvaluation 𝕜 incidence negative degree) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨incidenceDualEvaluation_injective 𝕜 incidence negative degree,
        fun cochain => ⟨incidenceDualExtension 𝕜 incidence negative degree cochain,
          incidenceDualEvaluation_extension 𝕜 incidence negative degree cochain⟩⟩
  exact asIso (incidenceDualEvaluation 𝕜 incidence negative degree)

theorem incidenceDualEvaluation_d (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    (dualChainComplex 𝕜 (incidenceChains incidence negative)).d degree (degree + 1) ≫
      incidenceDualEvaluation 𝕜 incidence negative (degree + 1) =
    incidenceDualEvaluation 𝕜 incidence negative degree ≫
      (negativeComplex 𝕜 incidence negative).d degree (degree + 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro cochain
  change (incidenceChains incidence negative).X degree ⟶ AddCommGrpCat.of 𝕜 at cochain
  funext tuple
  change ((incidenceChainInclusion incidence negative (degree + 1) tuple ≫
    (incidenceChains incidence negative).d (degree + 1) degree) ≫ cochain) (1 : ℤ) =
      (negativeComplex 𝕜 incidence negative).d degree (degree + 1)
        (incidenceDualEvaluation 𝕜 incidence negative degree cochain) tuple
  rw [incidenceChainInclusion, SSet.ιChainComplex_d,
    BondalThomsen.ClosedCoverReducedZeroCohomology.negativeComplex_d_apply, sum_comp]
  change AddCommGrpCat.homAddEquiv
    (∑ deleted : Fin (degree + 2), ((-1 : ℤ) ^ deleted.val •
      (incidenceSimplicialSet incidence negative).ιChainComplex
        ((incidenceSimplicialSet incidence negative).δ deleted tuple)) ≫ cochain) (1 : ℤ) = _
  rw [map_sum]
  simp only [zsmul_comp, map_zsmul]
  rw [AddMonoidHom.finsetSum_apply]
  simp only [AddMonoidHom.zsmul_apply]
  rfl

noncomputable def incidenceDualComparison (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    dualChainComplex 𝕜 (incidenceChains incidence negative) ⟶ negativeComplex 𝕜 incidence negative :=
  CochainComplex.ofHom (incidenceDualEvaluation 𝕜 incidence negative)
    (fun degree => (incidenceDualEvaluation_d 𝕜 incidence negative degree).symm)

noncomputable def incidenceDualIso (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    dualChainComplex 𝕜 (incidenceChains incidence negative) ≅ negativeComplex 𝕜 incidence negative := by
  letI : ∀ degree, IsIso ((incidenceDualComparison 𝕜 incidence negative).f degree) :=
    fun degree => (incidenceDualDegreeIso 𝕜 incidence negative degree).isIso_hom
  letI := HomologicalComplex.Hom.isIso_of_components (incidenceDualComparison 𝕜 incidence negative)
  exact asIso (incidenceDualComparison 𝕜 incidence negative)

end DualIdentification

section ConeCochains

variable {Ray : Type*} {Chart : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop) (anchor : Chart)
variable (cone : PreAbstractSimplicialComplex.IsCone
  (negativeChartComplex incidence negative) anchor)

def coneTuple (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    forbiddenTuple incidence negative (degree + 1) :=
  ⟨Fin.cons anchor tuple.val, by
    apply (tupleForbidden_iff_face incidence negative (degree + 1) _).mpr
    have enlarged := cone.insert_mem
      ((tupleForbidden_iff_face incidence negative degree tuple.val).mp tuple.property)
    convert enlarged using 1
    ext chart
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨column, rfl⟩
      refine Fin.cases ?_ (fun previous => ?_) column
      · exact Or.inl (Fin.cons_zero _ _)
      · exact Or.inr ⟨previous, by simp⟩
    · rintro (rfl | ⟨column, rfl⟩)
      · exact ⟨0, Fin.cons_zero _ _⟩
      · exact ⟨column.succ, Fin.cons_succ _ _ _⟩⟩

end ConeCochains

section ConeRealizations

variable {Vertex : Type} [Finite Vertex] [DecidableEq Vertex]

noncomputable def coneRealizationContraction (complex : AbstractSimplicialComplex Vertex)
    (anchor : Vertex) (cone : PreAbstractSimplicialComplex.IsCone
      complex.toPreAbstractSimplicialComplex anchor) :
    (ContinuousMap.id (AbstractSimplicialComplex.Realization complex)).Homotopy
      (ContinuousMap.const _ (AbstractSimplicialComplex.vertex complex anchor)) :=
  realizationAffineHomotopy complex (ContinuousMap.id _)
    (ContinuousMap.const _ (AbstractSimplicialComplex.vertex complex anchor)) (by
      intro point
      have enlarged := cone.insert_mem (AbstractSimplicialComplex.support_mem complex point)
      change insert anchor point.val.support ∈ complex at enlarged
      simp only [ContinuousMap.id_apply, ContinuousMap.const_apply,
        AbstractSimplicialComplex.vertex_val, Finsupp.support_single _ one_ne_zero,
        Finset.union_singleton]
      convert enlarged using 1; ext vertex; simp)

theorem coneRealization_contractible (complex : AbstractSimplicialComplex Vertex)
    (anchor : Vertex) (cone : PreAbstractSimplicialComplex.IsCone
      complex.toPreAbstractSimplicialComplex anchor) :
    ContractibleSpace (AbstractSimplicialComplex.Realization complex) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨AbstractSimplicialComplex.vertex complex anchor,
      ⟨coneRealizationContraction complex anchor cone⟩⟩

end ConeRealizations

section ConeComparison

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop) (anchor : Chart)
variable (cone : PreAbstractSimplicialComplex.IsCone
  (negativeChartComplex incidence negative) anchor)

def incidenceConeActiveAnchor : ActiveIndex (incidencePatches incidence negative) :=
  ⟨anchor, by
    obtain ⟨ray, negativeRay, contains⟩ := cone.apex_mem.2
    exact ⟨ray, negativeRay, contains anchor (Finset.mem_singleton_self _)⟩⟩

omit [Finite Chart] in
theorem activeIncidenceNerve_isCone :
    PreAbstractSimplicialComplex.IsCone
      (activeNerve (incidencePatches incidence negative)).toPreAbstractSimplicialComplex
      (incidenceConeActiveAnchor incidence negative anchor cone) where
  apex_mem := by
    change Finset.image Subtype.val {incidenceConeActiveAnchor incidence negative anchor cone} ∈
      coverNerve (incidencePatches incidence negative)
    rw [incidencePatches_coverNerve]
    simpa only [Finset.image_singleton, incidenceConeActiveAnchor] using cone.apex_mem
  insert_mem := by
    intro face present
    change face.image Subtype.val ∈ coverNerve (incidencePatches incidence negative) at present
    change (insert (incidenceConeActiveAnchor incidence negative anchor cone) face).image Subtype.val ∈
      coverNerve (incidencePatches incidence negative)
    rw [incidencePatches_coverNerve] at present ⊢
    simpa only [Finset.image_insert, incidenceConeActiveAnchor] using cone.insert_mem present

include anchor cone in
theorem incidenceCone_realization_contractible :
    ContractibleSpace (incidenceRealization incidence negative) :=
  coneRealization_contractible (activeNerve (incidencePatches incidence negative))
    (incidenceConeActiveAnchor incidence negative anchor cone)
    (activeIncidenceNerve_isCone incidence negative anchor cone)

end ConeComparison

section FaceCarriers

variable {Ray : Type*} {Chart : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

def faceCarrierNegative (face : Finset Chart) (ray : Ray) : Prop :=
  negative ray ∧ ∀ chart ∈ face, incidence ray chart

theorem faceCarrier_face_iff (face support : Finset Chart) :
    support ∈ negativeChartComplex incidence (faceCarrierNegative incidence negative face) ↔
      support.Nonempty ∧ support ∪ face ∈ negativeChartComplex incidence negative := by
  constructor
  · rintro ⟨nonempty, ray, ⟨negativeRay, onFace⟩, onSupport⟩
    refine ⟨nonempty, nonempty.mono Finset.subset_union_left, ray, negativeRay, ?_⟩
    intro chart present
    rcases Finset.mem_union.mp present with onLeft | onRight
    · exact onSupport chart onLeft
    · exact onFace chart onRight
  · rintro ⟨nonempty, _unionNonempty, ray, negativeRay, onUnion⟩
    exact ⟨nonempty, ray, ⟨negativeRay,
      fun chart present => onUnion chart (Finset.mem_union_right _ present)⟩,
      fun chart present => onUnion chart (Finset.mem_union_left _ present)⟩

theorem faceCarrier_tuple_iff (face : Finset Chart) (degree : ℕ)
    (tuple : Fin (degree + 1) → Chart) :
    tupleForbidden incidence (faceCarrierNegative incidence negative face) degree tuple ↔
      Finset.univ.image tuple ∪ face ∈ negativeChartComplex incidence negative := by
  rw [tupleForbidden_iff_face, faceCarrier_face_iff]
  exact and_iff_right ⟨tuple 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

theorem faceCarrier_isCone (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (anchor : Chart)
    (onFace : anchor ∈ face) :
    PreAbstractSimplicialComplex.IsCone
      (negativeChartComplex incidence (faceCarrierNegative incidence negative face)) anchor where
  apex_mem := by
    obtain ⟨_nonempty, ray, negativeRay, contains⟩ := present
    exact ⟨Finset.singleton_nonempty _, ray, ⟨negativeRay, contains⟩,
      fun chart member => (Finset.mem_singleton.mp member) ▸ contains anchor onFace⟩
  insert_mem := by
    intro support supported
    obtain ⟨nonempty, ray, ⟨negativeRay, containsFace⟩, containsSupport⟩ := supported
    refine ⟨Finset.insert_nonempty _ _, ray, ⟨negativeRay, containsFace⟩, ?_⟩
    intro chart member
    rcases Finset.mem_insert.mp member with same | inSupport
    · exact containsFace chart (same ▸ onFace)
    · exact containsSupport chart inSupport

def faceCarrierSimplicialInclusion (face : Finset Chart) :
    incidenceSimplicialSet incidence (faceCarrierNegative incidence negative face) ⟶
      incidenceSimplicialSet incidence negative where
  app _simplex := ↾fun tuple => ⟨tuple.val, by
    obtain ⟨ray, ⟨negativeRay, _onFace⟩, contains⟩ := tuple.property
    exact ⟨ray, negativeRay, contains⟩⟩
  naturality {source target} _selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    rfl

noncomputable def faceCarrierChainInclusion (face : Finset Chart) :
    incidenceChains incidence (faceCarrierNegative incidence negative face) ⟶
      incidenceChains incidence negative :=
  SSet.chainComplexMap (faceCarrierSimplicialInclusion incidence negative face) (AddCommGrpCat.of ℤ)

theorem faceCarrierChainInclusion_generator (face : Finset Chart) (degree : ℕ)
    (tuple : forbiddenTuple incidence (faceCarrierNegative incidence negative face) degree) :
    incidenceChainInclusion incidence (faceCarrierNegative incidence negative face) degree tuple ≫
      (faceCarrierChainInclusion incidence negative face).f degree =
    incidenceChainInclusion incidence negative degree
      ((faceCarrierSimplicialInclusion incidence negative face).app (Opposite.op ⦋degree⦌) tuple) := by
  exact SSet.ι_chainComplexMap_f _ _ (faceCarrierSimplicialInclusion incidence negative face)
    (AddCommGrpCat.of ℤ) tuple

def faceCarrierRefinement (smaller larger : Finset Chart) (subset : smaller ⊆ larger) :
    incidenceSimplicialSet incidence (faceCarrierNegative incidence negative larger) ⟶
      incidenceSimplicialSet incidence (faceCarrierNegative incidence negative smaller) where
  app _simplex := ↾fun tuple => ⟨tuple.val, by
    obtain ⟨ray, ⟨negativeRay, onLarger⟩, contains⟩ := tuple.property
    exact ⟨ray, ⟨negativeRay, fun chart member => onLarger chart (subset member)⟩, contains⟩⟩
  naturality {source target} _selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    rfl

noncomputable def faceCarrierChainRefinement (smaller larger : Finset Chart) (subset : smaller ⊆ larger) :
    incidenceChains incidence (faceCarrierNegative incidence negative larger) ⟶
      incidenceChains incidence (faceCarrierNegative incidence negative smaller) :=
  SSet.chainComplexMap (faceCarrierRefinement incidence negative smaller larger subset) (AddCommGrpCat.of ℤ)

theorem faceCarrierChainRefinement_inclusion (smaller larger : Finset Chart) (subset : smaller ⊆ larger) :
    faceCarrierChainRefinement incidence negative smaller larger subset ≫
      faceCarrierChainInclusion incidence negative smaller =
    faceCarrierChainInclusion incidence negative larger := by
  exact (((SSet.chainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map_comp
    (faceCarrierRefinement incidence negative smaller larger subset)
    (faceCarrierSimplicialInclusion incidence negative smaller)).symm

end FaceCarriers

end BondalThomsen.ConvexNerveIncidenceHomologyComparison
