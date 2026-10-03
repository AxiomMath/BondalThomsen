module

public import BondalThomsen.Cohomology.FiniteQuasicoherentPushforward
public import BondalThomsen.Derived.SheafExtCohomologyDimensionShift
public import BondalThomsen.Toric.Frobenius.MultiplicationCohomologyTransport

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace BondalThomsen.FiniteQuasicoherentCohomologyTower

universe u

noncomputable section

variable {Source Target : Scheme.{u}}

def IsCohomologicallyAcyclic (coefficient : Source.Modules) : Prop :=
  ∀ degree : ℕ, Subsingleton (Cohomology coefficient (degree + 1))

theorem isCohomologicallyAcyclic_of_isFlasque (coefficient : Source.Modules)
    [coefficient.presheaf.IsFlasque] : IsCohomologicallyAcyclic coefficient :=
  fun degree => Scheme.Modules.subsingleton_cohomology_succ_of_isFlasque coefficient degree

structure QuasicoherentResolutionStep (coefficient : Source.Modules) where
  middle : Source.Modules
  next : Source.Modules
  middle_quasicoherent : middle.IsQuasicoherent
  next_quasicoherent : next.IsQuasicoherent
  inclusion : coefficient ⟶ middle
  projection : middle ⟶ next
  zero : inclusion ≫ projection = 0
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

structure QuasicoherentResolutionTower (coefficient : Source.Modules) where
  object : ℕ → Source.Modules
  initial : object 0 ≅ coefficient
  middle : ℕ → Source.Modules
  object_quasicoherent : ∀ stage, (object stage).IsQuasicoherent
  middle_quasicoherent : ∀ stage, (middle stage).IsQuasicoherent
  inclusion : ∀ stage, object stage ⟶ middle stage
  projection : ∀ stage, middle stage ⟶ object (stage + 1)
  zero : ∀ stage, inclusion stage ≫ projection stage = 0
  shortExact : ∀ stage,
    (ShortComplex.mk (inclusion stage) (projection stage) (zero stage)).ShortExact

namespace QuasicoherentResolutionTower

variable {coefficient : Source.Modules}

def successiveCoefficient (quasicoherent : coefficient.IsQuasicoherent)
    (extension : ∀ current : Source.Modules, current.IsQuasicoherent →
      QuasicoherentResolutionStep current) :
    ℕ → {current : Source.Modules // current.IsQuasicoherent}
  | 0 => ⟨coefficient, quasicoherent⟩
  | stage + 1 =>
      let previous := successiveCoefficient quasicoherent extension stage
      let step := extension previous.val previous.property
      ⟨step.next, step.next_quasicoherent⟩

def ofSteps (quasicoherent : coefficient.IsQuasicoherent)
    (extension : ∀ current : Source.Modules, current.IsQuasicoherent →
      QuasicoherentResolutionStep current) : QuasicoherentResolutionTower coefficient where
  object stage := (successiveCoefficient quasicoherent extension stage).val
  initial := Iso.refl _
  middle stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).middle
  object_quasicoherent stage := (successiveCoefficient quasicoherent extension stage).property
  middle_quasicoherent stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).middle_quasicoherent
  inclusion stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).inclusion
  projection stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).projection
  zero stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).zero
  shortExact stage := (extension (successiveCoefficient quasicoherent extension stage).val
    (successiveCoefficient quasicoherent extension stage).property).shortExact

def sequence (tower : QuasicoherentResolutionTower coefficient) (stage : ℕ) :
    ShortComplex Source.Modules :=
  ShortComplex.mk (tower.inclusion stage) (tower.projection stage) (tower.zero stage)

theorem sequence_shortExact (tower : QuasicoherentResolutionTower coefficient) (stage : ℕ) :
    (tower.sequence stage).ShortExact := tower.shortExact stage

def pushforward (morphism : Source ⟶ Target) [IsAffineHom morphism]
    (tower : QuasicoherentResolutionTower coefficient) :
    QuasicoherentResolutionTower ((Scheme.Modules.pushforward morphism).obj coefficient) where
  object stage := (Scheme.Modules.pushforward morphism).obj (tower.object stage)
  initial := (Scheme.Modules.pushforward morphism).mapIso tower.initial
  middle stage := (Scheme.Modules.pushforward morphism).obj (tower.middle stage)
  object_quasicoherent stage := by
    let := tower.object_quasicoherent stage
    exact FiniteQuasicoherentPushforward.affinePushforward_isQuasicoherent _ _
  middle_quasicoherent stage := by
    let := tower.middle_quasicoherent stage
    exact FiniteQuasicoherentPushforward.affinePushforward_isQuasicoherent _ _
  inclusion stage := (Scheme.Modules.pushforward morphism).map (tower.inclusion stage)
  projection stage := (Scheme.Modules.pushforward morphism).map (tower.projection stage)
  zero stage := by rw [← Functor.map_comp, tower.zero stage, Functor.map_zero]
  shortExact stage := by
    let : (tower.sequence stage).X₁.IsQuasicoherent := tower.object_quasicoherent stage
    let : (tower.sequence stage).X₂.IsQuasicoherent := tower.middle_quasicoherent stage
    let : (tower.sequence stage).X₃.IsQuasicoherent := tower.object_quasicoherent (stage + 1)
    exact FiniteQuasicoherentPushforward.affinePushforward_shortExact morphism
      (tower.sequence_shortExact stage)

theorem pushforward_sequence_shortExact (morphism : Source ⟶ Target) [IsAffineHom morphism]
    (tower : QuasicoherentResolutionTower coefficient) (stage : ℕ) :
    ((tower.sequence stage).map (Scheme.Modules.pushforward morphism)).ShortExact :=
  (tower.pushforward morphism).sequence_shortExact stage

structure AcyclicFor (tower : QuasicoherentResolutionTower coefficient)
    (morphism : Source ⟶ Target) : Prop where
  source_middle : ∀ stage, IsCohomologicallyAcyclic (tower.middle stage)
  target_middle : ∀ stage, IsCohomologicallyAcyclic
    ((Scheme.Modules.pushforward morphism).obj (tower.middle stage))

theorem acyclicFor_of_isFlasque (tower : QuasicoherentResolutionTower coefficient)
    (morphism : Source ⟶ Target) [∀ stage, (tower.middle stage).presheaf.IsFlasque] :
    tower.AcyclicFor morphism where
  source_middle stage := isCohomologicallyAcyclic_of_isFlasque _
  target_middle stage := by
    let := ToricMultiplicationCohomologyTransport.pushforward_isFlasque morphism
      (tower.middle stage)
    exact isCohomologicallyAcyclic_of_isFlasque _

end QuasicoherentResolutionTower

theorem cohomologyδ_surjective_of_middle_acyclic {sequence : ShortComplex Source.Modules}
    (exact_sequence : sequence.ShortExact) (degree : ℕ)
    (vanishing : Subsingleton (Cohomology sequence.X₂ (degree + 1))) :
    Function.Surjective (cohomologyδ exact_sequence degree (degree + 1) rfl) := by
  let := vanishing
  intro element
  exact (exact_cohomologyδ_cohomologyMap exact_sequence degree (degree + 1) rfl element).mp
    (Subsingleton.elim _ _)

theorem cohomologyδ_injective_of_middle_acyclic {sequence : ShortComplex Source.Modules}
    (exact_sequence : sequence.ShortExact) (degree : ℕ)
    (vanishing : Subsingleton (Cohomology sequence.X₂ degree)) :
    Function.Injective (cohomologyδ exact_sequence degree (degree + 1) rfl) := by
  let := vanishing
  rw [injective_iff_map_eq_zero]
  intro element equality
  obtain ⟨previous, rfl⟩ :=
    (exact_cohomologyMap_cohomologyδ exact_sequence degree (degree + 1) rfl element).mp equality
  rw [Subsingleton.elim previous 0, map_zero]

def cohomologySuccEquivOfMiddleAcyclic {sequence : ShortComplex Source.Modules}
    (exact_sequence : sequence.ShortExact) (degree : ℕ)
    (vanishing : Subsingleton (Cohomology sequence.X₂ (degree + 1)))
    (next_vanishing : Subsingleton (Cohomology sequence.X₂ (degree + 2))) :
    Cohomology sequence.X₃ (degree + 1) ≃+ Cohomology sequence.X₁ (degree + 2) :=
  AddEquiv.ofBijective (cohomologyδ exact_sequence (degree + 1) (degree + 2) rfl)
    ⟨cohomologyδ_injective_of_middle_acyclic exact_sequence _ vanishing,
      cohomologyδ_surjective_of_middle_acyclic exact_sequence _ next_vanishing⟩

def cohomologyOneQuotientEquivOfMiddleAcyclic {sequence : ShortComplex Source.Modules}
    (exact_sequence : sequence.ShortExact)
    (vanishing : Subsingleton (Cohomology sequence.X₂ 1)) :
    (Cohomology sequence.X₃ 0 ⧸ (cohomologyMap sequence.g 0).range) ≃+
      Cohomology sequence.X₁ 1 :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
    ext element
    exact (exact_cohomologyMap_cohomologyδ exact_sequence 0 1 rfl element).symm)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (cohomologyδ exact_sequence 0 1 rfl)
      (cohomologyδ_surjective_of_middle_acyclic exact_sequence 0 vanishing))

def pushforwardCohomologyOneEquivOfMiddleAcyclic (morphism : Source ⟶ Target)
    {sequence : ShortComplex Source.Modules} (exact_sequence : sequence.ShortExact)
    (pushforward_exact : (sequence.map (Scheme.Modules.pushforward morphism)).ShortExact)
    (source_vanishing : Subsingleton (Cohomology sequence.X₂ 1))
    (target_vanishing : Subsingleton
      (Cohomology ((Scheme.Modules.pushforward morphism).obj sequence.X₂) 1)) :
    Cohomology ((Scheme.Modules.pushforward morphism).obj sequence.X₁) 1 ≃+
      Cohomology sequence.X₁ 1 :=
  (cohomologyOneQuotientEquivOfMiddleAcyclic pushforward_exact target_vanishing).symm.trans
    ((QuotientAddGroup.congr _ _
      (ToricMultiplicationCohomologyTransport.pushforwardCohomologyZeroEquiv morphism sequence.X₃)
      (by
        ext element
        rw [AddSubgroup.mem_map]
        constructor
        · rintro ⟨image, ⟨previous, rfl⟩, rfl⟩
          exact ⟨ToricMultiplicationCohomologyTransport.pushforwardCohomologyZeroEquiv
            morphism sequence.X₂ previous,
            (ToricMultiplicationCohomologyTransport.pushforwardCohomologyZeroEquiv_naturality
              morphism sequence.g previous).symm⟩
        · rintro ⟨section_class, rfl⟩
          obtain ⟨previous, rfl⟩ :=
            (ToricMultiplicationCohomologyTransport.pushforwardCohomologyZeroEquiv
              morphism sequence.X₂).surjective section_class
          exact ⟨cohomologyMap ((Scheme.Modules.pushforward morphism).map sequence.g) 0 previous,
            ⟨previous, rfl⟩,
            ToricMultiplicationCohomologyTransport.pushforwardCohomologyZeroEquiv_naturality
              morphism sequence.g previous⟩)).trans
      (cohomologyOneQuotientEquivOfMiddleAcyclic exact_sequence source_vanishing))

namespace QuasicoherentResolutionTower

variable {coefficient : Source.Modules}

set_option maxHeartbeats 800000 in
def cohomologyEquivAt (tower : QuasicoherentResolutionTower coefficient)
    (morphism : Source ⟶ Target) [IsAffineHom morphism] (acyclic : tower.AcyclicFor morphism) :
    ∀ degree stage, Cohomology ((Scheme.Modules.pushforward morphism).obj
      (tower.object stage)) degree ≃+ Cohomology (tower.object stage) degree := by
  intro degree
  induction degree with
  | zero =>
    intro stage
    exact ToricMultiplicationCohomologyTransport.pushforwardCohomologyZeroEquiv morphism _
  | succ degree induction_hypothesis =>
    intro stage
    cases degree with
    | zero =>
      exact pushforwardCohomologyOneEquivOfMiddleAcyclic morphism
        (sequence := tower.sequence stage)
        (tower.sequence_shortExact stage) (tower.pushforward_sequence_shortExact morphism stage)
        (acyclic.source_middle stage 0) (acyclic.target_middle stage 0)
    | succ previous =>
      exact (cohomologySuccEquivOfMiddleAcyclic
        (sequence := (tower.sequence stage).map (Scheme.Modules.pushforward morphism))
        (tower.pushforward_sequence_shortExact morphism stage)
        previous (acyclic.target_middle stage previous)
        (acyclic.target_middle stage (previous + 1))).symm.trans
        ((induction_hypothesis (stage + 1)).trans
          (cohomologySuccEquivOfMiddleAcyclic (sequence := tower.sequence stage)
            (tower.sequence_shortExact stage) previous (acyclic.source_middle stage previous)
            (acyclic.source_middle stage (previous + 1))))

def cohomologyEquiv (tower : QuasicoherentResolutionTower coefficient)
    (morphism : Source ⟶ Target) [IsAffineHom morphism]
    (acyclic : tower.AcyclicFor morphism) (degree : ℕ) :
    Cohomology ((Scheme.Modules.pushforward morphism).obj coefficient) degree ≃+
      Cohomology coefficient degree :=
  (((cohomologyFunctor Target degree).mapIso
    ((Scheme.Modules.pushforward morphism).mapIso tower.initial)).symm.addCommGroupIsoToAddEquiv).trans
    ((tower.cohomologyEquivAt morphism acyclic degree 0).trans
      ((cohomologyFunctor Source degree).mapIso tower.initial).addCommGroupIsoToAddEquiv)

def finiteCohomologyEquiv (tower : QuasicoherentResolutionTower coefficient)
    (morphism : Source ⟶ Target) [IsFinite morphism]
    (acyclic : tower.AcyclicFor morphism) (degree : ℕ) :
    Cohomology ((Scheme.Modules.pushforward morphism).obj coefficient) degree ≃+
      Cohomology coefficient degree :=
  tower.cohomologyEquiv morphism acyclic degree

end QuasicoherentResolutionTower

end

end BondalThomsen.FiniteQuasicoherentCohomologyTower

