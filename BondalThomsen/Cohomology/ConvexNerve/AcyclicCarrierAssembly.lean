module

public import BondalThomsen.Cohomology.ConvexNerve.IncidenceHomologyComparison
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ConvexNerveIncidenceHomologyComparison
open BondalThomsen.ToricCechNegativeSupportComparison
open BondalThomsen.ToricNegativeSupportRelativeCohomology
open scoped Classical Simplicial

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveAcyclicCarrierAssembly

section IntegralCones

variable {Ray : Type*} {Chart : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

noncomputable abbrev incidenceAugmentationObject : AddCommGrpCat.{0} :=
  ∐ fun _point : Unit => AddCommGrpCat.of ℤ

def augmentedIncidenceSet : SimplicialObject.Augmented (Type) where
  left := incidenceSimplicialSet incidence negative
  right := Unit
  hom := { app := fun _simplex => ↾fun _tuple => () }

noncomputable def incidenceChainAugmentationMap :
    incidenceChains incidence negative ⟶
      (ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((SimplicialObject.Augmented.whiskering (Type) AddCommGrpCat.{0}).obj
      (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj (augmentedIncidenceSet incidence negative))

noncomputable def incidenceChainAugmentation :
    (incidenceChains incidence negative).X 0 ⟶ incidenceAugmentationObject :=
  (incidenceChainAugmentationMap incidence negative).f 0

theorem incidenceChainAugmentation_generator (tuple : forbiddenTuple incidence negative 0) :
    incidenceChainInclusion incidence negative 0 tuple ≫ incidenceChainAugmentation incidence negative =
      Sigma.ι (fun _point : Unit => AddCommGrpCat.of ℤ) () := by
  unfold incidenceChainAugmentation incidenceChainAugmentationMap
  rw [AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
  change Sigma.ι (fun _tuple : forbiddenTuple incidence negative 0 => AddCommGrpCat.of ℤ) tuple ≫
    Sigma.map' (g := fun _tuple : forbiddenTuple incidence negative 0 => AddCommGrpCat.of ℤ)
      (f := fun _point : Unit => AddCommGrpCat.of ℤ)
      (fun _tuple => ()) (fun _tuple => 𝟙 (AddCommGrpCat.of ℤ)) = _
  simp

theorem incidenceChainAugmentation_zero :
    (incidenceChains incidence negative).d 1 0 ≫ incidenceChainAugmentation incidence negative = 0 := by
  have identity := (incidenceChainAugmentationMap incidence negative).comm 1 0
  rw [HomologicalComplex.single_obj_d] at identity
  rw [comp_zero] at identity
  exact identity.symm

variable (anchor : Chart) (cone : PreAbstractSimplicialComplex.IsCone
  (negativeChartComplex incidence negative) anchor)

def coneVertexTuple : forbiddenTuple incidence negative 0 :=
  ⟨fun _column => anchor, by
    obtain ⟨ray, negativeRay, contains⟩ := cone.apex_mem.2
    exact ⟨ray, negativeRay, fun _column => contains anchor (Finset.mem_singleton_self _)⟩⟩

def incidenceConeExtraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy (augmentedIncidenceSet incidence negative) where
  s' := ↾fun _point => coneVertexTuple incidence negative anchor cone
  s degree := ↾coneTuple incidence negative anchor cone degree
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro point
    rfl
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    funext column
    fin_cases column
    rfl
  s_comp_δ₀ degree := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    funext column
    simp [SimplicialObject.δ, SimplexCategory.δ, incidenceSimplicialSet,
      coneTuple, augmentedIncidenceSet]
  s_comp_δ degree deleted := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    funext column
    dsimp [SimplicialObject.δ, SimplexCategory.δ, incidenceSimplicialSet,
      coneTuple, augmentedIncidenceSet]
    cases column using Fin.cases <;> simp
  s_comp_σ degree repeated := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    funext column
    dsimp [SimplicialObject.σ, SimplexCategory.σ, incidenceSimplicialSet,
      coneTuple, augmentedIncidenceSet]
    cases column using Fin.cases <;> simp

noncomputable def incidenceConeChainHomotopyEquiv :
    HomotopyEquiv (incidenceChains incidence negative)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj (∐ fun _point : Unit => AddCommGrpCat.of ℤ)) :=
  ((incidenceConeExtraDegeneracy incidence negative anchor cone).map
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).homotopyEquiv

noncomputable def incidenceConeChainContraction (degree : ℕ) :
    (incidenceChains incidence negative).X degree ⟶
      (incidenceChains incidence negative).X (degree + 1) :=
  -((incidenceConeChainHomotopyEquiv incidence negative anchor cone).homotopyHomInvId.hom
    degree (degree + 1))

theorem incidenceConeChainContraction_identity_zero :
    incidenceConeChainContraction incidence negative anchor cone 0 ≫
      (incidenceChains incidence negative).d 1 0 =
    𝟙 ((incidenceChains incidence negative).X 0) -
      incidenceChainAugmentation incidence negative ≫
        (incidenceConeChainHomotopyEquiv incidence negative anchor cone).inv.f 0 := by
  let equivalence := incidenceConeChainHomotopyEquiv incidence negative anchor cone
  have identity := equivalence.homotopyHomInvId.comm 0
  rw [Homotopy.dNext_zero_chainComplex, zero_add, Homotopy.prevD_chainComplex] at identity
  change incidenceChainAugmentation incidence negative ≫ equivalence.inv.f 0 = _ at identity
  change (-equivalence.homotopyHomInvId.hom 0 1) ≫ _ = _
  rw [neg_comp]
  have rearranged := congrArg (fun value => 𝟙 ((incidenceChains incidence negative).X 0) - value) identity
  have reversed := rearranged.symm
  change 𝟙 ((incidenceChains incidence negative).X 0) -
    (equivalence.homotopyHomInvId.hom 0 1 ≫ (incidenceChains incidence negative).d 1 0 +
      𝟙 ((incidenceChains incidence negative).X 0)) = _ at reversed
  have cancellation : ∀ value : (incidenceChains incidence negative).X 0 ⟶
      (incidenceChains incidence negative).X 0,
      𝟙 _ - (value + 𝟙 _) = -value := by intro value; abel
  rw [cancellation] at reversed
  exact reversed

include anchor cone in
theorem incidenceConeChains_augmentedExact :
    (ShortComplex.mk ((incidenceChains incidence negative).d 1 0)
      (incidenceChainAugmentation incidence negative) (incidenceChainAugmentation_zero incidence negative)).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro cycle closed
  refine ⟨incidenceConeChainContraction incidence negative anchor cone 0 cycle, ?_⟩
  have identity := ConcreteCategory.congr_hom
    (incidenceConeChainContraction_identity_zero incidence negative anchor cone) cycle
  change (incidenceChains incidence negative).d 1 0
    (incidenceConeChainContraction incidence negative anchor cone 0 cycle) =
    cycle - (incidenceConeChainHomotopyEquiv incidence negative anchor cone).inv.f 0
      (incidenceChainAugmentation incidence negative cycle) at identity
  simpa only [closed, map_zero, sub_zero] using identity

include anchor cone in
theorem incidenceConeChains_homology_positive_isZero (degree : ℕ) :
    IsZero ((incidenceChains incidence negative).homology (degree + 1)) := by
  have singleZero : IsZero
      (((ChainComplex.single₀ AddCommGrpCat.{0}).obj
        (∐ fun _point : Unit => AddCommGrpCat.of ℤ)).X (degree + 1)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  exact (HomologicalComplex.ExactAt.of_isZero singleZero).isZero_homology.of_iso
    ((incidenceConeChainHomotopyEquiv incidence negative anchor cone).toHomologyIso (degree + 1))

include anchor cone in
theorem incidenceConeChains_exactAt_positive (degree : ℕ) :
    (incidenceChains incidence negative).ExactAt (degree + 1) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (incidenceConeChains_homology_positive_isZero incidence negative anchor cone degree)

end IntegralCones

section CycleLifts

noncomputable def integerCycleLift (sequence : ShortComplex AddCommGrpCat.{0})
    (exact : sequence.Exact) (cycle : AddCommGrpCat.of ℤ ⟶ sequence.X₂)
    (closed : cycle ≫ sequence.g = 0) : AddCommGrpCat.of ℤ ⟶ sequence.X₁ := by
  have closedValue : sequence.g (cycle (1 : ℤ)) = 0 :=
    ConcreteCategory.congr_hom closed (1 : ℤ)
  let filling := ((ShortComplex.ab_exact_iff sequence).mp exact (cycle (1 : ℤ)) closedValue).choose
  exact AddCommGrpCat.ofHom (zmultiplesHom sequence.X₁ filling)

theorem integerCycleLift_comp (sequence : ShortComplex AddCommGrpCat.{0})
    (exact : sequence.Exact) (cycle : AddCommGrpCat.of ℤ ⟶ sequence.X₂)
    (closed : cycle ≫ sequence.g = 0) :
    integerCycleLift sequence exact cycle closed ≫ sequence.f = cycle := by
  apply AddCommGrpCat.int_hom_ext
  change sequence.f ((1 : ℤ) • _) = cycle 1
  rw [one_zsmul]
  exact ((ShortComplex.ab_exact_iff sequence).mp exact (cycle 1)
    (ConcreteCategory.congr_hom closed 1)).choose_spec

end CycleLifts

section AcyclicCarriers

variable (simplicial : SSet.{0}) (target : ChainComplex AddCommGrpCat.{0} ℕ)
variable {augmentationObject : AddCommGrpCat.{0}}
variable (augmentation : target.X 0 ⟶ augmentationObject)

structure IntegralAcyclicCarrier where
  complex : ∀ degree, simplicial _⦋degree⦌ → ChainComplex AddCommGrpCat.{0} ℕ
  inclusion : ∀ degree simplex, complex degree simplex ⟶ target
  inclusion_mono : ∀ degree simplex component, Mono ((inclusion degree simplex).f component)
  faceMap : ∀ degree (deleted : Fin (degree + 2)) (simplex : simplicial _⦋degree + 1⦌),
    complex degree (simplicial.δ deleted simplex) ⟶ complex (degree + 1) simplex
  faceMap_inclusion : ∀ degree deleted simplex,
    faceMap degree deleted simplex ≫ inclusion (degree + 1) simplex =
      inclusion degree (simplicial.δ deleted simplex)
  augmentation_zero : ∀ degree simplex,
    (complex degree simplex).d 1 0 ≫ (inclusion degree simplex).f 0 ≫ augmentation = 0
  exact_zero : ∀ degree simplex,
    (ShortComplex.mk ((complex degree simplex).d 1 0)
      ((inclusion degree simplex).f 0 ≫ augmentation)
      (augmentation_zero degree simplex)).Exact
  exact_positive : ∀ degree simplex component,
    (complex degree simplex).ExactAt (component + 1)

namespace IntegralAcyclicCarrier

variable {simplicial target augmentation}
variable (carrier : IntegralAcyclicCarrier simplicial target augmentation)

structure CarriedIntegralChainMap
    (mapping : simplicial.chainComplex (AddCommGrpCat.of ℤ) ⟶ target) where
  value : ∀ degree simplex, AddCommGrpCat.of ℤ ⟶ (carrier.complex degree simplex).X degree
  value_inclusion : ∀ degree simplex,
    value degree simplex ≫ (carrier.inclusion degree simplex).f degree =
      simplicial.ιChainComplex simplex ≫ mapping.f degree

def CarrierHomotopyValues (degree : ℕ) :=
  ∀ simplex : simplicial _⦋degree⦌,
    AddCommGrpCat.of ℤ ⟶ (carrier.complex degree simplex).X (degree + 1)

noncomputable def carrierHomotopyComponent (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree) :
    (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X degree ⟶ target.X (degree + 1) :=
  Sigma.desc fun simplex => values simplex ≫ (carrier.inclusion degree simplex).f (degree + 1)

theorem carrierHomotopyComponent_generator (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree) (simplex : simplicial _⦋degree⦌) :
    simplicial.ιChainComplex simplex ≫ carrier.carrierHomotopyComponent degree values =
      values simplex ≫ (carrier.inclusion degree simplex).f (degree + 1) :=
  Sigma.ι_comp_desc _ _

variable {mapping : simplicial.chainComplex (AddCommGrpCat.of ℤ) ⟶ target}
variable (carried : carrier.CarriedIntegralChainMap mapping)

noncomputable def initialCarrierValues
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) : carrier.CarrierHomotopyValues 0 :=
  fun simplex => integerCycleLift _ (carrier.exact_zero 0 simplex) (carried.value 0 simplex) (by
    rw [← Category.assoc, carried.value_inclusion, Category.assoc, augmentationZero, comp_zero])

theorem initialCarrierComponent_boundary
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) :
    carrier.carrierHomotopyComponent 0 (carrier.initialCarrierValues carried augmentationZero) ≫
      target.d 1 0 = mapping.f 0 := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, carrierHomotopyComponent_generator, Category.assoc,
    (carrier.inclusion 0 simplex).comm]
  rw [← Category.assoc, initialCarrierValues, integerCycleLift_comp, carried.value_inclusion]

noncomputable def carrierResidual (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree) (simplex : simplicial _⦋degree + 1⦌) :
    AddCommGrpCat.of ℤ ⟶ (carrier.complex (degree + 1) simplex).X (degree + 1) :=
  carried.value (degree + 1) simplex -
    ∑ deleted : Fin (degree + 2), ((-1 : ℤ) ^ deleted.val) •
      (values (simplicial.δ deleted simplex) ≫ (carrier.faceMap degree deleted simplex).f (degree + 1))

theorem carrierResidual_inclusion (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree) (simplex : simplicial _⦋degree + 1⦌) :
    carrier.carrierResidual carried degree values simplex ≫
      (carrier.inclusion (degree + 1) simplex).f (degree + 1) =
    simplicial.ιChainComplex simplex ≫
      (mapping.f (degree + 1) -
        (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
          carrier.carrierHomotopyComponent degree values) := by
  rw [carrierResidual, sub_comp, carried.value_inclusion, sum_comp, comp_sub,
    ← Category.assoc, SSet.ιChainComplex_d, sum_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro deleted _member
  rw [zsmul_comp, zsmul_comp, Category.assoc, ← HomologicalComplex.comp_f,
    carrier.faceMap_inclusion, carrierHomotopyComponent_generator]

theorem carrierResidual_closed (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree)
    (previous : (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X (degree - 1) ⟶ target.X degree)
    (equation : mapping.f degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d degree (degree - 1) ≫ previous +
        carrier.carrierHomotopyComponent degree values ≫ target.d (degree + 1) degree)
    (simplex : simplicial _⦋degree + 1⦌) :
    carrier.carrierResidual carried degree values simplex ≫
      (carrier.complex (degree + 1) simplex).d (degree + 1) degree = 0 := by
  let := carrier.inclusion_mono (degree + 1) simplex degree
  apply (cancel_mono ((carrier.inclusion (degree + 1) simplex).f degree)).mp
  rw [zero_comp, Category.assoc, ← (carrier.inclusion (degree + 1) simplex).comm,
    ← Category.assoc, carrierResidual_inclusion, Category.assoc, sub_comp,
    mapping.comm, Category.assoc, equation, comp_add, ← Category.assoc,
    HomologicalComplex.d_comp_d, zero_comp, zero_add, sub_self, comp_zero]

noncomputable def nextCarrierValues (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree)
    (previous : (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X (degree - 1) ⟶ target.X degree)
    (equation : mapping.f degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d degree (degree - 1) ≫ previous +
        carrier.carrierHomotopyComponent degree values ≫ target.d (degree + 1) degree) :
    carrier.CarrierHomotopyValues (degree + 1) := fun simplex =>
  integerCycleLift ((carrier.complex (degree + 1) simplex).sc' (degree + 2) (degree + 1) degree)
    ((HomologicalComplex.exactAt_iff' _ (degree + 2) (degree + 1) degree
      (by simp) (by simp)).mp (carrier.exact_positive (degree + 1) simplex degree))
    (carrier.carrierResidual carried degree values simplex)
    (carrier.carrierResidual_closed carried degree values previous equation simplex)

theorem nextCarrierComponent_boundary (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree)
    (previous : (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X (degree - 1) ⟶ target.X degree)
    (equation : mapping.f degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d degree (degree - 1) ≫ previous +
        carrier.carrierHomotopyComponent degree values ≫ target.d (degree + 1) degree) :
    carrier.carrierHomotopyComponent (degree + 1)
        (carrier.nextCarrierValues carried degree values previous equation) ≫
      target.d (degree + 2) (degree + 1) =
    mapping.f (degree + 1) -
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
        carrier.carrierHomotopyComponent degree values := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, carrierHomotopyComponent_generator, Category.assoc,
    (carrier.inclusion (degree + 1) simplex).comm, ← Category.assoc]
  have filling := integerCycleLift_comp
    ((carrier.complex (degree + 1) simplex).sc' (degree + 2) (degree + 1) degree)
    ((HomologicalComplex.exactAt_iff' _ (degree + 2) (degree + 1) degree
      (by simp) (by simp)).mp (carrier.exact_positive (degree + 1) simplex degree))
    (carrier.carrierResidual carried degree values simplex)
    (carrier.carrierResidual_closed carried degree values previous equation simplex)
  change carrier.nextCarrierValues carried degree values previous equation simplex ≫
    (carrier.complex (degree + 1) simplex).d (degree + 2) (degree + 1) =
      carrier.carrierResidual carried degree values simplex at filling
  rw [filling, carrierResidual_inclusion]

noncomputable def recursiveCarrierHomotopyValues
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) :
    (degree : ℕ) → Σ' (previous :
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X (degree - 1) ⟶ target.X degree)
      (values : carrier.CarrierHomotopyValues degree),
      mapping.f degree =
        ((simplicial.chainComplex (AddCommGrpCat.of ℤ)).d degree (degree - 1) ≫ previous +
          carrier.carrierHomotopyComponent degree values ≫ target.d (degree + 1) degree) :=
  Nat.rec
    ⟨0, carrier.initialCarrierValues carried augmentationZero, by
      rw [comp_zero, zero_add]
      exact (carrier.initialCarrierComponent_boundary carried augmentationZero).symm⟩
    (fun degree previousData => ⟨carrier.carrierHomotopyComponent degree previousData.2.1,
      carrier.nextCarrierValues carried degree previousData.2.1 previousData.1 previousData.2.2, by
        rw [carrier.nextCarrierComponent_boundary]
        change mapping.f (degree + 1) =
          ((simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
            carrier.carrierHomotopyComponent degree previousData.2.1) +
          (mapping.f (degree + 1) -
            (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
              carrier.carrierHomotopyComponent degree previousData.2.1)
        abel⟩)

noncomputable def globalCarrierHomotopyComponent
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) (degree : ℕ) :
    (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X degree ⟶ target.X (degree + 1) :=
  carrier.carrierHomotopyComponent degree
    (carrier.recursiveCarrierHomotopyValues carried augmentationZero degree).2.1

theorem globalCarrierHomotopyComponent_zero
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) :
    carrier.globalCarrierHomotopyComponent carried augmentationZero 0 ≫ target.d 1 0 = mapping.f 0 :=
  carrier.initialCarrierComponent_boundary carried augmentationZero

theorem globalCarrierHomotopyComponent_succ
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) (degree : ℕ) :
    mapping.f (degree + 1) =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
        carrier.globalCarrierHomotopyComponent carried augmentationZero degree +
      carrier.globalCarrierHomotopyComponent carried augmentationZero (degree + 1) ≫
        target.d (degree + 2) (degree + 1) :=
  (carrier.recursiveCarrierHomotopyValues carried augmentationZero (degree + 1)).2.2

noncomputable def carriedNullHomotopy
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) : Homotopy mapping 0 where
  hom degree component := if equality : degree + 1 = component then
    carrier.globalCarrierHomotopyComponent carried augmentationZero degree ≫
      eqToHom (congrArg target.X equality) else 0
  zero degree component unrelated := by
    rw [dite_eq_right]
    exact unrelated
  comm degree := by
    rw [HomologicalComplex.zero_f_apply, add_zero, Homotopy.prevD_chainComplex]
    cases degree with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, zero_add]
      simpa only [dite_true, eqToHom_refl, Category.comp_id] using
        (carrier.globalCarrierHomotopyComponent_zero carried augmentationZero).symm
    | succ degree =>
      rw [Homotopy.dNext_succ_chainComplex]
      simpa only [dite_true, eqToHom_refl, Category.comp_id] using
        carrier.globalCarrierHomotopyComponent_succ carried augmentationZero degree

variable {first second : simplicial.chainComplex (AddCommGrpCat.of ℤ) ⟶ target}

def subtractCarriedMaps (firstCarried : carrier.CarriedIntegralChainMap first)
    (secondCarried : carrier.CarriedIntegralChainMap second) :
    carrier.CarriedIntegralChainMap (first - second) where
  value degree simplex := firstCarried.value degree simplex - secondCarried.value degree simplex
  value_inclusion degree simplex := by
    rw [sub_comp, firstCarried.value_inclusion, secondCarried.value_inclusion,
      HomologicalComplex.sub_f_apply, comp_sub]

noncomputable def carriedMapsHomotopy (firstCarried : carrier.CarriedIntegralChainMap first)
    (secondCarried : carrier.CarriedIntegralChainMap second)
    (sameAugmentation : first.f 0 ≫ augmentation = second.f 0 ≫ augmentation) :
    Homotopy first second :=
  Homotopy.equivSubZero.symm
    (carrier.carriedNullHomotopy (carrier.subtractCarriedMaps firstCarried secondCarried) (by
      rw [HomologicalComplex.sub_f_apply, sub_comp, sameAugmentation, sub_self]))

def CarrierMapValues (degree : ℕ) :=
  ∀ simplex : simplicial _⦋degree⦌,
    AddCommGrpCat.of ℤ ⟶ (carrier.complex degree simplex).X degree

noncomputable def carrierMapComponent (degree : ℕ) (values : carrier.CarrierMapValues degree) :
    (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X degree ⟶ target.X degree :=
  Sigma.desc fun simplex => values simplex ≫ (carrier.inclusion degree simplex).f degree

theorem carrierMapComponent_generator (degree : ℕ) (values : carrier.CarrierMapValues degree)
    (simplex : simplicial _⦋degree⦌) :
    simplicial.ιChainComplex simplex ≫ carrier.carrierMapComponent degree values =
      values simplex ≫ (carrier.inclusion degree simplex).f degree :=
  Sigma.ι_comp_desc _ _

noncomputable def carrierMapBoundary (degree : ℕ) (values : carrier.CarrierMapValues degree)
    (simplex : simplicial _⦋degree + 1⦌) :
    AddCommGrpCat.of ℤ ⟶ (carrier.complex (degree + 1) simplex).X degree :=
  ∑ deleted : Fin (degree + 2), ((-1 : ℤ) ^ deleted.val) •
    (values (simplicial.δ deleted simplex) ≫ (carrier.faceMap degree deleted simplex).f degree)

theorem carrierMapBoundary_inclusion (degree : ℕ) (values : carrier.CarrierMapValues degree)
    (simplex : simplicial _⦋degree + 1⦌) :
    carrier.carrierMapBoundary degree values simplex ≫ (carrier.inclusion (degree + 1) simplex).f degree =
      simplicial.ιChainComplex simplex ≫
        (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
          carrier.carrierMapComponent degree values := by
  rw [carrierMapBoundary, sum_comp, ← Category.assoc, SSet.ιChainComplex_d, sum_comp]
  apply Finset.sum_congr rfl
  intro deleted _member
  rw [zsmul_comp, zsmul_comp, Category.assoc, ← HomologicalComplex.comp_f,
    carrier.faceMap_inclusion, carrierMapComponent_generator]

noncomputable def initialCarrierMapValues (vertices : carrier.CarrierMapValues 0)
    (compatible : ∀ simplex : simplicial _⦋1⦌,
      vertices (simplicial.δ 0 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 0 simplex)).f 0 ≫ augmentation =
      vertices (simplicial.δ 1 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 1 simplex)).f 0 ≫ augmentation) :
    carrier.CarrierMapValues 1 := fun simplex =>
  integerCycleLift _ (carrier.exact_zero 1 simplex) (carrier.carrierMapBoundary 0 vertices simplex) (by
    rw [← Category.assoc, carrierMapBoundary_inclusion, ← Category.assoc, SSet.ιChainComplex_d,
      Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
      neg_smul, one_smul, add_comp, neg_comp, carrierMapComponent_generator,
      carrierMapComponent_generator, add_comp]
    simp only [neg_comp, Category.assoc]
    rw [compatible, add_neg_cancel])

theorem initialCarrierMapComponent_boundary (vertices : carrier.CarrierMapValues 0)
    (compatible : ∀ simplex : simplicial _⦋1⦌,
      vertices (simplicial.δ 0 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 0 simplex)).f 0 ≫ augmentation =
      vertices (simplicial.δ 1 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 1 simplex)).f 0 ≫ augmentation) :
    carrier.carrierMapComponent 1 (carrier.initialCarrierMapValues vertices compatible) ≫ target.d 1 0 =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d 1 0 ≫ carrier.carrierMapComponent 0 vertices := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, carrierMapComponent_generator, Category.assoc,
    (carrier.inclusion 1 simplex).comm, ← Category.assoc, initialCarrierMapValues,
    integerCycleLift_comp, carrierMapBoundary_inclusion]

theorem carrierMapBoundary_closed (degree : ℕ) (previous : carrier.CarrierMapValues degree)
    (values : carrier.CarrierMapValues (degree + 1))
    (equation : carrier.carrierMapComponent (degree + 1) values ≫ target.d (degree + 1) degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
        carrier.carrierMapComponent degree previous)
    (simplex : simplicial _⦋degree + 2⦌) :
    carrier.carrierMapBoundary (degree + 1) values simplex ≫
      (carrier.complex (degree + 2) simplex).d (degree + 1) degree = 0 := by
  let := carrier.inclusion_mono (degree + 2) simplex degree
  apply (cancel_mono ((carrier.inclusion (degree + 2) simplex).f degree)).mp
  rw [zero_comp, Category.assoc, ← (carrier.inclusion (degree + 2) simplex).comm,
    ← Category.assoc, carrierMapBoundary_inclusion, Category.assoc, Category.assoc, equation,
    HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

noncomputable def nextCarrierMapValues (degree : ℕ) (previous : carrier.CarrierMapValues degree)
    (values : carrier.CarrierMapValues (degree + 1))
    (equation : carrier.carrierMapComponent (degree + 1) values ≫ target.d (degree + 1) degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
        carrier.carrierMapComponent degree previous) :
    carrier.CarrierMapValues (degree + 2) := fun simplex =>
  integerCycleLift ((carrier.complex (degree + 2) simplex).sc' (degree + 2) (degree + 1) degree)
    ((HomologicalComplex.exactAt_iff' _ (degree + 2) (degree + 1) degree
      (by simp) (by simp)).mp (carrier.exact_positive (degree + 2) simplex degree))
    (carrier.carrierMapBoundary (degree + 1) values simplex)
    (carrier.carrierMapBoundary_closed degree previous values equation simplex)

theorem nextCarrierMapComponent_boundary (degree : ℕ) (previous : carrier.CarrierMapValues degree)
    (values : carrier.CarrierMapValues (degree + 1))
    (equation : carrier.carrierMapComponent (degree + 1) values ≫ target.d (degree + 1) degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
        carrier.carrierMapComponent degree previous) :
    carrier.carrierMapComponent (degree + 2) (carrier.nextCarrierMapValues degree previous values equation) ≫
      target.d (degree + 2) (degree + 1) =
    (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 2) (degree + 1) ≫
      carrier.carrierMapComponent (degree + 1) values := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, carrierMapComponent_generator, Category.assoc,
    (carrier.inclusion (degree + 2) simplex).comm, ← Category.assoc]
  have filling := integerCycleLift_comp
    ((carrier.complex (degree + 2) simplex).sc' (degree + 2) (degree + 1) degree)
    ((HomologicalComplex.exactAt_iff' _ (degree + 2) (degree + 1) degree
      (by simp) (by simp)).mp (carrier.exact_positive (degree + 2) simplex degree))
    (carrier.carrierMapBoundary (degree + 1) values simplex)
    (carrier.carrierMapBoundary_closed degree previous values equation simplex)
  change carrier.nextCarrierMapValues degree previous values equation simplex ≫
    (carrier.complex (degree + 2) simplex).d (degree + 2) (degree + 1) =
      carrier.carrierMapBoundary (degree + 1) values simplex at filling
  rw [filling, carrierMapBoundary_inclusion]

noncomputable def recursiveCarrierMapValues (vertices : carrier.CarrierMapValues 0)
    (compatible : ∀ simplex : simplicial _⦋1⦌,
      vertices (simplicial.δ 0 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 0 simplex)).f 0 ≫ augmentation =
      vertices (simplicial.δ 1 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 1 simplex)).f 0 ≫ augmentation) :
    (degree : ℕ) → Σ' (previous : carrier.CarrierMapValues degree)
      (values : carrier.CarrierMapValues (degree + 1)),
      carrier.carrierMapComponent (degree + 1) values ≫ target.d (degree + 1) degree =
        (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
          carrier.carrierMapComponent degree previous :=
  Nat.rec ⟨vertices, carrier.initialCarrierMapValues vertices compatible,
    carrier.initialCarrierMapComponent_boundary vertices compatible⟩
    (fun degree previousData =>
      ⟨previousData.2.1, carrier.nextCarrierMapValues degree previousData.1 previousData.2.1 previousData.2.2,
        carrier.nextCarrierMapComponent_boundary degree previousData.1 previousData.2.1 previousData.2.2⟩)

noncomputable def extendCarriedVertexMap (vertices : carrier.CarrierMapValues 0)
    (compatible : ∀ simplex : simplicial _⦋1⦌,
      vertices (simplicial.δ 0 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 0 simplex)).f 0 ≫ augmentation =
      vertices (simplicial.δ 1 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 1 simplex)).f 0 ≫ augmentation) :
    simplicial.chainComplex (AddCommGrpCat.of ℤ) ⟶ target where
  f degree := carrier.carrierMapComponent degree
    (carrier.recursiveCarrierMapValues vertices compatible degree).1
  comm' degree component adjacent := by
    rcases adjacent with (rfl : component + 1 = degree)
    exact (carrier.recursiveCarrierMapValues vertices compatible component).2.2

noncomputable def extendCarriedVertexMap_carried (vertices : carrier.CarrierMapValues 0)
    (compatible : ∀ simplex : simplicial _⦋1⦌,
      vertices (simplicial.δ 0 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 0 simplex)).f 0 ≫ augmentation =
      vertices (simplicial.δ 1 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 1 simplex)).f 0 ≫ augmentation) :
    carrier.CarriedIntegralChainMap (carrier.extendCarriedVertexMap vertices compatible) where
  value degree := (carrier.recursiveCarrierMapValues vertices compatible degree).1
  value_inclusion degree simplex :=
    (carrier.carrierMapComponent_generator degree
      (carrier.recursiveCarrierMapValues vertices compatible degree).1 simplex).symm

end IntegralAcyclicCarrier

end AcyclicCarriers

section ActualFaceCarriers

variable {Ray : Type*} {Chart : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

theorem faceCarrierChainInclusion_mono (face : Finset Chart) (degree : ℕ) :
    Mono ((faceCarrierChainInclusion incidence negative face).f degree) := by
  let inclusion := faceCarrierSimplicialInclusion incidence negative face
  have componentMono (simplex : SimplexCategoryᵒᵖ) : Mono (inclusion.app simplex) := by
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro first second equality
    apply Subtype.ext
    have same := congrArg Subtype.val equality
    change first.val = second.val at same
    exact same
  let : Mono inclusion := NatTrans.mono_of_mono_app inclusion
  exact inferInstanceAs (Mono ((SSet.chainComplexMap (SSetPair.of inclusion).hom
    (AddCommGrpCat.of ℤ)).f degree))

theorem faceCarrierChainInclusion_augmentation (face : Finset Chart) :
    (faceCarrierChainInclusion incidence negative face).f 0 ≫ incidenceChainAugmentation incidence negative =
      incidenceChainAugmentation incidence (faceCarrierNegative incidence negative face) := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  change incidenceChainInclusion incidence (faceCarrierNegative incidence negative face) 0 tuple ≫
    ((faceCarrierChainInclusion incidence negative face).f 0 ≫ incidenceChainAugmentation incidence negative) =
    incidenceChainInclusion incidence (faceCarrierNegative incidence negative face) 0 tuple ≫
      incidenceChainAugmentation incidence (faceCarrierNegative incidence negative face)
  rw [← Category.assoc, faceCarrierChainInclusion_generator,
    incidenceChainAugmentation_generator, incidenceChainAugmentation_generator]

theorem faceCarrierChains_augmentedExact (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    (ShortComplex.mk
      ((incidenceChains incidence (faceCarrierNegative incidence negative face)).d 1 0)
      (incidenceChainAugmentation incidence (faceCarrierNegative incidence negative face))
      (incidenceChainAugmentation_zero incidence (faceCarrierNegative incidence negative face))).Exact := by
  obtain ⟨anchor, onFace⟩ := present.1
  exact incidenceConeChains_augmentedExact incidence (faceCarrierNegative incidence negative face) anchor
    (faceCarrier_isCone incidence negative face present anchor onFace)

theorem faceCarrierChains_exactAt_positive (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (degree : ℕ) :
    (incidenceChains incidence (faceCarrierNegative incidence negative face)).ExactAt (degree + 1) := by
  obtain ⟨anchor, onFace⟩ := present.1
  exact incidenceConeChains_exactAt_positive incidence (faceCarrierNegative incidence negative face) anchor
    (faceCarrier_isCone incidence negative face present anchor onFace) degree

noncomputable def reverseFaceCarrier
    (simplicial : SSet.{0})
    (shape : ∀ degree, simplicial _⦋degree⦌ → Finset Chart)
    (shape_face : ∀ degree deleted simplex,
      shape (degree + 1) simplex ⊆ shape degree
        (simplicial.δ deleted simplex))
    (shape_present : ∀ degree simplex, shape degree simplex ∈ negativeChartComplex incidence negative) :
    IntegralAcyclicCarrier simplicial
      (incidenceChains incidence negative) (incidenceChainAugmentation incidence negative) where
  complex degree simplex := incidenceChains incidence
    (faceCarrierNegative incidence negative (shape degree simplex))
  inclusion degree simplex := faceCarrierChainInclusion incidence negative (shape degree simplex)
  inclusion_mono degree simplex component :=
    faceCarrierChainInclusion_mono incidence negative (shape degree simplex) component
  faceMap degree deleted simplex := faceCarrierChainRefinement incidence negative
    (shape (degree + 1) simplex) (shape degree (simplicial.δ deleted simplex))
    (shape_face degree deleted simplex)
  faceMap_inclusion degree deleted simplex :=
    faceCarrierChainRefinement_inclusion incidence negative _ _ (shape_face degree deleted simplex)
  augmentation_zero degree simplex := by
    rw [faceCarrierChainInclusion_augmentation, incidenceChainAugmentation_zero]
  exact_zero degree simplex := by
    simpa only [faceCarrierChainInclusion_augmentation] using
      faceCarrierChains_augmentedExact incidence negative (shape degree simplex) (shape_present degree simplex)
  exact_positive degree simplex component :=
    faceCarrierChains_exactAt_positive incidence negative (shape degree simplex) (shape_present degree simplex) component

end ActualFaceCarriers

end BondalThomsen.ConvexNerveAcyclicCarrierAssembly
