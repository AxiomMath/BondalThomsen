module

public import BondalThomsen.Derived.InvertibleSheafExtCohomology
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.Flasque

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite

namespace BondalThomsen.SheafPositiveExtCohomology

universe u

noncomputable section

section Locality

variable {site : Type u} [SmallCategory site] {topology : GrothendieckTopology site}
  {ring_sheaf : Sheaf topology RingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
theorem hom_ext_of_coversTop {Index : Type u} {cover : Index → site}
    (covering : topology.CoversTop cover)
    {source target : SheafOfModules.{u} ring_sheaf} {first second : source ⟶ target}
    (locally_equal : ∀ index, first.over (cover index) = second.over (cover index)) :
    first = second := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro open_subset
  apply (forget₂ (ModuleCat _) AddCommGrpCat).map_injective
  apply target.isSheaf.hom_ext (covering.cover open_subset.unop)
  rintro ⟨domain, restriction, ⟨index, ⟨chart_map⟩⟩⟩
  have component := congrArg
    (fun morphism => morphism.val.app (op (Over.mk chart_map))) (locally_equal index)
  change first.val.app (op domain) = second.val.app (op domain) at component
  have first_naturality := ((SheafOfModules.toSheaf ring_sheaf).map first).hom.naturality
    restriction.op
  have second_naturality := ((SheafOfModules.toSheaf ring_sheaf).map second).hom.naturality
    restriction.op
  change ((SheafOfModules.toSheaf ring_sheaf).map first).hom.app open_subset ≫
      target.val.presheaf.map restriction.op =
    ((SheafOfModules.toSheaf ring_sheaf).map second).hom.app open_subset ≫
      target.val.presheaf.map restriction.op
  exact first_naturality.symm.trans ((congrArg
    (fun linear_map => source.val.presheaf.map restriction.op ≫
      (forget₂ (ModuleCat _) AddCommGrpCat).map linear_map) component).trans
        second_naturality)

theorem mono_of_coversTop {Index : Type u} {cover : Index → site}
    (covering : topology.CoversTop cover)
    {source target : SheafOfModules.{u} ring_sheaf} (morphism : source ⟶ target)
    (locally_mono : ∀ index, Mono (morphism.over (cover index))) : Mono morphism where
  right_cancellation first second equal := by
    apply hom_ext_of_coversTop covering
    intro index
    let := locally_mono index
    apply (cancel_mono (morphism.over (cover index))).mp
    exact (SheafOfModules.overFunctor ring_sheaf (cover index)).congr_map equal

theorem mono_over {source target : SheafOfModules.{u} ring_sheaf}
    (morphism : source ⟶ target) [Mono morphism] (chart : site) :
    Mono (morphism.over chart) := by
  let : Mono morphism.val :=
    inferInstanceAs (Mono ((SheafOfModules.forget ring_sheaf).map morphism))
  apply (SheafOfModules.forget (ring_sheaf.over chart)).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro open_subset
  exact PresheafOfModules.injective_of_mono morphism.val
    (op open_subset.unop.left)

end Locality

section TensorExactness

variable {site : Type u} [SmallCategory site] {topology : GrothendieckTopology site}
  [topology.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify topology AddCommGrpCat.{u}]
  [topology.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ chart : site, HasWeakSheafify (topology.over chart) AddCommGrpCat.{u}]
  [∀ chart : site, (topology.over chart).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {commutative_ring_sheaf : Sheaf topology CommRingCat.{u}}

local instance : MonoidalCategory
    (SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf commutative_ring_sheaf)) :=
  TauCeti.SheafOfModules.monoidalCategory commutative_ring_sheaf

local instance : MonoidalClosed
    (SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf commutative_ring_sheaf)) :=
  TauCeti.SheafOfModules.monoidalClosed commutative_ring_sheaf

local instance : MonoidalPreadditive
    (SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf commutative_ring_sheaf)) :=
  TauCeti.SheafOfModules.monoidalPreadditive commutative_ring_sheaf

set_option backward.isDefEq.respectTransparency false in
theorem invertible_tensorLeft_preservesMonomorphisms
    (line_bundle : SheafOfModules.{u}
      (TauCeti.SheafOfModules.ringCatSheaf commutative_ring_sheaf))
    [TauCeti.SheafOfModules.IsInvertible line_bundle] :
    (tensorLeft line_bundle).PreservesMonomorphisms where
  preserves {source target} morphism mono := by
    let := mono
    let atlas := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible line_bundle
    apply mono_of_coversTop atlas.coversTop
    intro index
    let chart := atlas.X index
    let : MonoidalCategory (SheafOfModules.{u}
        ((TauCeti.SheafOfModules.ringCatSheaf commutative_ring_sheaf).over chart)) :=
      TauCeti.SheafOfModules.monoidalCategory (commutative_ring_sheaf.over chart)
    let trivialization : line_bundle.over chart ≅ 𝟙_ _ :=
      (atlas.iso index).symm ≪≫
        TauCeti.SheafOfModules.freePUnitIsoUnit
          ((TauCeti.SheafOfModules.ringCatSheaf commutative_ring_sheaf).over chart)
    let := mono_over morphism chart
    let source_iso := SheafOfModules.overTensorIso
      (R := commutative_ring_sheaf) (X := chart) line_bundle source
    let target_iso := SheafOfModules.overTensorIso
      (R := commutative_ring_sheaf) (X := chart) line_bundle target
    have local_mono : Mono (line_bundle.over chart ◁ morphism.over chart) := by
      have naturality := (tensoringLeft _).mapIso trivialization |>.hom.naturality
        (morphism.over chart)
      change (line_bundle.over chart ◁ morphism.over chart) ≫
        ((tensoringLeft _).mapIso trivialization).hom.app _ =
        ((tensoringLeft _).mapIso trivialization).hom.app _ ≫
          (𝟙_ _ ◁ morphism.over chart) at naturality
      have unit_mono : Mono (𝟙_ _ ◁ morphism.over chart) := by
        have unit_naturality := (leftUnitorNatIso _).hom.naturality (morphism.over chart)
        change (𝟙_ _ ◁ morphism.over chart) ≫ (λ_ _).hom =
          (λ_ _).hom ≫ morphism.over chart at unit_naturality
        have : Mono ((𝟙_ _ ◁ morphism.over chart) ≫ (λ_ (target.over chart)).hom) := by
          rw [unit_naturality]
          infer_instance
        exact mono_of_mono (𝟙_ _ ◁ morphism.over chart) (λ_ (target.over chart)).hom
      let := unit_mono
      have : Mono ((line_bundle.over chart ◁ morphism.over chart) ≫
          ((tensoringLeft _).mapIso trivialization).hom.app _) := by
        rw [naturality]
        infer_instance
      exact mono_of_mono (line_bundle.over chart ◁ morphism.over chart)
        (((tensoringLeft _).mapIso trivialization).hom.app (target.over chart))
    have compatibility := Functor.OplaxMonoidal.δ_natural
      (SheafOfModules.overFunctor
        (TauCeti.SheafOfModules.ringCatSheaf commutative_ring_sheaf) chart)
      (𝟙 line_bundle) morphism
    rw [← SheafOfModules.overTensorIso_hom (R := commutative_ring_sheaf) (X := chart),
      ← SheafOfModules.overTensorIso_hom (R := commutative_ring_sheaf) (X := chart)]
      at compatibility
    rw [id_tensorHom] at compatibility
    have identity : (SheafOfModules.overFunctor
        (TauCeti.SheafOfModules.ringCatSheaf commutative_ring_sheaf) chart).map
          (𝟙 line_bundle) = 𝟙 (line_bundle.over chart) := CategoryTheory.Functor.map_id _ _
    rw [identity, id_tensorHom] at compatibility
    change source_iso.hom ≫ (line_bundle.over chart ◁ morphism.over chart) =
      ((tensorLeft line_bundle).map morphism).over chart ≫ target_iso.hom at compatibility
    let := local_mono
    have : Mono (((tensorLeft line_bundle).map morphism).over chart ≫ target_iso.hom) := by
      rw [← compatibility]
      infer_instance
    exact mono_of_mono (((tensorLeft line_bundle).map morphism).over chart) target_iso.hom

end TensorExactness

section SchemeExactness

variable {scheme : Scheme.{u}}

local instance : MonoidalPreadditive scheme.Modules :=
  TauCeti.SheafOfModules.monoidalPreadditive scheme.sheaf

instance invertibleSheaf_tensorLeft_preservesMonomorphisms
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    (tensorLeft line_bundle.obj).PreservesMonomorphisms :=
  invertible_tensorLeft_preservesMonomorphisms
    (commutative_ring_sheaf := scheme.sheaf) line_bundle.obj

instance invertibleSheaf_tensorLeft_preservesHomology
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    (tensorLeft line_bundle.obj).PreservesHomology :=
  CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance invertibleSheaf_tensorLeft_preservesFiniteLimits
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    PreservesFiniteLimits (tensorLeft line_bundle.obj) :=
  CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology _

instance invertibleSheaf_ihom_preservesInjectiveObjects
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    (ihom line_bundle.obj).PreservesInjectiveObjects :=
  CategoryTheory.Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ihom.adjunction line_bundle.obj)

end SchemeExactness

section InjectiveAcyclicity

variable {scheme : Scheme.{u}}

def freeOpenSheaf (open_subset : scheme.Opens) : scheme.Modules :=
  (PresheafOfModules.sheafification (𝟙 scheme.ringCatSheaf.obj)).obj
    ((PresheafOfModules.free scheme.ringCatSheaf.obj).obj (yoneda.obj open_subset))

def freeOpenHomEquiv (open_subset : scheme.Opens) (target : scheme.Modules) :
    (freeOpenSheaf open_subset ⟶ target) ≃ Γ(target, open_subset) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 scheme.ringCatSheaf.obj)).homEquiv _ _).trans
    PresheafOfModules.freeYonedaEquiv

theorem freeOpenMap_mono {first_open second_open : scheme.Opens}
    (inclusion : first_open ⟶ second_open) :
    Mono ((PresheafOfModules.sheafification (𝟙 scheme.ringCatSheaf.obj)).map
      ((PresheafOfModules.free scheme.ringCatSheaf.obj).map (yoneda.map inclusion))) := by
  have : Mono ((PresheafOfModules.free scheme.ringCatSheaf.obj).map
      (yoneda.map inclusion)) := by
    apply PresheafOfModules.mono_of_injective
    intro open_subset
    change Function.Injective (Finsupp.mapDomain (fun morphism => morphism ≫ inclusion))
    exact Finsupp.mapDomain_injective (fun first second _ => Subsingleton.elim first second)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem freeOpenHomEquiv_naturality {first_open second_open : scheme.Opens}
    (inclusion : first_open ⟶ second_open) (target : scheme.Modules)
    (morphism : freeOpenSheaf second_open ⟶ target) :
    freeOpenHomEquiv first_open target
      ((PresheafOfModules.sheafification (𝟙 scheme.ringCatSheaf.obj)).map
        ((PresheafOfModules.free scheme.ringCatSheaf.obj).map (yoneda.map inclusion)) ≫
          morphism) = target.presheaf.map inclusion.op
            (freeOpenHomEquiv second_open target morphism) := by
  unfold freeOpenHomEquiv
  dsimp only [Equiv.trans_apply]
  have sheaf_naturality :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 scheme.ringCatSheaf.obj)).homEquiv_naturality_left
      ((PresheafOfModules.free scheme.ringCatSheaf.obj).map (yoneda.map inclusion)) morphism
  refine (congrArg PresheafOfModules.freeYonedaEquiv sheaf_naturality).trans ?_
  unfold PresheafOfModules.freeYonedaEquiv
  dsimp only [Equiv.trans_apply]
  have free_naturality :=
    (PresheafOfModules.freeAdjunction scheme.ringCatSheaf.obj).homEquiv_naturality_left
      (yoneda.map inclusion)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 scheme.ringCatSheaf.obj)).homEquiv
        _ _ morphism)
  exact (congrArg yonedaEquiv free_naturality).trans
    (yonedaEquiv_naturality _ inclusion).symm

set_option backward.isDefEq.respectTransparency false in
instance injectiveSheaf_isFlasque (injective_sheaf : scheme.Modules)
    [Injective injective_sheaf] : injective_sheaf.presheaf.IsFlasque where
  epi {first_open second_open} restriction := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro section_value
    let local_morphism : freeOpenSheaf second_open.unop ⟶ injective_sheaf :=
      (freeOpenHomEquiv second_open.unop injective_sheaf).symm section_value
    let extension_map : freeOpenSheaf second_open.unop ⟶ freeOpenSheaf first_open.unop :=
      (PresheafOfModules.sheafification (𝟙 scheme.ringCatSheaf.obj)).map
      ((PresheafOfModules.free scheme.ringCatSheaf.obj).map (yoneda.map restriction.unop))
    let : Mono extension_map := freeOpenMap_mono restriction.unop
    obtain ⟨extension, factors⟩ := Injective.factors local_morphism extension_map
    refine ⟨freeOpenHomEquiv first_open.unop injective_sheaf extension, ?_⟩
    exact (freeOpenHomEquiv_naturality restriction.unop injective_sheaf extension).symm.trans
      ((congrArg (freeOpenHomEquiv second_open.unop injective_sheaf) factors).trans
        (Equiv.apply_symm_apply _ _))

end InjectiveAcyclicity

end

end BondalThomsen.SheafPositiveExtCohomology
