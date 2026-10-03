module

public import BondalThomsen.Cohomology.FiniteQuasicoherentCohomologyTower
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.ModuleCat.Injective

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite
open BondalThomsen.FiniteQuasicoherentCohomologyTower

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.QuasicoherentFlasqueTowerConstruction

universe u

noncomputable section

variable {scheme : Scheme.{u}} {Index : Type u}

theorem specCokernel_isQuasicoherent {ring : CommRingCat.{u}}
    {first second : (Spec ring).Modules} [first.IsQuasicoherent] [second.IsQuasicoherent]
    (coefficient_map : first ⟶ second) : (cokernel coefficient_map).IsQuasicoherent := by
  let first_iso := asIso first.fromTildeΓ
  let second_iso := asIso second.fromTildeΓ
  let comparison := (PreservesCokernel.iso (tilde.functor ring)
    (moduleSpecΓFunctor.map coefficient_map)) ≪≫
    cokernel.mapIso ((tilde.functor ring).map (moduleSpecΓFunctor.map coefficient_map))
      coefficient_map first_iso second_iso
      (Scheme.Modules.fromTildeΓNatTrans.naturality coefficient_map)
  exact (SheafOfModules.isQuasicoherent.{u} (Spec ring).ringCatSheaf).prop_of_iso
    comparison inferInstance

theorem cokernel_isQuasicoherent {first second : scheme.Modules}
    [first.IsQuasicoherent] [second.IsQuasicoherent] (coefficient_map : first ⟶ second) :
    (cokernel coefficient_map).IsQuasicoherent := by
  let cover := scheme.affineCover
  let (index : cover.I₀) : ((cokernel coefficient_map).restrict (cover.f index)).IsQuasicoherent := by
    let restriction := Scheme.Modules.restrictFunctor (cover.f index)
    let local_map := restriction.map coefficient_map
    let := specCokernel_isQuasicoherent local_map
    exact (SheafOfModules.isQuasicoherent.{u} (cover.X index).ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso restriction coefficient_map).symm inferInstance
  exact FiniteQuasicoherentPushforward.isQuasicoherent_of_openCover cover _

theorem specFiniteProduct_isQuasicoherent {ring : CommRingCat.{u}} [Finite Index]
    (coefficient : Index → (Spec ring).Modules) [∀ index, (coefficient index).IsQuasicoherent] :
    (∏ᶜ coefficient).IsQuasicoherent := by
  let : Fintype Index := Fintype.ofFinite Index
  let comparison := (asIso (piComparison (tilde.functor ring)
      (fun index => moduleSpecΓFunctor.obj (coefficient index)))) ≪≫
    Pi.mapIso (fun index => asIso (coefficient index).fromTildeΓ)
  exact (SheafOfModules.isQuasicoherent.{u} (Spec ring).ringCatSheaf).prop_of_iso
    comparison inferInstance

theorem finiteProduct_isQuasicoherent [Finite Index] (coefficient : Index → scheme.Modules)
    [∀ index, (coefficient index).IsQuasicoherent] : (∏ᶜ coefficient).IsQuasicoherent := by
  let : Fintype Index := Fintype.ofFinite Index
  let cover := scheme.affineCover
  let (chart : cover.I₀) : ((∏ᶜ coefficient).restrict (cover.f chart)).IsQuasicoherent := by
    let restriction := Scheme.Modules.restrictFunctor (cover.f chart)
    let : restriction.Additive := ⟨by intros; rfl⟩
    let := specFiniteProduct_isQuasicoherent (fun index => restriction.obj (coefficient index))
    exact (SheafOfModules.isQuasicoherent.{u} (cover.X chart).ringCatSheaf).prop_of_iso
      (asIso (piComparison restriction coefficient)).symm inferInstance
  exact FiniteQuasicoherentPushforward.isQuasicoherent_of_openCover cover _

theorem finiteProduct_isFlasque [Finite Index] (coefficient : Index → scheme.Modules)
    [∀ index, (coefficient index).presheaf.IsFlasque] :
    (∏ᶜ coefficient).presheaf.IsFlasque := by
  let : Fintype Index := Fintype.ofFinite Index
  constructor
  intro first_open second_open restriction
  let first_evaluation := Scheme.Modules.toPresheaf scheme ⋙
    (evaluation _ _).obj first_open
  let second_evaluation := Scheme.Modules.toPresheaf scheme ⋙
    (evaluation _ _).obj second_open
  let : first_evaluation.Additive := ⟨by intros; rfl⟩
  let : second_evaluation.Additive := ⟨by intros; rfl⟩
  let restriction_map : first_evaluation ⟶ second_evaluation :=
    Functor.whiskerLeft (Scheme.Modules.toPresheaf scheme)
      ((evaluation _ _).map restriction)
  let product_map : (∏ᶜ fun index => first_evaluation.obj (coefficient index)) ⟶
      (∏ᶜ fun index => second_evaluation.obj (coefficient index)) :=
    Limits.Pi.map (fun index => (coefficient index).presheaf.map restriction)
  let (index : Index) : Epi ((coefficient index).presheaf.map restriction) := inferInstance
  let : Epi product_map := Limits.Pi.map_epi _
  have comparison_eq : (∏ᶜ coefficient).presheaf.map restriction ≫
      piComparison second_evaluation coefficient =
    piComparison first_evaluation coefficient ≫ product_map := by
    apply Limits.Pi.hom_ext
    intro index
    dsimp only [product_map]
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π]
    rw [← Category.assoc, piComparison_comp_π]
    exact (restriction_map.naturality (Pi.π coefficient index)).symm
  let : Epi ((∏ᶜ coefficient).presheaf.map restriction ≫
      piComparison second_evaluation coefficient) := by
    rw [comparison_eq]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (piComparison second_evaluation coefficient)).mp
    (inferInstanceAs (Epi ((∏ᶜ coefficient).presheaf.map restriction ≫
      piComparison second_evaluation coefficient)))

structure LocalFlasqueEmbedding (cover : Scheme.OpenCover.{u} scheme)
    (coefficient : scheme.Modules) where
  sheaf : ∀ index : cover.I₀, (cover.X index).Modules
  quasicoherent : ∀ index, (sheaf index).IsQuasicoherent
  flasque : ∀ index, (sheaf index).presheaf.IsFlasque
  local_inclusion : ∀ index, coefficient.restrict (cover.f index) ⟶ sheaf index
  mono : ∀ index, Mono (local_inclusion index)

namespace LocalFlasqueEmbedding

variable {cover : Scheme.OpenCover.{u} scheme} {coefficient : scheme.Modules}

def pushedSheaf (local_data : LocalFlasqueEmbedding cover coefficient) (index : cover.I₀) :
    scheme.Modules :=
  (Scheme.Modules.pushforward (cover.f index)).obj (local_data.sheaf index)

def middle (local_data : LocalFlasqueEmbedding cover coefficient) : scheme.Modules :=
  ∏ᶜ local_data.pushedSheaf

def component (local_data : LocalFlasqueEmbedding cover coefficient) (index : cover.I₀) :
    coefficient ⟶ local_data.pushedSheaf index :=
  (Scheme.Modules.restrictAdjunction (cover.f index)).homEquiv _ _ (local_data.local_inclusion index)

def inclusion (local_data : LocalFlasqueEmbedding cover coefficient) :
    coefficient ⟶ local_data.middle :=
  Limits.Pi.lift local_data.component

theorem inclusion_mono (local_data : LocalFlasqueEmbedding cover coefficient) :
    Mono local_data.inclusion := by
  constructor
  intro third first_map second_map equality
  apply FiniteQuasicoherentPushforward.hom_ext_of_openCover cover
  intro index
  let adjunction := Scheme.Modules.restrictAdjunction (cover.f index)
  let := local_data.mono index
  apply (cancel_mono (local_data.local_inclusion index)).mp
  have component_eq : first_map ≫ local_data.component index =
      second_map ≫ local_data.component index := by
    have projected := equality =≫ Limits.Pi.π local_data.pushedSheaf index
    dsimp only [inclusion] at projected
    simp only [Category.assoc] at projected
    have projection_formula : Limits.Pi.lift local_data.component ≫
        Limits.Pi.π local_data.pushedSheaf index = local_data.component index :=
      Limits.Pi.lift_comp_π local_data.component index
    exact (congrArg (fun arrow => first_map ≫ arrow) projection_formula).symm.trans
      (projected.trans (congrArg (fun arrow => second_map ≫ arrow) projection_formula))
  have local_eq := congrArg (adjunction.homEquiv _ (local_data.sheaf index)).symm component_eq
  simpa only [adjunction, Adjunction.homEquiv_naturality_left_symm, component,
    Equiv.symm_apply_apply] using local_eq

theorem middle_isQuasicoherent [Finite cover.I₀]
    [∀ index, IsAffineHom (cover.f index)]
    (local_data : LocalFlasqueEmbedding cover coefficient) :
    local_data.middle.IsQuasicoherent := by
  let (index : cover.I₀) : (local_data.sheaf index).IsQuasicoherent :=
    local_data.quasicoherent index
  let (index : cover.I₀) : (local_data.pushedSheaf index).IsQuasicoherent :=
    FiniteQuasicoherentPushforward.affinePushforward_isQuasicoherent _ _
  exact finiteProduct_isQuasicoherent local_data.pushedSheaf

theorem middle_isFlasque [Finite cover.I₀]
    (local_data : LocalFlasqueEmbedding cover coefficient) :
    local_data.middle.presheaf.IsFlasque := by
  let (index : cover.I₀) : (local_data.sheaf index).presheaf.IsFlasque := local_data.flasque index
  let (index : cover.I₀) : (local_data.pushedSheaf index).presheaf.IsFlasque :=
    ToricMultiplicationCohomologyTransport.pushforward_isFlasque _ _
  exact finiteProduct_isFlasque local_data.pushedSheaf

theorem cokernel_isQuasicoherent [Finite cover.I₀]
    [∀ index, IsAffineHom (cover.f index)] [coefficient.IsQuasicoherent]
    (local_data : LocalFlasqueEmbedding cover coefficient) :
    (cokernel local_data.inclusion).IsQuasicoherent := by
  let := local_data.middle_isQuasicoherent
  exact BondalThomsen.QuasicoherentFlasqueTowerConstruction.cokernel_isQuasicoherent _

def resolutionStep [Finite cover.I₀] [∀ index, IsAffineHom (cover.f index)]
    [coefficient.IsQuasicoherent] (local_data : LocalFlasqueEmbedding cover coefficient) :
    QuasicoherentResolutionStep coefficient where
  middle := local_data.middle
  next := cokernel local_data.inclusion
  middle_quasicoherent := local_data.middle_isQuasicoherent
  next_quasicoherent := local_data.cokernel_isQuasicoherent
  inclusion := local_data.inclusion
  projection := cokernel.π local_data.inclusion
  zero := cokernel.condition local_data.inclusion
  shortExact := by
    let := local_data.inclusion_mono
    have exactness := ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk local_data.inclusion (cokernel.π local_data.inclusion)
        (cokernel.condition local_data.inclusion)) (cokernelIsCokernel _)
    exact { exact := exactness }

theorem resolutionStep_middle_isFlasque [Finite cover.I₀]
    [∀ index, IsAffineHom (cover.f index)] [coefficient.IsQuasicoherent]
    (local_data : LocalFlasqueEmbedding cover coefficient) :
    local_data.resolutionStep.middle.presheaf.IsFlasque := local_data.middle_isFlasque

end LocalFlasqueEmbedding

def flasqueResolutionTower (cover : Scheme.OpenCover.{u} scheme) [Finite cover.I₀]
    [∀ index, IsAffineHom (cover.f index)] (coefficient : scheme.Modules)
    [quasicoherent : coefficient.IsQuasicoherent]
    (local_extension : ∀ current : scheme.Modules, current.IsQuasicoherent →
      LocalFlasqueEmbedding cover current) : QuasicoherentResolutionTower coefficient :=
  QuasicoherentResolutionTower.ofSteps quasicoherent (fun current current_quasicoherent =>
    letI := current_quasicoherent
    (local_extension current current_quasicoherent).resolutionStep)

theorem flasqueResolutionTower_middle_isFlasque (cover : Scheme.OpenCover.{u} scheme)
    [Finite cover.I₀] [∀ index, IsAffineHom (cover.f index)] (coefficient : scheme.Modules)
    [quasicoherent : coefficient.IsQuasicoherent]
    (local_extension : ∀ current : scheme.Modules, current.IsQuasicoherent →
      LocalFlasqueEmbedding cover current) (stage : ℕ) :
    ((flasqueResolutionTower cover coefficient local_extension).middle stage).presheaf.IsFlasque := by
  let extension := fun (current : scheme.Modules)
      (current_quasicoherent : current.IsQuasicoherent) =>
    letI := current_quasicoherent
    (local_extension current current_quasicoherent).resolutionStep
  let current := QuasicoherentResolutionTower.successiveCoefficient quasicoherent extension stage
  let := current.property
  exact (local_extension current.val current.property).resolutionStep_middle_isFlasque

theorem flasqueResolutionTower_acyclicFor (cover : Scheme.OpenCover.{u} scheme)
    [Finite cover.I₀] [∀ index, IsAffineHom (cover.f index)] (coefficient : scheme.Modules)
    [coefficient.IsQuasicoherent]
    (local_extension : ∀ current : scheme.Modules, current.IsQuasicoherent →
      LocalFlasqueEmbedding cover current) {target : Scheme.{u}} (morphism : scheme ⟶ target) :
    (flasqueResolutionTower cover coefficient local_extension).AcyclicFor morphism := by
  let (stage : ℕ) := flasqueResolutionTower_middle_isFlasque cover coefficient local_extension stage
  exact QuasicoherentResolutionTower.acyclicFor_of_isFlasque _ morphism

theorem affineSource_isAffineHom {source : Scheme.{u}} [IsAffine source]
    [scheme.IsSeparated] (open_map : source ⟶ scheme) : IsAffineHom open_map := by
  let : IsAffineHom (open_map ≫ terminal.from scheme) := by
    rw [terminal.comp_from]
    infer_instance
  exact IsAffineHom.of_comp open_map (terminal.from scheme)

structure AffineInjectiveFlasqueEmbedding (ring : CommRingCat.{u})
    (coefficient : (Spec ring).Modules) where
  module : ModuleCat ring
  injective : CategoryTheory.Injective module
  flasque : (tilde module).presheaf.IsFlasque
  inclusion : coefficient ⟶ tilde module
  mono : Mono inclusion

def localFlasqueEmbeddingOfAffineModules (cover : Scheme.AffineOpenCover.{u} scheme)
    (coefficient : scheme.Modules)
    (local_data : ∀ index : cover.I₀, AffineInjectiveFlasqueEmbedding (cover.X index)
      (coefficient.restrict (cover.f index))) :
    LocalFlasqueEmbedding cover.openCover coefficient where
  sheaf index := tilde (local_data index).module
  quasicoherent index := inferInstanceAs
    (SheafOfModules.IsQuasicoherent.{u} (tilde (local_data index).module))
  flasque index := (local_data index).flasque
  local_inclusion index := (local_data index).inclusion
  mono index := (local_data index).mono

def flasqueResolutionTowerOfAffineModules [scheme.IsSeparated]
    (cover : Scheme.AffineOpenCover.{u} scheme) [Finite cover.I₀]
    (coefficient : scheme.Modules) [coefficient.IsQuasicoherent]
    (local_extension : ∀ current : scheme.Modules, current.IsQuasicoherent →
      ∀ index : cover.I₀, AffineInjectiveFlasqueEmbedding (cover.X index)
        (current.restrict (cover.f index))) : QuasicoherentResolutionTower coefficient := by
  letI : Finite cover.openCover.I₀ := inferInstanceAs (Finite cover.I₀)
  letI (index : cover.openCover.I₀) : IsAffineHom (cover.openCover.f index) :=
    affineSource_isAffineHom _
  exact flasqueResolutionTower cover.openCover coefficient (fun current quasicoherent =>
    localFlasqueEmbeddingOfAffineModules cover current (local_extension current quasicoherent))

end

end BondalThomsen.QuasicoherentFlasqueTowerConstruction

namespace TauCeti.Toric.Fan

open BondalThomsen.QuasicoherentFlasqueTowerConstruction

variable {Lattice : Type} {Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def toricQuasicoherentFlasqueResolutionTower (fan : Fan embedding)
    (regular : fan.IsRegular) (coefficient : (fan.algebraicRealization 𝕜 regular).Modules)
    [coefficient.IsQuasicoherent]
    (local_extension : ∀ current : (fan.algebraicRealization 𝕜 regular).Modules,
      current.IsQuasicoherent → LocalFlasqueEmbedding (fan.toricChartOpenCover 𝕜 regular) current) :
    QuasicoherentResolutionTower coefficient := by
  letI := fan.algebraicRealization_isSeparated 𝕜 regular
  letI : Finite (fan.toricChartOpenCover 𝕜 regular).I₀ := inferInstanceAs (Finite fan.cones)
  letI (cone : (fan.toricChartOpenCover 𝕜 regular).I₀) :
      IsAffine ((fan.toricChartOpenCover 𝕜 regular).X cone) :=
    inferInstanceAs (IsAffine (fan.affineToricChart 𝕜 cone))
  letI (cone : (fan.toricChartOpenCover 𝕜 regular).I₀) :
      IsAffineHom ((fan.toricChartOpenCover 𝕜 regular).f cone) := affineSource_isAffineHom _
  exact flasqueResolutionTower (fan.toricChartOpenCover 𝕜 regular) coefficient local_extension

theorem toricQuasicoherentFlasqueResolutionTower_acyclicFor (fan : Fan embedding)
    (regular : fan.IsRegular) (coefficient : (fan.algebraicRealization 𝕜 regular).Modules)
    [coefficient.IsQuasicoherent]
    (local_extension : ∀ current : (fan.algebraicRealization 𝕜 regular).Modules,
      current.IsQuasicoherent → LocalFlasqueEmbedding (fan.toricChartOpenCover 𝕜 regular) current)
    {target : Scheme} (morphism : fan.algebraicRealization 𝕜 regular ⟶ target) :
    (fan.toricQuasicoherentFlasqueResolutionTower 𝕜 regular coefficient local_extension).AcyclicFor
      morphism := by
  let := fan.algebraicRealization_isSeparated 𝕜 regular
  let : Finite (fan.toricChartOpenCover 𝕜 regular).I₀ := inferInstanceAs (Finite fan.cones)
  let (cone : (fan.toricChartOpenCover 𝕜 regular).I₀) :
      IsAffine ((fan.toricChartOpenCover 𝕜 regular).X cone) :=
    inferInstanceAs (IsAffine (fan.affineToricChart 𝕜 cone))
  let (cone : (fan.toricChartOpenCover 𝕜 regular).I₀) :
      IsAffineHom ((fan.toricChartOpenCover 𝕜 regular).f cone) := affineSource_isAffineHom _
  exact flasqueResolutionTower_acyclicFor (fan.toricChartOpenCover 𝕜 regular) coefficient
    local_extension morphism

end TauCeti.Toric.Fan
