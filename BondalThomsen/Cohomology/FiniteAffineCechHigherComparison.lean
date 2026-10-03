module

public import BondalThomsen.Cohomology.FiniteAffineCechCohomology
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open BondalThomsen.FiniteAffineCechCohomology
open BondalThomsen.FiniteQuasicoherentCohomologyTower
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace BondalThomsen.FiniteAffineCechHigherComparison

universe u

noncomputable section

variable {scheme : Scheme.{u}} {Index : Type u}

theorem productOpens_eq_iInf {Tuple : Type*} (opens : Tuple → scheme.Opens) :
    (∏ᶜ opens) = ⨅ index, opens index := by
  exact (IsLimit.conePointUniqueUpToIso
    (limit.isLimit (Discrete.functor opens)) (Preorder.isLimitIInf opens)).to_eq

def cechIntersection (opens : Index → scheme.Opens) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) : scheme.Opens :=
  ∏ᶜ (opens ∘ tuple)

theorem cechIntersection_isAffine [scheme.IsSeparated] (opens : Index → scheme.Opens)
    (affine : ∀ index, IsAffineOpen (opens index)) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) : IsAffineOpen (cechIntersection opens degree tuple) := by
  have intersection : cechIntersection opens degree tuple = ⨅ index, opens (tuple index) :=
    (IsLimit.conePointUniqueUpToIso
      (limit.isLimit (Discrete.functor (opens ∘ tuple)))
      (Preorder.isLimitIInf (opens ∘ tuple))).to_eq
  rw [intersection]
  exact IsAffineOpen.iInf (fun index => affine (tuple index))

def schemeCechComplexFunctor (opens : Index → scheme.Opens) :
    scheme.Modules ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  SheafOfModules.toSheaf scheme.ringCatSheaf ⋙ sheafToPresheaf _ _ ⋙ cechComplexFunctor opens

def schemeCechComplex (opens : Index → scheme.Opens) (coefficient : scheme.Modules) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (schemeCechComplexFunctor opens).obj coefficient

theorem schemeCechComplex_map_f (opens : Index → scheme.Opens)
    {first second : scheme.Modules} (coefficient_map : first ⟶ second) (degree : ℕ) :
    ((schemeCechComplexFunctor opens).map coefficient_map).f degree =
      Limits.Pi.map (fun tuple : Fin (degree + 1) → Index =>
        coefficient_map.app (cechIntersection opens degree tuple)) := rfl

theorem schemeCechComplex_d_zero_component (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (tuple : Fin 2 → Index) :
    (schemeCechComplex opens coefficient).d 0 1 ≫
        Limits.Pi.π (fun tuple : Fin 2 → Index =>
          coefficient.presheaf.obj (op (cechIntersection opens 1 tuple))) tuple =
      Limits.Pi.π (fun tuple : Fin 1 → Index =>
        coefficient.presheaf.obj (op (cechIntersection opens 0 tuple)))
          (tuple ∘ (0 : Fin 2).succAbove) ≫
        coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin 1 =>
          Limits.Pi.π (opens ∘ tuple) ((0 : Fin 2).succAbove index))).op -
      Limits.Pi.π (fun tuple : Fin 1 → Index =>
        coefficient.presheaf.obj (op (cechIntersection opens 0 tuple)))
          (tuple ∘ (1 : Fin 2).succAbove) ≫
        coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin 1 =>
          Limits.Pi.π (opens ∘ tuple) ((1 : Fin 2).succAbove index))).op := by
  change (AlgebraicTopology.AlternatingCofaceMapComplex.objD _ 0) ≫ _ = _
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  change (∑ face : Fin 2, (-1 : ℤ) ^ face.val •
    Limits.Pi.lift (fun tuple : Fin 2 → Index =>
      Limits.Pi.π (fun tuple : Fin 1 → Index =>
        coefficient.presheaf.obj (op (cechIntersection opens 0 tuple)))
          (tuple ∘ face.succAbove) ≫
        coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin 1 =>
          Limits.Pi.π (opens ∘ tuple) (face.succAbove index))).op)) ≫ _ = _
  change (∑ face : Fin 2, (-1 : ℤ) ^ face.val •
    Limits.Pi.lift (fun tuple : Fin 2 → Index =>
      Limits.Pi.π (fun tuple : Fin 1 → Index =>
        coefficient.presheaf.obj (op (∏ᶜ (opens ∘ tuple))))
          (tuple ∘ face.succAbove) ≫
        coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin 1 =>
          Limits.Pi.π (opens ∘ tuple) (face.succAbove index))).op)) ≫
      Limits.Pi.π (fun tuple : Fin 2 → Index =>
        coefficient.presheaf.obj (op (∏ᶜ (opens ∘ tuple)))) tuple = _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul,
    Preadditive.add_comp, Preadditive.neg_comp, sub_eq_add_neg, Limits.Pi.lift_comp_π]
  rfl

instance schemeCechComplexFunctor_additive (opens : Index → scheme.Opens) :
    (schemeCechComplexFunctor opens).Additive where
  map_add := by
    intro first second first_map second_map
    apply HomologicalComplex.Hom.ext
    funext degree
    simp only [schemeCechComplex_map_f, HomologicalComplex.add_f_apply]
    apply Limits.Pi.hom_ext _ _
    intro tuple
    simp

def openSectionsFunctor (open_set : scheme.Opens) : scheme.Modules ⥤ AddCommGrpCat.{u} :=
  (SheafOfModules.forget.{u} scheme.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf.{u} scheme.ringCatSheaf.obj) ⋙
    (evaluation _ AddCommGrpCat.{u}).obj (op open_set)

instance openSectionsFunctor_additive (open_set : scheme.Opens) :
    (openSectionsFunctor open_set).Additive where
  map_add := by intros; rfl

instance openSectionsFunctor_preservesFiniteLimits (open_set : scheme.Opens) :
    PreservesFiniteLimits (openSectionsFunctor open_set) := by
  dsimp [openSectionsFunctor]
  let : PreservesFiniteLimits (SheafOfModules.forget.{u} scheme.ringCatSheaf) := inferInstance
  let : PreservesFiniteLimits
      (PresheafOfModules.toPresheaf.{u} scheme.ringCatSheaf.obj) := inferInstance
  infer_instance

theorem affineOpenSections_shortExact {sequence : ShortComplex scheme.Modules}
    [sequence.X₁.IsQuasicoherent] [sequence.X₂.IsQuasicoherent] [sequence.X₃.IsQuasicoherent]
    (exact_sequence : sequence.ShortExact) (open_set : scheme.Opens)
    (affine : IsAffineOpen open_set) :
    (sequence.map (openSectionsFunctor open_set)).ShortExact := by
  let := exact_sequence.mono_f
  let := exact_sequence.epi_g
  let : Epi ((openSectionsFunctor open_set).map sequence.g) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (affineOpenSections_surjective sequence.g open_set affine)
  let : Mono ((openSectionsFunctor open_set).map sequence.f) := inferInstance
  exact
    { mono_f := inferInstanceAs (Mono ((openSectionsFunctor open_set).map sequence.f))
      epi_g := inferInstanceAs (Epi ((openSectionsFunctor open_set).map sequence.g))
      exact := exact_sequence.exact.map_of_mono_of_preservesKernel
        (openSectionsFunctor open_set) exact_sequence.mono_f inferInstance }

def productElementsEquiv {Tuple : Type u} (coefficient : Tuple → AddCommGrpCat.{u}) :
    (∏ᶜ coefficient : AddCommGrpCat.{u}) ≃+ (∀ index, coefficient index) :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor coefficient))
    (AddCommGrpCat.HasLimit.productLimitCone coefficient).isLimit).addCommGroupIsoToAddEquiv

theorem productElementsEquiv_apply {Tuple : Type u} (coefficient : Tuple → AddCommGrpCat.{u})
    (element : (∏ᶜ coefficient : AddCommGrpCat.{u})) (index : Tuple) :
    productElementsEquiv coefficient element index = Limits.Pi.π coefficient index element := by
  have projection := IsLimit.conePointUniqueUpToIso_hom_comp
    (limit.isLimit (Discrete.functor coefficient))
    (AddCommGrpCat.HasLimit.productLimitCone coefficient).isLimit (Discrete.mk index)
  exact (ConcreteCategory.congr_hom projection element).symm

theorem productElementsEquiv_map {Tuple : Type u} {first second : Tuple → AddCommGrpCat.{u}}
    (coefficient_map : ∀ index, first index ⟶ second index)
    (element : (∏ᶜ first : AddCommGrpCat.{u})) (index : Tuple) :
    productElementsEquiv second (Limits.Pi.map coefficient_map element) index =
      coefficient_map index (productElementsEquiv first element index) := by
  rw [productElementsEquiv_apply, productElementsEquiv_apply]
  exact ConcreteCategory.congr_hom (Limits.Pi.map_π coefficient_map index) element

def productShortComplex {Tuple : Type u} (sequence : Tuple → ShortComplex AddCommGrpCat.{u}) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (Limits.Pi.map (fun index => (sequence index).f))
    (Limits.Pi.map (fun index => (sequence index).g)) (by
      apply Limits.Pi.hom_ext _ _
      intro index
      simp [Category.assoc, (sequence index).zero])

theorem productShortComplex_shortExact {Tuple : Type u}
    (sequence : Tuple → ShortComplex AddCommGrpCat.{u})
    (exact_sequence : ∀ index, (sequence index).ShortExact) :
    (productShortComplex sequence).ShortExact := by
  classical
  let (index : Tuple) : Mono (sequence index).f := (exact_sequence index).mono_f
  let (index : Tuple) : Epi (sequence index).g := (exact_sequence index).epi_g
  have projection_surjective : Function.Surjective (productShortComplex sequence).g := by
    intro element
    choose preimage preimage_image using fun index =>
      (AddCommGrpCat.epi_iff_surjective (sequence index).g).mp inferInstance
        (productElementsEquiv (fun index => (sequence index).X₃) element index)
    refine ⟨(productElementsEquiv (fun index => (sequence index).X₂)).symm preimage, ?_⟩
    apply (productElementsEquiv (fun index => (sequence index).X₃)).injective
    funext index
    change productElementsEquiv (fun index => (sequence index).X₃)
      (Limits.Pi.map (fun index => (sequence index).g)
        ((productElementsEquiv (fun index => (sequence index).X₂)).symm preimage)) index = _
    rw [productElementsEquiv_map, AddEquiv.apply_symm_apply]
    exact preimage_image index
  have product_exact : (productShortComplex sequence).Exact := by
    apply (ShortComplex.ab_exact_iff _).mpr
    intro element zero_image
    have local_zero (index : Tuple) :
        (sequence index).g (productElementsEquiv (fun index => (sequence index).X₂)
          element index) = 0 := by
      have image := congrArg (fun local_element =>
        productElementsEquiv (fun index => (sequence index).X₃) local_element index) zero_image
      simpa only [productShortComplex, productElementsEquiv_map, map_zero, Pi.zero_apply] using image
    choose preimage preimage_image using fun index =>
      (ShortComplex.ab_exact_iff _).mp (exact_sequence index).exact
        (productElementsEquiv (fun index => (sequence index).X₂) element index) (local_zero index)
    refine ⟨(productElementsEquiv (fun index => (sequence index).X₁)).symm preimage, ?_⟩
    apply (productElementsEquiv (fun index => (sequence index).X₂)).injective
    funext index
    change productElementsEquiv (fun index => (sequence index).X₂)
      (Limits.Pi.map (fun index => (sequence index).f)
        ((productElementsEquiv (fun index => (sequence index).X₁)).symm preimage)) index = _
    rw [productElementsEquiv_map, AddEquiv.apply_symm_apply]
    exact preimage_image index
  exact
    { mono_f := inferInstanceAs (Mono (Limits.Pi.map (fun index => (sequence index).f)))
      epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr projection_surjective
      exact := product_exact }

theorem schemeCechComplex_degree_shortExact [scheme.IsSeparated]
    (opens : Index → scheme.Opens) (affine : ∀ index, IsAffineOpen (opens index))
    {sequence : ShortComplex scheme.Modules} [sequence.X₁.IsQuasicoherent]
    [sequence.X₂.IsQuasicoherent] [sequence.X₃.IsQuasicoherent]
    (exact_sequence : sequence.ShortExact) (degree : ℕ) :
    ((sequence.map (schemeCechComplexFunctor opens)).map
      (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℕ) degree)).ShortExact := by
  let local_sequence := fun tuple : Fin (degree + 1) → Index =>
    sequence.map (openSectionsFunctor (cechIntersection opens degree tuple))
  have local_exact : ∀ tuple, (local_sequence tuple).ShortExact := by
    intro tuple
    exact affineOpenSections_shortExact exact_sequence _
      (cechIntersection_isAffine opens affine degree tuple)
  exact productShortComplex_shortExact local_sequence local_exact

theorem schemeCechComplex_shortExact [scheme.IsSeparated]
    (opens : Index → scheme.Opens) (affine : ∀ index, IsAffineOpen (opens index))
    {sequence : ShortComplex scheme.Modules} [sequence.X₁.IsQuasicoherent]
    [sequence.X₂.IsQuasicoherent] [sequence.X₃.IsQuasicoherent]
    (exact_sequence : sequence.ShortExact) :
    (sequence.map (schemeCechComplexFunctor opens)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (schemeCechComplex_degree_shortExact opens affine exact_sequence)

def schemeCechBoundary [scheme.IsSeparated]
    (opens : Index → scheme.Opens) (affine : ∀ index, IsAffineOpen (opens index))
    {sequence : ShortComplex scheme.Modules} [sequence.X₁.IsQuasicoherent]
    [sequence.X₂.IsQuasicoherent] [sequence.X₃.IsQuasicoherent]
    (exact_sequence : sequence.ShortExact) (degree : ℕ) :
    (schemeCechComplex opens sequence.X₃).homology degree ⟶
      (schemeCechComplex opens sequence.X₁).homology (degree + 1) :=
  (schemeCechComplex_shortExact opens affine exact_sequence).δ degree (degree + 1) rfl

def schemeCechBoundaryIso [scheme.IsSeparated]
    (opens : Index → scheme.Opens) (affine : ∀ index, IsAffineOpen (opens index))
    {sequence : ShortComplex scheme.Modules} [sequence.X₁.IsQuasicoherent]
    [sequence.X₂.IsQuasicoherent] [sequence.X₃.IsQuasicoherent]
    (exact_sequence : sequence.ShortExact) (degree : ℕ)
    (acyclic_degree : IsZero ((schemeCechComplex opens sequence.X₂).homology degree))
    (acyclic_successor : IsZero
      ((schemeCechComplex opens sequence.X₂).homology (degree + 1))) :
    (schemeCechComplex opens sequence.X₃).homology degree ≅
      (schemeCechComplex opens sequence.X₁).homology (degree + 1) :=
  (schemeCechComplex_shortExact opens affine exact_sequence).δIso degree (degree + 1) rfl
    acyclic_degree acyclic_successor

end

end BondalThomsen.FiniteAffineCechHigherComparison

