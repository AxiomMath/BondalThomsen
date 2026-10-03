module

public import BondalThomsen.Derived.LineBundleCollectionOrder
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Germ
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.RationalTrivialization

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace BondalThomsen

universe u

variable {scheme : Scheme.{u}} [IsIntegral scheme]

theorem invertibleSheaf_hom_over_injective
    (source : scheme.Modules) (target : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (generic_open : scheme.Opens) [Nonempty generic_open] :
    Function.Injective (fun morphism : source ⟶ target.obj => morphism.over generic_open) := by
  intro first second same_restriction
  apply Scheme.Modules.hom_ext
  intro domain
  ext section_value
  by_cases inhabited : Nonempty domain
  · let := inhabited
    let common := domain ⊓ generic_open
    have : Nonempty common := ⟨⟨genericPoint scheme,
      TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem domain,
      TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem generic_open⟩⟩
    let inclusion : common ⟶ domain := homOfLE inf_le_left
    apply target.map_injective_of_isIntegral inclusion
    have first_natural := first.mapPresheaf.naturality_apply inclusion.op section_value
    have second_natural := second.mapPresheaf.naturality_apply inclusion.op section_value
    simp only [Scheme.Modules.mapPresheaf_app, unop_op] at first_natural second_natural
    rw [← first_natural, ← second_natural]
    have same_component := congrArg
      (fun morphism => morphism.val.app (op (Over.mk
        (homOfLE (inf_le_right : common ≤ generic_open))))) same_restriction
    exact congrArg (fun morphism => morphism (source.presheaf.map inclusion.op section_value))
      same_component
  · apply TopCat.Presheaf.section_ext
      (⟨target.obj.presheaf, target.obj.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat scheme)
    intro point membership
    exact (inhabited ⟨⟨point, membership⟩⟩).elim

theorem invertibleSheaf_hom_eq_zero_of_generator_image_eq_zero
    (source target : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    {generic_open : scheme.Opens} [Nonempty generic_open]
    (trivialization : SheafOfModules.free (R := scheme.ringCatSheaf.over generic_open) PUnit ≅
      source.obj.over generic_open)
    (morphism : source.obj ⟶ target.obj)
    (basis_image_zero : morphism.app generic_open
      (Scheme.Modules.trivializationGenerator source.obj trivialization) = 0) :
    morphism = 0 := by
  apply invertibleSheaf_hom_over_injective source.obj target generic_open
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro domain
  ext section_value
  let inclusion := domain.unop.hom
  have natural := morphism.mapPresheaf.naturality_apply inclusion.op
    (Scheme.Modules.trivializationGenerator source.obj trivialization)
  simp only [Scheme.Modules.mapPresheaf_app, unop_op, basis_image_zero, map_zero] at natural
  have normal_form := Scheme.Modules.eq_trivializationCoordinate_smul_map_trivializationGenerator
    source.obj trivialization inclusion section_value
  change morphism.app domain.unop.left section_value = 0
  rw [normal_form, Scheme.Modules.Hom.app_smul, natural, smul_zero]

theorem invertibleSheaf_hom_restricted_generator_image_ne_zero
    (source target : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    {trivializing_open generic_open : scheme.Opens} [Nonempty generic_open]
    (trivialization : SheafOfModules.free (R := scheme.ringCatSheaf.over trivializing_open)
      PUnit ≅ source.obj.over trivializing_open)
    (inclusion : generic_open ⟶ trivializing_open)
    (morphism : source.obj ⟶ target.obj) (nonzero : morphism ≠ 0) :
    morphism.app generic_open (source.obj.presheaf.map inclusion.op
      (Scheme.Modules.trivializationGenerator source.obj trivialization)) ≠ 0 := by
  have : Nonempty trivializing_open := ⟨⟨genericPoint scheme,
    inclusion.le (TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem generic_open)⟩⟩
  intro image_zero
  apply nonzero
  apply invertibleSheaf_hom_eq_zero_of_generator_image_eq_zero source target trivialization
  apply target.map_injective_of_isIntegral inclusion
  have natural := morphism.mapPresheaf.naturality_apply inclusion.op
    (Scheme.Modules.trivializationGenerator source.obj trivialization)
  simp only [Scheme.Modules.mapPresheaf_app, unop_op, image_zero, map_zero] at natural ⊢
  exact natural.symm

theorem invertibleSheaf_comp_ne_zero_of_isIntegral
    (source middle target : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (first : source.obj ⟶ middle.obj) (second : middle.obj ⟶ target.obj)
    (first_nonzero : first ≠ 0) (second_nonzero : second ≠ 0) : first ≫ second ≠ 0 := by
  obtain ⟨source_open, source_trivialization, source_generic⟩ :=
    Scheme.Modules.exists_mem_trivialization source.obj (genericPoint scheme)
  obtain ⟨middle_open, middle_trivialization, middle_generic⟩ :=
    Scheme.Modules.exists_mem_trivialization middle.obj (genericPoint scheme)
  obtain ⟨target_open, target_trivialization, target_generic⟩ :=
    Scheme.Modules.exists_mem_trivialization target.obj (genericPoint scheme)
  let common := (source_open ⊓ middle_open) ⊓ target_open
  have : Nonempty common := ⟨⟨genericPoint scheme,
    ⟨⟨source_generic, middle_generic⟩, target_generic⟩⟩⟩
  have : IsDomain Γ(scheme, common) := IsIntegral.component_integral common
  let source_inclusion : common ⟶ source_open := homOfLE (inf_le_left.trans inf_le_left)
  let middle_inclusion : common ⟶ middle_open := homOfLE (inf_le_left.trans inf_le_right)
  let target_inclusion : common ⟶ target_open := homOfLE inf_le_right
  let source_basis := source.obj.presheaf.map source_inclusion.op
    (Scheme.Modules.trivializationGenerator source.obj source_trivialization)
  let middle_basis := middle.obj.presheaf.map middle_inclusion.op
    (Scheme.Modules.trivializationGenerator middle.obj middle_trivialization)
  let first_scalar := Scheme.Modules.trivializationCoordinate middle.obj middle_trivialization
    middle_inclusion (first.app common source_basis)
  have first_image_nonzero : first.app common source_basis ≠ 0 :=
    invertibleSheaf_hom_restricted_generator_image_ne_zero source middle source_trivialization
      source_inclusion first first_nonzero
  have second_image_nonzero : second.app common middle_basis ≠ 0 :=
    invertibleSheaf_hom_restricted_generator_image_ne_zero middle target middle_trivialization
      middle_inclusion second second_nonzero
  have first_normal : first.app common source_basis = first_scalar • middle_basis :=
    Scheme.Modules.eq_trivializationCoordinate_smul_map_trivializationGenerator middle.obj
      middle_trivialization middle_inclusion (first.app common source_basis)
  have first_scalar_nonzero : first_scalar ≠ 0 := by
    intro scalar_zero
    apply first_image_nonzero
    rw [first_normal, scalar_zero, zero_smul]
  have second_scalar_nonzero : Scheme.Modules.trivializationCoordinate target.obj
      target_trivialization target_inclusion (second.app common middle_basis) ≠ 0 := by
    intro scalar_zero
    apply second_image_nonzero
    apply (Scheme.Modules.trivializationCoordinate target.obj target_trivialization
      target_inclusion).injective
    simpa only [map_zero] using scalar_zero
  intro composite_zero
  have composite_image_zero := congrArg (fun morphism => morphism.app common source_basis)
    composite_zero
  change second.app common (first.app common source_basis) = 0 at composite_image_zero
  rw [first_normal, Scheme.Modules.Hom.app_smul] at composite_image_zero
  have scalar_product_zero := congrArg (Scheme.Modules.trivializationCoordinate target.obj
    target_trivialization target_inclusion) composite_image_zero
  simp only [map_smul, smul_eq_mul, map_zero] at scalar_product_zero
  exact mul_ne_zero first_scalar_nonzero second_scalar_nonzero scalar_product_zero

theorem exists_invertibleSheafExt_ordering_of_isIntegral
    {BaseField : Type*} [Field BaseField] {Index : Type*} [Fintype Index]
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (pairwise_nonisomorphic : ∀ {first second : Index},
      Nonempty ((line_bundles first).obj ≅ (line_bundles second).obj) → first = second)
    (positive_vanishing : ∀ source target degree, 0 < degree →
      Subsingleton (Abelian.Ext (line_bundles source).obj (line_bundles target).obj degree)) :
    ∃ numbering : Index ≃ Fin (Fintype.card Index),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Abelian.Ext (line_bundles source).obj
          (line_bundles target).obj degree), extension = 0 :=
  exists_invertibleSheafExt_ordering_of_globalFunctions global_functions line_bundles
    (fun {source middle target} first second first_nonzero second_nonzero =>
      invertibleSheaf_comp_ne_zero_of_isIntegral (line_bundles source) (line_bundles middle)
        (line_bundles target) first second first_nonzero second_nonzero)
    pairwise_nonisomorphic positive_vanishing

theorem invertibleSheaf_nonzeroHom_isPartialOrder_of_isIntegral
    {BaseField : Type*} [Field BaseField] {Index : Type*}
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (distinct_classes : Function.Injective (fun index =>
      TauCeti.AlgebraicGeometry.LineBundleClass.mk (line_bundles index))) :
    IsPartialOrder Index (OrderingObstruction.NonzeroHom
      (fun index => (line_bundles index).obj)) :=
  OrderingObstruction.nonzeroHom_isPartialOrder (fun index => (line_bundles index).obj)
    (fun index => invertibleSheaf_identity_ne_zero_of_globalFunctions global_functions
      (line_bundles index))
    (fun {source middle target} first second first_nonzero second_nonzero =>
      invertibleSheaf_comp_ne_zero_of_isIntegral (line_bundles source) (line_bundles middle)
        (line_bundles target) first second first_nonzero second_nonzero)
    (fun index endomorphism nonzero =>
      invertibleSheaf_nonzero_endomorphism_isIso_of_globalFunctions global_functions
        (line_bundles index) endomorphism nonzero)
    (fun _ _ isomorphic => distinct_classes
      (TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff.mpr isomorphic))

end BondalThomsen
