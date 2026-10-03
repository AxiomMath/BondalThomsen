module

public import BondalThomsen.Toric.Frobenius.MultiplicationDivisorPullback
public import Mathlib.CategoryTheory.Sites.LocalProperties

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

universe schemeUniverse

variable {SchemeModel : Scheme.{schemeUniverse}} [IsIntegral SchemeModel]

theorem rationalPullback_nonempty_preimage (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain : SchemeModel.Opens) [Nonempty domain] : Nonempty (morphism ⁻¹ᵁ domain) := by
  refine ⟨⟨genericPoint SchemeModel, ?_⟩⟩
  change morphism (genericPoint SchemeModel) ∈ domain
  rw [generic]
  exact TauCeti.AlgebraicGeometry.Scheme.genericPoint_mem domain

theorem rationalPullback_stalk (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (point : SchemeModel) (localSection : SchemeModel.presheaf.stalk (morphism point)) :
    rationalPullback morphism generic
        (algebraMap (SchemeModel.presheaf.stalk (morphism point)) SchemeModel.functionField
          localSection) =
      algebraMap (SchemeModel.presheaf.stalk point) SchemeModel.functionField
        (morphism.stalkMap point localSection) := by
  obtain ⟨domain, member, regularSection, represent⟩ :=
    SchemeModel.presheaf.exists_germ_eq localSection
  let : Nonempty domain := ⟨⟨morphism point, member⟩⟩
  let : Nonempty (morphism ⁻¹ᵁ domain) := ⟨⟨point, member⟩⟩
  rw [← represent, Scheme.algebraMap_germ_eq_germToFunctionField,
    morphism.germ_stalkMap_apply,
    Scheme.algebraMap_germ_eq_germToFunctionField]
  exact rationalPullback_germ morphism generic domain regularSection

theorem rationalPullback_mem_stalkRange (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (point : SchemeModel) {rational : SchemeModel.functionField}
    (regular : rational ∈
      (algebraMap (SchemeModel.presheaf.stalk (morphism point)) SchemeModel.functionField).range) :
    rationalPullback morphism generic rational ∈
      (algebraMap (SchemeModel.presheaf.stalk point) SchemeModel.functionField).range := by
  obtain ⟨localSection, rfl⟩ := regular
  exact ⟨morphism.stalkMap point localSection,
    (rationalPullback_stalk morphism generic point localSection).symm⟩

noncomputable def rationalSectionsPullback (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain : SchemeModel.Opens) :
    Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel, domain) →+
      Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel,
        morphism ⁻¹ᵁ domain) := by
  classical
  exact if nonempty : Nonempty domain then
    letI := nonempty
    letI := rationalPullback_nonempty_preimage morphism generic domain
    (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv
      (morphism ⁻¹ᵁ domain)).symm.toAddMonoidHom.comp
        ((rationalPullback morphism generic).toAddMonoidHom.comp
          (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain).toAddMonoidHom)
  else 0

theorem rationalSectionsPullback_equiv (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain : SchemeModel.Opens) [Nonempty domain] [Nonempty (morphism ⁻¹ᵁ domain)]
    (rationalSection :
      Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel, domain)) :
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (morphism ⁻¹ᵁ domain)
        (rationalSectionsPullback morphism generic domain rationalSection) =
      rationalPullback morphism generic
        (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain rationalSection) := by
  classical
  rw [rationalSectionsPullback, dite_eq_left (inferInstance : Nonempty domain)]
  exact LinearEquiv.apply_symm_apply _ _

theorem rationalSectionsPullback_smul (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (domain : SchemeModel.Opens) (coefficient : Γ(SchemeModel, domain))
    (rationalSection :
      Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel, domain)) :
    rationalSectionsPullback morphism generic domain (coefficient • rationalSection) =
      morphism.app domain coefficient •
        rationalSectionsPullback morphism generic domain rationalSection := by
  classical
  by_cases nonempty : Nonempty domain
  · let := nonempty
    let := rationalPullback_nonempty_preimage morphism generic domain
    apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _).injective
    simp only [rationalSectionsPullback_equiv, map_smul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, map_mul, rationalPullback_germ]
  · simp [rationalSectionsPullback, nonempty]

theorem rationalSectionsPullback_restrict (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    {domain smaller : SchemeModel.Opens} (inclusion : smaller ⟶ domain)
    (rationalSection :
      Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel, domain)) :
    rationalSectionsPullback morphism generic smaller
        ((TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel).presheaf.map
          inclusion.op rationalSection) =
      (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel).presheaf.map
        ((Opens.map morphism.base).map inclusion).op
        (rationalSectionsPullback morphism generic domain rationalSection) := by
  classical
  by_cases nonempty : Nonempty smaller
  · let := nonempty
    let : Nonempty domain := by
      obtain ⟨point, member⟩ := nonempty
      exact ⟨⟨point, inclusion.le member⟩⟩
    let := rationalPullback_nonempty_preimage morphism generic smaller
    let := rationalPullback_nonempty_preimage morphism generic domain
    apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv _).injective
    simp only [rationalSectionsPullback_equiv,
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map]
  · have empty : smaller = ⊥ := by
      apply bot_unique
      intro point member
      exact False.elim (nonempty ⟨⟨point, member⟩⟩)
    have pulled_empty : morphism ⁻¹ᵁ smaller = ⊥ := by simp [empty]
    let := TauCeti.AlgebraicGeometry.Scheme.subsingleton_rationalFunctions
      (morphism ⁻¹ᵁ smaller) pulled_empty
    exact Subsingleton.elim _ _

namespace CartierEquationAtlas

theorem rationalSectionsPullback_mem (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    (domain : SchemeModel.Opens)
    {rationalSection :
      Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel, domain)}
    (member : rationalSection ∈ atlas.cartierDivisor.sections domain) :
    rationalSectionsPullback morphism generic domain rationalSection ∈
      (atlas.pullbackPreserved morphism generic preserved).cartierDivisor.sections
        (morphism ⁻¹ᵁ domain) := by
  apply TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.mem_sections_iff_exists.mpr
  intro point point_member
  let : Nonempty domain := ⟨⟨morphism point, point_member⟩⟩
  let : Nonempty (morphism ⁻¹ᵁ domain) := ⟨⟨point, point_member⟩⟩
  obtain ⟨index, chart_member⟩ := atlas.covers.exists_mem point
  have image_member : morphism point ∈ atlas.chart index := by
    change point ∈ morphism ⁻¹ᵁ atlas.chart index
    rw [preserved index]
    exact chart_member
  refine ⟨_, (atlas.pullbackPreserved morphism generic preserved).equation_isLocalEquationAt
    index point chart_member, ?_⟩
  have regular := member (morphism point) point_member (atlas.equation index)
    (atlas.equation_isLocalEquationAt index (morphism point) image_member)
  have pulled := rationalPullback_mem_stalkRange morphism generic point regular
  change rationalPullback morphism generic (atlas.equation index : SchemeModel.functionField) *
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (morphism ⁻¹ᵁ domain)
      (rationalSectionsPullback morphism generic domain rationalSection) ∈ _
  rw [rationalSectionsPullback_equiv, ← map_mul]
  exact pulled

end CartierEquationAtlas

noncomputable def rationalSheafToPushforward (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel) :
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel ⟶
      (Scheme.Modules.pushforward morphism).obj
        (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions SchemeModel) where
  val :=
    { app := fun domain => { hom' :=
        { toFun := rationalSectionsPullback morphism generic domain.unop
          map_add' := (rationalSectionsPullback morphism generic domain.unop).map_add
          map_smul' := fun coefficient rationalSection =>
            rationalSectionsPullback_smul morphism generic domain.unop coefficient rationalSection } }
      naturality := by
        intro domain smaller inclusion
        ext rationalSection
        exact rationalSectionsPullback_restrict morphism generic inclusion.unop rationalSection }

namespace CartierEquationAtlas

noncomputable def localSectionHom (moduleSheaf : SchemeModel.Modules)
    (domain : SchemeModel.Opens) (regularSection : Γ(moduleSheaf, domain)) :
    (SheafOfModules.unit SchemeModel.ringCatSheaf).over domain ⟶ moduleSheaf.over domain where
  val :=
    { app := fun smaller => { hom' :=
        { toFun := fun (coefficient : Γ(SchemeModel, smaller.unop.left)) => coefficient •
            (moduleSheaf.presheaf.map smaller.unop.hom.op regularSection :
              Γ(moduleSheaf, smaller.unop.left))
          map_add' := by
            intro first second
            change Γ(SchemeModel, smaller.unop.left) at first second
            change (first + second) • (moduleSheaf.presheaf.map smaller.unop.hom.op
              regularSection : Γ(moduleSheaf, smaller.unop.left)) = _
            exact add_smul first second _
          map_smul' := by
            intro first second
            change Γ(SchemeModel, smaller.unop.left) at first second
            change (first * second : Γ(SchemeModel, smaller.unop.left)) •
                (moduleSheaf.presheaf.map smaller.unop.hom.op regularSection :
                  Γ(moduleSheaf, smaller.unop.left)) =
              first • (second • (moduleSheaf.presheaf.map smaller.unop.hom.op regularSection :
                Γ(moduleSheaf, smaller.unop.left)))
            exact mul_smul first second _ } }
      naturality := by
        intro first second inclusion
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro coefficient
        change Γ(SchemeModel, first.unop.left) at coefficient
        change SchemeModel.presheaf.map inclusion.unop.left.op coefficient •
            moduleSheaf.presheaf.map second.unop.hom.op regularSection =
          moduleSheaf.presheaf.map inclusion.unop.left.op
            (coefficient • moduleSheaf.presheaf.map first.unop.hom.op regularSection)
        rw [moduleSheaf.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl }

theorem chartTrivialization_ι (atlas : CartierEquationAtlas SchemeModel)
    (index : atlas.Index) :
    (atlas.chartTrivialization index).hom ≫ atlas.cartierDivisor.sheafι.over (atlas.chart index) =
      (SheafOfModules.overFunctor SchemeModel.ringCatSheaf (atlas.chart index)).map
        (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitToSheafPrincipalCartierDivisor
          SchemeModel (atlas.equation index)) ≫
        (TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor
          SchemeModel (atlas.equation index)).sheafι.over (atlas.chart index) := by
  let := atlas.nonempty_chart index
  simp only [chartTrivialization, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheafOverIsoOfRestrictEq_hom_ι]
  rfl

theorem chartTrivialization_rational (atlas : CartierEquationAtlas SchemeModel)
    (index : atlas.Index) (coefficient : Γ(SchemeModel, atlas.chart index)) :
    letI := atlas.nonempty_chart index
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (atlas.chart index)
      (Scheme.Modules.Hom.app atlas.cartierDivisor.sheafι (atlas.chart index)
        ((atlas.chartTrivialization index).hom.val.app
          (op (Over.mk (𝟙 (atlas.chart index)))) coefficient)) =
      (atlas.equation index : SchemeModel.functionField)⁻¹ *
        SchemeModel.germToFunctionField (atlas.chart index) coefficient := by
  let := atlas.nonempty_chart index
  have inclusion := congrArg (fun comparison => comparison.val.app
    (op (Over.mk (𝟙 (atlas.chart index)))) coefficient) (atlas.chartTrivialization_ι index)
  change Scheme.Modules.Hom.app atlas.cartierDivisor.sheafι (atlas.chart index)
      ((atlas.chartTrivialization index).hom.val.app
        (op (Over.mk (𝟙 (atlas.chart index)))) coefficient) = _ at inclusion
  rw [inclusion]
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (atlas.chart index)
      (Scheme.Modules.Hom.app
        (TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor
          SchemeModel (atlas.equation index)).sheafι (atlas.chart index)
        (Scheme.Modules.Hom.app
          (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitToSheafPrincipalCartierDivisor
            SchemeModel (atlas.equation index)) (atlas.chart index) coefficient)) = _
  rw [TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitToSheafPrincipalCartierDivisor_app,
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app,
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_toRationalFunctions_app]
  simp only [Units.val_inv_eq_inv_val]

noncomputable def sectionsPullback (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    (domain : SchemeModel.Opens) :
    Γ(atlas.cartierDivisor.sheaf, domain) →+
      Γ((atlas.pullbackPreserved morphism generic preserved).cartierDivisor.sheaf,
        morphism ⁻¹ᵁ domain) where
  toFun regularSection :=
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sectionMk
      (rationalSectionsPullback morphism generic domain
        (Scheme.Modules.Hom.app atlas.cartierDivisor.sheafι domain regularSection))
      (atlas.rationalSectionsPullback_mem morphism generic preserved domain
        (atlas.cartierDivisor.sheafι_app_mem domain regularSection))
  map_zero' := by
    apply (atlas.pullbackPreserved morphism generic preserved).cartierDivisor
      |>.sheafι_app_injective (morphism ⁻¹ᵁ domain)
    simp only [map_zero,
      TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheafι_app_sectionMk]
  map_add' := by
    intro first second
    apply (atlas.pullbackPreserved morphism generic preserved).cartierDivisor
      |>.sheafι_app_injective (morphism ⁻¹ᵁ domain)
    simp only [map_add,
      TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheafι_app_sectionMk]

theorem sectionsPullback_ι (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    (domain : SchemeModel.Opens) (regularSection : Γ(atlas.cartierDivisor.sheaf, domain)) :
    Scheme.Modules.Hom.app
        (atlas.pullbackPreserved morphism generic preserved).cartierDivisor.sheafι
        (morphism ⁻¹ᵁ domain)
        (atlas.sectionsPullback morphism generic preserved domain regularSection) =
      rationalSectionsPullback morphism generic domain
        (Scheme.Modules.Hom.app atlas.cartierDivisor.sheafι domain regularSection) := rfl

theorem sectionsPullback_smul (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    (domain : SchemeModel.Opens) (coefficient : Γ(SchemeModel, domain))
    (regularSection : Γ(atlas.cartierDivisor.sheaf, domain)) :
    atlas.sectionsPullback morphism generic preserved domain (coefficient • regularSection) =
      morphism.app domain coefficient •
        atlas.sectionsPullback morphism generic preserved domain regularSection := by
  apply (atlas.pullbackPreserved morphism generic preserved).cartierDivisor
    |>.sheafι_app_injective (morphism ⁻¹ᵁ domain)
  rw [Scheme.Modules.Hom.app_smul, sectionsPullback_ι, sectionsPullback_ι,
    Scheme.Modules.Hom.app_smul, rationalSectionsPullback_smul]

theorem sectionsPullback_restrict (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    {domain smaller : SchemeModel.Opens} (inclusion : smaller ⟶ domain)
    (regularSection : Γ(atlas.cartierDivisor.sheaf, domain)) :
    atlas.sectionsPullback morphism generic preserved smaller
        (atlas.cartierDivisor.sheaf.presheaf.map inclusion.op regularSection) =
      (atlas.pullbackPreserved morphism generic preserved).cartierDivisor.sheaf.presheaf.map
        ((Opens.map morphism.base).map inclusion).op
        (atlas.sectionsPullback morphism generic preserved domain regularSection) := by
  apply (atlas.pullbackPreserved morphism generic preserved).cartierDivisor
    |>.sheafι_app_injective (morphism ⁻¹ᵁ smaller)
  have original_naturality := ConcreteCategory.congr_hom
    (atlas.cartierDivisor.sheafι.mapPresheaf.naturality inclusion.op) regularSection
  have pulled_naturality := ConcreteCategory.congr_hom
    ((atlas.pullbackPreserved morphism generic preserved).cartierDivisor.sheafι.mapPresheaf
      |>.naturality ((Opens.map morphism.base).map inclusion).op)
    (atlas.sectionsPullback morphism generic preserved domain regularSection)
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at original_naturality pulled_naturality
  rw [sectionsPullback_ι, original_naturality, pulled_naturality, sectionsPullback_ι]
  exact rationalSectionsPullback_restrict morphism generic inclusion
    (Scheme.Modules.Hom.app atlas.cartierDivisor.sheafι domain regularSection)

noncomputable def sheafToPushforward (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index) :
    atlas.cartierDivisor.sheaf ⟶ (Scheme.Modules.pushforward morphism).obj
      (atlas.pullbackPreserved morphism generic preserved).cartierDivisor.sheaf where
  val :=
    { app := fun domain => { hom' :=
        { toFun := atlas.sectionsPullback morphism generic preserved domain.unop
          map_add' := (atlas.sectionsPullback morphism generic preserved domain.unop).map_add
          map_smul' := fun coefficient regularSection =>
            atlas.sectionsPullback_smul morphism generic preserved domain.unop
              coefficient regularSection } }
      naturality := by
        intro domain smaller inclusion
        ext regularSection
        exact atlas.sectionsPullback_restrict morphism generic preserved inclusion.unop
          regularSection }

noncomputable def modulePullbackComparison (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index) :
    (Scheme.Modules.pullback morphism).obj atlas.cartierDivisor.sheaf ⟶
      (atlas.pullbackPreserved morphism generic preserved).cartierDivisor.sheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction morphism).homEquiv _ _).symm
    (atlas.sheafToPushforward morphism generic preserved)

theorem modulePullbackComparison_adjoint (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index) :
    (Scheme.Modules.pullbackPushforwardAdjunction morphism).homEquiv _ _
        (atlas.modulePullbackComparison morphism generic preserved) =
      atlas.sheafToPushforward morphism generic preserved :=
  Equiv.apply_symm_apply _ _

theorem modulePullbackComparison_unit (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    (domain : SchemeModel.Opens) (regularSection : Γ(atlas.cartierDivisor.sheaf, domain)) :
    Scheme.Modules.Hom.app (atlas.modulePullbackComparison morphism generic preserved)
        (morphism ⁻¹ᵁ domain)
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app
            atlas.cartierDivisor.sheaf) domain regularSection) =
      atlas.sectionsPullback morphism generic preserved domain regularSection := by
  have equation := atlas.modulePullbackComparison_adjoint morphism generic preserved
  rw [Adjunction.homEquiv_unit] at equation
  exact congrArg (fun comparison => Scheme.Modules.Hom.app comparison domain regularSection) equation

omit [IsIntegral SchemeModel] in

theorem localUnitHom_ext {moduleSheaf : SchemeModel.Modules} {domain : SchemeModel.Opens}
    {first second : (SheafOfModules.unit SchemeModel.ringCatSheaf).over domain ⟶
      moduleSheaf.over domain}
    (same : first.val.app (op (Over.mk (𝟙 domain))) (1 : Γ(SchemeModel, domain)) =
      second.val.app (op (Over.mk (𝟙 domain))) (1 : Γ(SchemeModel, domain))) : first = second := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro smaller
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change Γ(SchemeModel, smaller.unop.left) at coefficient
  let restrictionMap : smaller.unop ⟶ Over.mk (𝟙 domain) :=
    Over.homMk smaller.unop.hom
  have restriction := ConcreteCategory.congr_hom
    (first.val.naturality restrictionMap.op) (1 : Γ(SchemeModel, domain))
  have restriction' := ConcreteCategory.congr_hom
    (second.val.naturality restrictionMap.op) (1 : Γ(SchemeModel, domain))
  simp only [ConcreteCategory.comp_apply] at restriction restriction'
  have values : first.val.app smaller (1 : Γ(SchemeModel, smaller.unop.left)) =
      second.val.app smaller (1 : Γ(SchemeModel, smaller.unop.left)) := by
    change first.val.app smaller (SchemeModel.presheaf.map smaller.unop.hom.op 1) = _ at restriction
    change second.val.app smaller (SchemeModel.presheaf.map smaller.unop.hom.op 1) = _ at restriction'
    rw [map_one] at restriction restriction'
    rw [restriction, restriction', same]
  have first_linear := (first.val.app smaller).hom.map_smul coefficient
    (1 : Γ(SchemeModel, smaller.unop.left))
  have second_linear := (second.val.app smaller).hom.map_smul coefficient
    (1 : Γ(SchemeModel, smaller.unop.left))
  change first.val.app smaller (coefficient * (1 : Γ(SchemeModel, smaller.unop.left))) =
    coefficient • first.val.app smaller (1 : Γ(SchemeModel, smaller.unop.left)) at first_linear
  change second.val.app smaller (coefficient * (1 : Γ(SchemeModel, smaller.unop.left))) =
    coefficient • second.val.app smaller (1 : Γ(SchemeModel, smaller.unop.left)) at second_linear
  rw [mul_one] at first_linear second_linear
  exact first_linear.trans ((congrArg (coefficient • ·) values).trans second_linear.symm)

noncomputable def liftedFrameSection (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    (index : atlas.Index) :
    Γ((Scheme.Modules.pullback morphism).obj atlas.cartierDivisor.sheaf, atlas.chart index) :=
  ((Scheme.Modules.pullback morphism).obj atlas.cartierDivisor.sheaf).presheaf.map
    (eqToHom (preserved index).symm).op
    (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app atlas.cartierDivisor.sheaf)
      (atlas.chart index)
      ((atlas.chartTrivialization index).hom.val.app (op (Over.mk (𝟙 (atlas.chart index))))
        (1 : Γ(SchemeModel, atlas.chart index))))

theorem liftedFrameSection_comparison (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    (index : atlas.Index) :
    Scheme.Modules.Hom.app (atlas.modulePullbackComparison morphism generic preserved)
        (atlas.chart index) (atlas.liftedFrameSection morphism preserved index) =
      ((atlas.pullbackPreserved morphism generic preserved).chartTrivialization index).hom.val.app
        (op (Over.mk (𝟙 (atlas.chart index)))) (1 : Γ(SchemeModel, atlas.chart index)) := by
  let := atlas.nonempty_chart index
  let := rationalPullback_nonempty_preimage morphism generic (atlas.chart index)
  apply (atlas.pullbackPreserved morphism generic preserved).cartierDivisor
    |>.sheafι_app_injective (atlas.chart index)
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (atlas.chart index)).injective
  have naturality := (atlas.modulePullbackComparison morphism generic preserved).mapPresheaf
    |>.naturality_apply (eqToHom (preserved index).symm).op
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction morphism).unit.app atlas.cartierDivisor.sheaf)
        (atlas.chart index)
        ((atlas.chartTrivialization index).hom.val.app (op (Over.mk (𝟙 (atlas.chart index))))
          (1 : Γ(SchemeModel, atlas.chart index))))
  change Scheme.Modules.Hom.app (atlas.modulePullbackComparison morphism generic preserved)
    (atlas.chart index) (atlas.liftedFrameSection morphism preserved index) = _ at naturality
  rw [naturality]
  simp only [Scheme.Modules.mapPresheaf_app]
  rw [atlas.modulePullbackComparison_unit]
  have included := (atlas.pullbackPreserved morphism generic preserved).cartierDivisor.sheafι.mapPresheaf
    |>.naturality_apply (eqToHom (preserved index).symm).op
      (atlas.sectionsPullback morphism generic preserved (atlas.chart index)
        ((atlas.chartTrivialization index).hom.val.app (op (Over.mk (𝟙 (atlas.chart index))))
          (1 : Γ(SchemeModel, atlas.chart index))))
  simp only [Scheme.Modules.mapPresheaf_app] at included
  rw [included, TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map,
    sectionsPullback_ι, rationalSectionsPullback_equiv, chartTrivialization_rational]
  have target := (atlas.pullbackPreserved morphism generic preserved).chartTrivialization_rational
    index (1 : Γ(SchemeModel, atlas.chart index))
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (atlas.chart index)
      (Scheme.Modules.Hom.app
        (atlas.pullbackPreserved morphism generic preserved).cartierDivisor.sheafι
        (atlas.chart index)
        (((atlas.pullbackPreserved morphism generic preserved).chartTrivialization index).hom.val.app
          (op (Over.mk (𝟙 (atlas.chart index)))) (1 : Γ(SchemeModel, atlas.chart index)))) = _ at target
  rw [target]
  simp only [map_one, mul_one, map_inv₀]
  rfl

omit [IsIntegral SchemeModel] in

theorem localUnitEnd_comp_comm (domain : SchemeModel.Opens)
    (first second : End ((SheafOfModules.unit SchemeModel.ringCatSheaf).over domain)) :
    first ≫ second = second ≫ first := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro smaller
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  change Γ(SchemeModel, smaller.unop.left) at coefficient
  let action (comparison : End ((SheafOfModules.unit SchemeModel.ringCatSheaf).over domain)) :
      Γ(SchemeModel, smaller.unop.left) → Γ(SchemeModel, smaller.unop.left) :=
    fun value => comparison.val.app smaller value
  have linear (comparison : End ((SheafOfModules.unit SchemeModel.ringCatSheaf).over domain))
      (value : Γ(SchemeModel, smaller.unop.left)) :
      action comparison value = value * action comparison 1 := by
    have equation := (comparison.val.app smaller).hom.map_smul value
      (1 : Γ(SchemeModel, smaller.unop.left))
    change action comparison (value * 1) = value * action comparison 1 at equation
    simpa only [mul_one] using equation
  change action second (action first coefficient) = action first (action second coefficient)
  rw [linear second (action first coefficient), linear first (action second coefficient),
    linear first coefficient, linear second coefficient]
  exact mul_right_comm coefficient (action first 1) (action second 1)

omit [IsIntegral SchemeModel] in

theorem localComparison_isIso {source target : SchemeModel.Modules} (domain : SchemeModel.Opens)
    (comparison : source.over domain ⟶ target.over domain)
    (sourceFrame : (SheafOfModules.unit SchemeModel.ringCatSheaf).over domain ≅ source.over domain)
    (targetFrame : (SheafOfModules.unit SchemeModel.ringCatSheaf).over domain ≅ target.over domain)
    (lift : (SheafOfModules.unit SchemeModel.ringCatSheaf).over domain ⟶ source.over domain)
    (frame_eq : lift ≫ comparison = targetFrame.hom) : IsIso comparison := by
  let inverse := targetFrame.inv ≫ lift
  have right_inverse : inverse ≫ comparison = 𝟙 _ := by
    simp only [inverse, Category.assoc, frame_eq, targetFrame.inv_hom_id]
  have commutes := localUnitEnd_comp_comm domain
    (sourceFrame.hom ≫ comparison ≫ targetFrame.inv) (lift ≫ sourceFrame.inv)
  have frame_eq_assoc : lift ≫ comparison ≫ targetFrame.inv = 𝟙 _ := by
    rw [← Category.assoc, frame_eq, targetFrame.hom_inv_id]
  have left_inverse : comparison ≫ inverse = 𝟙 _ := by
    apply (cancel_epi sourceFrame.hom).mp
    apply (cancel_mono sourceFrame.inv).mp
    simpa only [inverse, Category.assoc, sourceFrame.inv_hom_id_assoc, frame_eq_assoc,
      targetFrame.hom_inv_id_assoc, sourceFrame.hom_inv_id, Category.comp_id,
      Category.id_comp] using commutes
  exact ⟨⟨inverse, left_inverse, right_inverse⟩⟩

noncomputable def modulePullbackChartFrame (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    (index : atlas.Index) :
    (SheafOfModules.unit SchemeModel.ringCatSheaf).over (atlas.chart index) ≅
      ((Scheme.Modules.pullback morphism).obj atlas.cartierDivisor.sheaf).over (atlas.chart index) := by
  let chart := atlas.chart index
  let frame : (SheafOfModules.unit SchemeModel.ringCatSheaf).over (morphism ⁻¹ᵁ chart) ≅
      ((Scheme.Modules.pullback morphism).obj atlas.cartierDivisor.sheaf).over (morphism ⁻¹ᵁ chart) :=
    Scheme.Modules.pullbackOverUnitIso morphism chart ≪≫
      (Scheme.Modules.pullbackOver morphism chart).mapIso (atlas.chartTrivialization index) ≪≫
      Scheme.Modules.pullbackOverObjIso morphism chart atlas.cartierDivisor.sheaf
  have transport (sourceOpen : SchemeModel.Opens) (equal : sourceOpen = chart)
      (sourceFrame : (SheafOfModules.unit SchemeModel.ringCatSheaf).over sourceOpen ≅
        ((Scheme.Modules.pullback morphism).obj atlas.cartierDivisor.sheaf).over sourceOpen) :
      (SheafOfModules.unit SchemeModel.ringCatSheaf).over chart ≅
        ((Scheme.Modules.pullback morphism).obj atlas.cartierDivisor.sheaf).over chart := by
    subst sourceOpen
    exact sourceFrame
  exact transport _ (preserved index) frame

theorem modulePullbackComparison_over_isIso (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index)
    (index : atlas.Index) :
    IsIso ((atlas.modulePullbackComparison morphism generic preserved).over (atlas.chart index)) := by
  let lift := localSectionHom ((Scheme.Modules.pullback morphism).obj atlas.cartierDivisor.sheaf)
    (atlas.chart index) (atlas.liftedFrameSection morphism preserved index)
  apply localComparison_isIso (atlas.chart index) _
    (atlas.modulePullbackChartFrame morphism preserved index)
    ((atlas.pullbackPreserved morphism generic preserved).chartTrivialization index) lift
  apply localUnitHom_ext
  change Scheme.Modules.Hom.app (atlas.modulePullbackComparison morphism generic preserved)
      (atlas.chart index)
      ((1 : Γ(SchemeModel, atlas.chart index)) •
        ((Scheme.Modules.pullback morphism).obj atlas.cartierDivisor.sheaf).presheaf.map
          (𝟙 (atlas.chart index)).op (atlas.liftedFrameSection morphism preserved index)) = _
  simp only [CategoryTheory.Functor.map_id, op_id, ConcreteCategory.id_apply, one_smul]
  exact atlas.liftedFrameSection_comparison morphism generic preserved index

theorem modulePullbackComparison_isIso (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index) :
    IsIso (atlas.modulePullbackComparison morphism generic preserved) := by
  let comparison := atlas.modulePullbackComparison morphism generic preserved
  let forget := SheafOfModules.toSheaf SchemeModel.ringCatSheaf
  have global_iso : IsIso (forget.map comparison) := by
    apply CategoryTheory.Sheaf.isIso_of_coversTop
      ((Opens.coversTop_iff (SchemeModel : Type schemeUniverse) atlas.chart).mpr atlas.covers)
    intro index
    let := atlas.modulePullbackComparison_over_isIso morphism generic preserved index
    change IsIso ((SheafOfModules.toSheaf (SchemeModel.ringCatSheaf.over (atlas.chart index))).map
      (comparison.over (atlas.chart index)))
    infer_instance
  let := global_iso
  have presheaf_iso : IsIso ((Scheme.Modules.toPresheaf SchemeModel).map comparison) := by
    change IsIso ((sheafToPresheaf (Opens.grothendieckTopology SchemeModel) AddCommGrpCat).map
      (forget.map comparison))
    infer_instance
  exact (isIso_iff_of_reflects_iso comparison (Scheme.Modules.toPresheaf SchemeModel)).mp
    presheaf_iso

noncomputable def modulePullbackIso (atlas : CartierEquationAtlas SchemeModel)
    (morphism : SchemeModel ⟶ SchemeModel)
    (generic : morphism (genericPoint SchemeModel) = genericPoint SchemeModel)
    (preserved : ∀ index, morphism ⁻¹ᵁ atlas.chart index = atlas.chart index) :
    (Scheme.Modules.pullback morphism).obj atlas.cartierDivisor.sheaf ≅
      (atlas.pullbackPreserved morphism generic preserved).cartierDivisor.sheaf := by
  letI := atlas.modulePullbackComparison_isIso morphism generic preserved
  exact asIso (atlas.modulePullbackComparison morphism generic preserved)

end CartierEquationAtlas

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable def toricMultiplicationLineBundlePullbackIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    {degree : ℕ} (positive : 0 < degree) (divisor : fan.InvariantRayDivisor) :
    (Scheme.Modules.pullback (fan.toricMultiplication 𝕜 regular degree)).obj
        (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj ≅
      (fan.invariantDivisorLineBundle 𝕜 complete regular (degree • divisor)).obj := by
  letI := fan.algebraicRealization_isIntegral 𝕜 regular (fan.completeFan_nonemptyCones complete)
  let atlas := ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).neg 𝕜).cartierEquationAtlas 𝕜
    (fan.completeFan_nonemptyCones complete)
  let comparison := atlas.modulePullbackIso (fan.toricMultiplication 𝕜 regular degree)
    (fan.toricMultiplication_genericPoint 𝕜 regular (fan.completeFan_nonemptyCones complete) positive)
    (fun index => fan.toricMultiplication_preimage_chart_open 𝕜 regular positive
      ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular divisor).cone index))
  exact comparison ≪≫ eqToIso
    (congrArg TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf
      (fan.toricMultiplicationInvariantCartierPullback_eq 𝕜 complete regular positive divisor))

end TauCeti.Toric.Fan
