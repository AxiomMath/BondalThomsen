module

public import BondalThomsen.ProjectiveBundle.FrameCompatibility
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import BondalThomsen.Toric.Divisor.PicardEquivalence
public import BondalThomsen.ProjectiveBundle.Scheme
public import BondalThomsen.ProjectiveBundle.NefSupport
public import BondalThomsen.Toric.Divisor.DivisorSheafSections
public import BondalThomsen.Toric.Positivity.GlobalGenerationCriterion
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.Pullback
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.GlobalSections

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open Classical AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable def restrictLocalModuleHom {schemeModel : Scheme}
    {source target : schemeModel.Modules} {smaller larger : schemeModel.Opens}
    (contained : smaller ≤ larger) (morphism : source.over larger ⟶ target.over larger) :
    source.over smaller ⟶ target.over smaller :=
  ((SheafOfModules.overFunctorMap schemeModel.ringCatSheaf (homOfLE contained)).app source).inv ≫
    (SheafOfModules.overMap schemeModel.ringCatSheaf (homOfLE contained)).map morphism ≫
    ((SheafOfModules.overFunctorMap schemeModel.ringCatSheaf (homOfLE contained)).app target).hom

theorem restrictLocalModuleHom_app {schemeModel : Scheme}
    {source target : schemeModel.Modules} {smaller larger : schemeModel.Opens}
    (contained : smaller ≤ larger) (morphism : source.over larger ⟶ target.over larger)
    (subopen : Over smaller) (coefficient : Γ(source, subopen.left)) :
    (restrictLocalModuleHom contained morphism).val.app (op subopen) coefficient =
      morphism.val.app (op (Over.mk (subopen.hom ≫ homOfLE contained))) coefficient := by
  rfl

theorem restrictLocalModuleHom_global {schemeModel : Scheme}
    {source target : schemeModel.Modules} {smaller larger : schemeModel.Opens}
    (contained : smaller ≤ larger) (morphism : source ⟶ target) :
    restrictLocalModuleHom contained (morphism.over larger) = morphism.over smaller := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.Hom.ext
  funext subopen
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  cases subopen with
  | op subopen => rfl

theorem restrictLocalModuleHom_map_comp {schemeModel : Scheme}
    {source middle target : schemeModel.Modules} {smaller larger : schemeModel.Opens}
    (contained : smaller ≤ larger) (first : source.over larger ⟶ middle.over larger)
    (second : middle.over larger ⟶ target.over larger) :
    restrictLocalModuleHom contained (first ≫ second) =
      restrictLocalModuleHom contained first ≫ restrictLocalModuleHom contained second := by
  dsimp only [restrictLocalModuleHom]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

namespace LocalModuleGluing

variable {schemeModel : Scheme} {source target : schemeModel.Modules} {Index : Type}
    (charts : Index → schemeModel.Opens) (covers : IsOpenCover charts)
    (localMaps : ∀ index, source.over (charts index) ⟶ target.over (charts index))
    (compatible : ∀ first second,
      restrictLocalModuleHom (inf_le_left : charts first ⊓ charts second ≤ charts first)
          (localMaps first) =
        restrictLocalModuleHom (inf_le_right : charts first ⊓ charts second ≤ charts second)
          (localMaps second))

include covers in
theorem chartIntersection_covers (domain : schemeModel.Opens) :
    domain ≤ ⨆ index, domain ⊓ charts index := by
  rw [← inf_iSup_eq, covers.iSup_eq_top, inf_top_eq]

noncomputable def localImage (domain : schemeModel.Opens) (sectionValue : Γ(source, domain))
    (index : Index) : Γ(target, domain ⊓ charts index) :=
  (localMaps index).val.app
    (op (Over.mk (homOfLE (inf_le_right : domain ⊓ charts index ≤ charts index))))
    (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op sectionValue)

include compatible in
theorem localImage_compatible (domain : schemeModel.Opens) (sectionValue : Γ(source, domain)) :
    TopCat.Presheaf.IsCompatible target.presheaf (fun index => domain ⊓ charts index)
      (localImage charts localMaps domain sectionValue) := by
  intro first second
  let common := (domain ⊓ charts first) ⊓ (domain ⊓ charts second)
  have inOverlap : common ≤ charts first ⊓ charts second :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have mapsEqual := congrArg (fun morphism => morphism.val.app
      (op (Over.mk (homOfLE inOverlap)))
      (source.presheaf.map (homOfLE
        (inf_le_left.trans inf_le_left : common ≤ domain)).op sectionValue))
    (compatible first second)
  simp only [restrictLocalModuleHom_app] at mapsEqual
  have firstNatural := congrArg (fun morphism => morphism.hom
      (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts first ≤ domain)).op sectionValue))
    ((localMaps first).val.naturality
      (Over.homMk (U := Over.mk (homOfLE (inOverlap.trans inf_le_left)))
        (V := Over.mk (homOfLE (inf_le_right : domain ⊓ charts first ≤ charts first)))
        (homOfLE (inf_le_left : common ≤ domain ⊓ charts first))).op)
  have secondNatural := congrArg (fun morphism => morphism.hom
      (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts second ≤ domain)).op sectionValue))
    ((localMaps second).val.naturality
      (Over.homMk (U := Over.mk (homOfLE (inOverlap.trans inf_le_right)))
        (V := Over.mk (homOfLE (inf_le_right : domain ⊓ charts second ≤ charts second)))
        (homOfLE (inf_le_right : common ≤ domain ⊓ charts second))).op)
  change (localMaps first).val.app (op (Over.mk (homOfLE (inOverlap.trans inf_le_left))))
      (source.presheaf.map (homOfLE (inf_le_left : common ≤ domain ⊓ charts first)).op
        (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts first ≤ domain)).op
          sectionValue)) =
    target.presheaf.map (homOfLE (inf_le_left : common ≤ domain ⊓ charts first)).op
      (localImage charts localMaps domain sectionValue first) at firstNatural
  change (localMaps second).val.app (op (Over.mk (homOfLE (inOverlap.trans inf_le_right))))
      (source.presheaf.map (homOfLE (inf_le_right : common ≤ domain ⊓ charts second)).op
        (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts second ≤ domain)).op
          sectionValue)) =
    target.presheaf.map (homOfLE (inf_le_right : common ≤ domain ⊓ charts second)).op
      (localImage charts localMaps domain sectionValue second) at secondNatural
  simp only [← Functor.map_comp_apply] at firstNatural secondNatural
  dsimp only [localImage]
  change target.presheaf.map (homOfLE (inf_le_left : common ≤ domain ⊓ charts first)).op _ =
    target.presheaf.map (homOfLE (inf_le_right : common ≤ domain ⊓ charts second)).op _
  exact firstNatural.symm.trans (mapsEqual.trans secondNatural)

include covers compatible in

theorem existsUnique_image (domain : schemeModel.Opens) (sectionValue : Γ(source, domain)) :
    ∃! image : Γ(target, domain), ∀ index,
      target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op image =
        localImage charts localMaps domain sectionValue index := by
  exact (show TopCat.Sheaf Ab schemeModel from (SheafOfModules.toSheaf _).obj target).existsUnique_gluing'
    (fun index => domain ⊓ charts index) domain (fun index => homOfLE inf_le_left)
    (chartIntersection_covers charts covers domain) _
    (localImage_compatible charts localMaps compatible domain sectionValue)

noncomputable def image (domain : schemeModel.Opens) (sectionValue : Γ(source, domain)) :
    Γ(target, domain) :=
  (existsUnique_image charts covers localMaps compatible domain sectionValue).exists.choose

include covers compatible in
theorem image_restriction (domain : schemeModel.Opens) (sectionValue : Γ(source, domain))
    (index : Index) :
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
        (image charts covers localMaps compatible domain sectionValue) =
      localImage charts localMaps domain sectionValue index :=
  (existsUnique_image charts covers localMaps compatible domain sectionValue).exists.choose_spec index

theorem localImage_add (domain : schemeModel.Opens) (first second : Γ(source, domain))
    (index : Index) :
    localImage charts localMaps domain (first + second) index =
      localImage charts localMaps domain first index + localImage charts localMaps domain second index := by
  dsimp only [localImage]
  rw [map_add, map_add]

theorem localImage_smul (domain : schemeModel.Opens) (scalar : Γ(schemeModel, domain))
    (sectionValue : Γ(source, domain)) (index : Index) :
    localImage charts localMaps domain (scalar • sectionValue) index =
      schemeModel.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op scalar •
        localImage charts localMaps domain sectionValue index := by
  dsimp only [localImage]
  rw [Scheme.Modules.map_smul]
  exact ((localMaps index).val.app _).hom.map_smul _ _

include covers compatible in
theorem image_add (domain : schemeModel.Opens) (first second : Γ(source, domain)) :
    image charts covers localMaps compatible domain (first + second) =
      image charts covers localMaps compatible domain first +
        image charts covers localMaps compatible domain second := by
  apply (show TopCat.Sheaf Ab schemeModel from (SheafOfModules.toSheaf _).obj target).eq_of_locally_eq'
    (fun index => domain ⊓ charts index) domain (fun index => homOfLE inf_le_left)
    (chartIntersection_covers charts covers domain)
  intro index
  change target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (image charts covers localMaps compatible domain (first + second)) =
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (image charts covers localMaps compatible domain first +
        image charts covers localMaps compatible domain second)
  rw [map_add, image_restriction, image_restriction, image_restriction, localImage_add]

include covers compatible in
theorem image_smul (domain : schemeModel.Opens) (scalar : Γ(schemeModel, domain))
    (sectionValue : Γ(source, domain)) :
    image charts covers localMaps compatible domain (scalar • sectionValue) =
      scalar • image charts covers localMaps compatible domain sectionValue := by
  apply (show TopCat.Sheaf Ab schemeModel from (SheafOfModules.toSheaf _).obj target).eq_of_locally_eq'
    (fun index => domain ⊓ charts index) domain (fun index => homOfLE inf_le_left)
    (chartIntersection_covers charts covers domain)
  intro index
  change target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (image charts covers localMaps compatible domain (scalar • sectionValue)) =
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (scalar • image charts covers localMaps compatible domain sectionValue)
  rw [Scheme.Modules.map_smul, image_restriction, image_restriction, localImage_smul]

theorem localImage_naturality {smaller larger : schemeModel.Opens} (contained : smaller ≤ larger)
    (sectionValue : Γ(source, larger)) (index : Index) :
    target.presheaf.map (homOfLE (inf_le_inf_right (charts index) contained)).op
        (localImage charts localMaps larger sectionValue index) =
      localImage charts localMaps smaller (source.presheaf.map (homOfLE contained).op sectionValue)
        index := by
  have naturality := congrArg (fun morphism => morphism.hom
      (source.presheaf.map (homOfLE (inf_le_left : larger ⊓ charts index ≤ larger)).op sectionValue))
    ((localMaps index).val.naturality
      (Over.homMk (U := Over.mk (homOfLE (inf_le_right : smaller ⊓ charts index ≤ charts index)))
        (V := Over.mk (homOfLE (inf_le_right : larger ⊓ charts index ≤ charts index)))
        (homOfLE (inf_le_inf_right (charts index) contained))).op)
  change (localMaps index).val.app
      (op (Over.mk (homOfLE (inf_le_right : smaller ⊓ charts index ≤ charts index))))
      (source.presheaf.map (homOfLE (inf_le_inf_right (charts index) contained)).op
        (source.presheaf.map (homOfLE (inf_le_left : larger ⊓ charts index ≤ larger)).op
          sectionValue)) =
    target.presheaf.map (homOfLE (inf_le_inf_right (charts index) contained)).op
      (localImage charts localMaps larger sectionValue index) at naturality
  dsimp only [localImage]
  simpa only [localImage, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    using naturality.symm

include covers compatible in
theorem image_naturality {smaller larger : schemeModel.Opens} (contained : smaller ≤ larger)
    (sectionValue : Γ(source, larger)) :
    target.presheaf.map (homOfLE contained).op
        (image charts covers localMaps compatible larger sectionValue) =
      image charts covers localMaps compatible smaller
        (source.presheaf.map (homOfLE contained).op sectionValue) := by
  apply (show TopCat.Sheaf Ab schemeModel from (SheafOfModules.toSheaf _).obj target).eq_of_locally_eq'
    (fun index => smaller ⊓ charts index) smaller (fun index => homOfLE inf_le_left)
    (chartIntersection_covers charts covers smaller)
  intro index
  change target.presheaf.map (homOfLE (inf_le_left : smaller ⊓ charts index ≤ smaller)).op
      (target.presheaf.map (homOfLE contained).op
        (image charts covers localMaps compatible larger sectionValue)) =
    target.presheaf.map (homOfLE (inf_le_left : smaller ⊓ charts index ≤ smaller)).op
      (image charts covers localMaps compatible smaller
        (source.presheaf.map (homOfLE contained).op sectionValue))
  rw [image_restriction]
  rw [← localImage_naturality charts localMaps contained sectionValue index,
    ← image_restriction charts covers localMaps compatible larger sectionValue index]
  simp only [← Functor.map_comp_apply]
  rfl

noncomputable def glue : source ⟶ target where
  val.app domain := ModuleCat.ofHom
    { toFun := image charts covers localMaps compatible domain.unop
      map_add' := image_add charts covers localMaps compatible domain.unop
      map_smul' := image_smul charts covers localMaps compatible domain.unop }
  val.naturality {larger smaller} inclusion := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro sectionValue
    change image charts covers localMaps compatible smaller.unop
        (source.presheaf.map inclusion sectionValue) =
      target.presheaf.map inclusion (image charts covers localMaps compatible larger.unop sectionValue)
    exact (image_naturality charts covers localMaps compatible inclusion.unop.le sectionValue).symm

include covers compatible in
theorem image_eq_local (index : Index) (domain : schemeModel.Opens) (contained : domain ≤ charts index)
    (sectionValue : Γ(source, domain)) :
    image charts covers localMaps compatible domain sectionValue =
      (localMaps index).val.app (op (Over.mk (homOfLE contained))) sectionValue := by
  have restricted := image_restriction charts covers localMaps compatible domain sectionValue index
  have overlapEq : domain ⊓ charts index = domain := inf_eq_left.mpr contained
  dsimp only [localImage] at restricted
  generalize_proofs firstProof secondProof at restricted
  generalize commonDef : domain ⊓ charts index = common at firstProof secondProof restricted overlapEq
  clear commonDef
  cases overlapEq
  have firstMap : homOfLE firstProof = 𝟙 domain := Subsingleton.elim _ _
  rw [firstMap, op_id, target.presheaf.map_id, source.presheaf.map_id] at restricted
  exact restricted

theorem glue_over (index : Index) :
    (glue charts covers localMaps compatible).over (charts index) = localMaps index := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.Hom.ext
  funext subopen
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro sectionValue
  cases subopen with
  | op subopen =>
    change image charts covers localMaps compatible subopen.left sectionValue = _
    exact image_eq_local charts covers localMaps compatible index subopen.left subopen.hom.le sectionValue

include covers in

theorem hom_ext (first second : source ⟶ target)
    (localEq : ∀ index, first.over (charts index) = second.over (charts index)) : first = second := by
  apply Scheme.Modules.hom_ext
  intro domain
  ext sectionValue
  apply (show TopCat.Sheaf Ab schemeModel from (SheafOfModules.toSheaf _).obj target).eq_of_locally_eq'
    (fun index => domain ⊓ charts index) domain (fun index => homOfLE inf_le_left)
    (chartIntersection_covers charts covers domain)
  intro index
  have localValue := congrArg (fun morphism => morphism.val.app
      (op (Over.mk (homOfLE (inf_le_right : domain ⊓ charts index ≤ charts index))))
      (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op sectionValue))
    (localEq index)
  change target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (Scheme.Modules.Hom.app first domain sectionValue) =
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (Scheme.Modules.Hom.app second domain sectionValue)
  have firstNatural := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf schemeModel).map first).naturality
      (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op) sectionValue
  have secondNatural := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf schemeModel).map second).naturality
      (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op) sectionValue
  simp only [ConcreteCategory.comp_apply] at firstNatural secondNatural
  change Scheme.Modules.Hom.app first (domain ⊓ charts index)
      (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op sectionValue) =
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (Scheme.Modules.Hom.app first domain sectionValue) at firstNatural
  change Scheme.Modules.Hom.app second (domain ⊓ charts index)
      (source.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op sectionValue) =
    target.presheaf.map (homOfLE (inf_le_left : domain ⊓ charts index ≤ domain)).op
      (Scheme.Modules.Hom.app second domain sectionValue) at secondNatural
  exact firstNatural.symm.trans (localValue.trans secondNatural)

end LocalModuleGluing

namespace ProjectiveBundle

variable {rows baseDimension columns : ℕ}

variable {𝕜} in
local instance globalRelativeQuotient_schemeIntegral
    (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    IsIntegral (scheme 𝕜 (baseDimension := baseDimension) matrix) := scheme_isIntegral 𝕜 matrix

variable {𝕜} in
local instance globalRelativeQuotient_fanIntegral
    (matrix : Matrix (Fin rows) (Fin columns) ℤ) :
    IsIntegral ((fan (baseDimension := baseDimension) matrix).algebraicRealization 𝕜
      (fan_isRegular matrix)) :=
  (fan matrix).algebraicRealization_isIntegral 𝕜 (fan_isRegular matrix)
    ((fan matrix).completeFan_nonemptyCones (fan_isComplete matrix))

end ProjectiveBundle

end BondalThomsen
