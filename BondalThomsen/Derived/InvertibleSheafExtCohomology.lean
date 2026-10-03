module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.Basic
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite

namespace BondalThomsen.InvertibleSheafExtCohomology

universe u

variable {scheme : Scheme.{u}}

noncomputable abbrev structureSheaf (scheme : Scheme.{u}) : scheme.Modules :=
  SheafOfModules.unit scheme.ringCatSheaf

noncomputable def compatibleSectionsOfGlobal (target : scheme.Modules)
    (global_section : Γ(target, ⊤)) : target.sections :=
  PresheafOfModules.sectionsMk
    (fun open_subset => target.presheaf.map
      (homOfLE (show open_subset.unop ≤ ⊤ from le_top)).op global_section)
    (by
      intro first_open second_open restriction
      change target.presheaf.map restriction
        (target.presheaf.map (homOfLE (show first_open.unop ≤ ⊤ from le_top)).op
          global_section) = _
      rw [← Functor.map_comp_apply]
      exact
        congrArg (fun map => target.presheaf.map map global_section)
          (Subsingleton.elim
            ((homOfLE (show first_open.unop ≤ ⊤ from le_top)).op ≫ restriction)
            (homOfLE (show second_open.unop ≤ ⊤ from le_top)).op))

noncomputable def structureSheafHomGlobalSectionsEquiv (target : scheme.Modules) :
    (structureSheaf scheme ⟶ target) ≃+ Γ(target, ⊤) where
  toFun := fun morphism => morphism.app ⊤ (1 : Γ(scheme, ⊤))
  invFun := fun global_section =>
    (SheafOfModules.unitHomEquiv target).symm (compatibleSectionsOfGlobal target global_section)
  left_inv := by
    intro morphism
    apply (SheafOfModules.unitHomEquiv target).injective
    apply PresheafOfModules.sections_ext
    intro open_subset
    simp only [Equiv.apply_symm_apply]
    change target.presheaf.map
      (homOfLE (show open_subset.unop ≤ ⊤ from le_top)).op
        (morphism.app ⊤ (1 : Γ(scheme, ⊤))) =
      morphism.val.app open_subset (1 : scheme.ringCatSheaf.obj.obj open_subset)
    have naturality := PresheafOfModules.naturality_apply morphism.val
      (homOfLE (show open_subset.unop ≤ ⊤ from le_top)).op (1 : Γ(scheme, ⊤))
    change morphism.val.app open_subset
      ((PresheafOfModules.unit scheme.ringCatSheaf.obj).map
        (homOfLE (show open_subset.unop ≤ ⊤ from le_top)).op (1 : Γ(scheme, ⊤))) =
      target.presheaf.map (homOfLE (show open_subset.unop ≤ ⊤ from le_top)).op
        (morphism.app ⊤ (1 : Γ(scheme, ⊤))) at naturality
    exact naturality.symm.trans (congrArg (fun scalar => morphism.val.app open_subset scalar)
      (PresheafOfModules.unit_map_one scheme.ringCatSheaf.obj
        (homOfLE (show open_subset.unop ≤ ⊤ from le_top)).op))
  right_inv := by
    intro global_section
    have evaluation := SheafOfModules.unitHomEquiv_apply_coe target
      ((SheafOfModules.unitHomEquiv target).symm
        (compatibleSectionsOfGlobal target global_section)) (op ⊤)
    change ((SheafOfModules.unitHomEquiv target).symm
      (compatibleSectionsOfGlobal target global_section)).val.app (op ⊤)
        (1 : Γ(scheme, ⊤)) = global_section
    exact evaluation.symm.trans (by
      rw [Equiv.apply_symm_apply]
      change target.presheaf.map (𝟙 (op ⊤)) global_section = global_section
      simp)
  map_add' := by
    intro first second
    rw [Scheme.Modules.Hom.add_app]
    rfl

local instance : MonoidalPreadditive scheme.Modules :=
  TauCeti.SheafOfModules.monoidalPreadditive scheme.sheaf

theorem structureSheafHomGlobalSectionsEquiv_naturality
    {target next_target : scheme.Modules} (morphism : structureSheaf scheme ⟶ target)
    (next_morphism : target ⟶ next_target) :
    structureSheafHomGlobalSectionsEquiv next_target (morphism ≫ next_morphism) =
      next_morphism.app ⊤ (structureSheafHomGlobalSectionsEquiv target morphism) := by
  rfl

noncomputable def homInternalHomEquiv (source target : scheme.Modules) :
    (source ⟶ target) ≃+ (structureSheaf scheme ⟶ (ihom source).obj target) :=
  ({ toEquiv := (ρ_ source).symm.homCongr (Iso.refl target)
     map_add' := by
       intro first second
       change (ρ_ source).hom ≫ ((first + second) ≫ 𝟙 target) =
         (ρ_ source).hom ≫ (first ≫ 𝟙 target) +
           (ρ_ source).hom ≫ (second ≫ 𝟙 target)
       rw [Preadditive.add_comp, Preadditive.comp_add] } :
    (source ⟶ target) ≃+ (source ⊗ 𝟙_ scheme.Modules ⟶ target)).trans
    ((ihom.adjunction source).homAddEquiv (𝟙_ scheme.Modules) target)

noncomputable def homCohomologyZeroEquiv (source target : scheme.Modules) :
    (source ⟶ target) ≃+
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology ((ihom source).obj target) 0 :=
  (homInternalHomEquiv source target).trans
    ((structureSheafHomGlobalSectionsEquiv ((ihom source).obj target)).trans
      (TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyZeroEquiv
        ((ihom source).obj target)).symm)

noncomputable def extZeroCohomologyEquiv (source target : scheme.Modules) :
    Abelian.Ext source target 0 ≃+
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology ((ihom source).obj target) 0 :=
  Abelian.Ext.addEquiv₀.trans (homCohomologyZeroEquiv source target)

noncomputable def structureSheafHomCohomologyZeroEquiv (target : scheme.Modules) :
    (structureSheaf scheme ⟶ target) ≃+
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology target 0 :=
  (structureSheafHomGlobalSectionsEquiv target).trans
    (TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyZeroEquiv target).symm

theorem structureSheafHomCohomologyZeroEquiv_naturality
    {target next_target : scheme.Modules} (morphism : structureSheaf scheme ⟶ target)
    (next_morphism : target ⟶ next_target) :
    structureSheafHomCohomologyZeroEquiv next_target (morphism ≫ next_morphism) =
      (TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor scheme 0).map
        next_morphism (structureSheafHomCohomologyZeroEquiv target morphism) := by
  apply (TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyZeroEquiv next_target).injective
  rw [TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyZeroEquiv_naturality]
  change (TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyZeroEquiv next_target)
      ((TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyZeroEquiv next_target).symm
        (structureSheafHomGlobalSectionsEquiv next_target (morphism ≫ next_morphism))) =
    next_morphism.app ⊤ ((TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyZeroEquiv target)
      ((TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyZeroEquiv target).symm
        (structureSheafHomGlobalSectionsEquiv target morphism)))
  simp only [AddEquiv.apply_symm_apply]
  exact structureSheafHomGlobalSectionsEquiv_naturality _ _

noncomputable def structureSheafExtZeroCohomologyEquiv (target : scheme.Modules) :
    Abelian.Ext (structureSheaf scheme) target 0 ≃+
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology target 0 :=
  Abelian.Ext.addEquiv₀.trans (structureSheafHomCohomologyZeroEquiv target)

end BondalThomsen.InvertibleSheafExtCohomology
