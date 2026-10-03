module

public import BondalThomsen.Collection.BondalThomsenClasses
public import BondalThomsen.Derived.SheafExtOrdering
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Germ

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace BondalThomsen

universe u v

variable {scheme : Scheme.{u}} {BaseField : Type v} [Field BaseField]

theorem invertibleSheaf_identity_ne_zero_of_globalFunctions
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    𝟙 line_bundle.obj ≠ 0 := by
  let endomorphisms := global_functions.trans
    (Scheme.Modules.globalSectionsActionRingEquiv line_bundle.obj)
  have identity_nonzero := endomorphisms.injective.ne (one_ne_zero : (1 : BaseField) ≠ 0)
  simpa only [map_one, map_zero, End.one_def] using identity_nonzero

theorem invertibleSheaf_nonzero_endomorphism_isIso_of_globalFunctions
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (line_bundle : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (endomorphism : line_bundle.obj ⟶ line_bundle.obj) (nonzero : endomorphism ≠ 0) :
    IsIso endomorphism := by
  let endomorphisms := global_functions.trans
    (Scheme.Modules.globalSectionsActionRingEquiv line_bundle.obj)
  have scalar_nonzero : endomorphisms.symm endomorphism ≠ 0 := by
    intro zero_scalar
    apply nonzero
    simpa only [RingEquiv.apply_symm_apply, map_zero] using
      congrArg endomorphisms zero_scalar
  apply (CategoryTheory.isUnit_iff_isIso endomorphism).mp
  have mapped_unit := (isUnit_iff_ne_zero.mpr scalar_nonzero).map endomorphisms.toMonoidHom
  change IsUnit (endomorphisms (endomorphisms.symm endomorphism)) at mapped_unit
  simpa only [RingEquiv.apply_symm_apply] using mapped_unit

theorem exists_invertibleSheafExt_ordering_of_globalFunctions
    {Index : Type*} [Fintype Index]
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (composition_nonzero : ∀ {source middle target : Index}
      (first : (line_bundles source).obj ⟶ (line_bundles middle).obj)
      (second : (line_bundles middle).obj ⟶ (line_bundles target).obj),
      first ≠ 0 → second ≠ 0 → first ≫ second ≠ 0)
    (pairwise_nonisomorphic : ∀ {first second : Index},
      Nonempty ((line_bundles first).obj ≅ (line_bundles second).obj) → first = second)
    (positive_vanishing : ∀ source target degree, 0 < degree →
      Subsingleton (Abelian.Ext (line_bundles source).obj (line_bundles target).obj degree)) :
    ∃ numbering : Index ≃ Fin (Fintype.card Index),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Abelian.Ext (line_bundles source).obj
          (line_bundles target).obj degree), extension = 0 :=
  exists_invertibleSheafExt_backward_ordering scheme line_bundles
    (fun index => invertibleSheaf_identity_ne_zero_of_globalFunctions global_functions
      (line_bundles index)) composition_nonzero
    (fun index endomorphism nonzero =>
      invertibleSheaf_nonzero_endomorphism_isIso_of_globalFunctions global_functions
        (line_bundles index) endomorphism nonzero)
    pairwise_nonisomorphic positive_vanishing

end BondalThomsen
