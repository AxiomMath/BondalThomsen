module

public import BondalThomsen.Derived.SheafDerivedDegreeZero
public import BondalThomsen.Toric.Scheme.Noetherian
public import BondalThomsen.Toric.Divisor.DivisorLineBundle
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Subcategory

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace BondalThomsen

universe schemeUniverse derivedUniverse

noncomputable section

variable (scheme : Scheme.{schemeUniverse})

abbrev coherentModuleProperty [IsLocallyNoetherian scheme] :
    ObjectProperty scheme.Modules :=
  SheafOfModules.isFinitePresentation scheme.ringCatSheaf

abbrev CoherentSheaf [IsLocallyNoetherian scheme] :=
  (coherentModuleProperty scheme).FullSubcategory

instance [IsLocallyNoetherian scheme] (sheaf : CoherentSheaf scheme) :
    sheaf.obj.IsFinitePresentation := sheaf.property

instance [IsLocallyNoetherian scheme] (sheaf : CoherentSheaf scheme) :
    SheafOfModules.IsQuasicoherent.{schemeUniverse, schemeUniverse, schemeUniverse}
      sheaf.obj := by
  obtain ⟨presentation, _⟩ := sheaf.property
  exact SheafOfModules.QuasicoherentData.isQuasicoherent
    (R := scheme.ringCatSheaf) (M := sheaf.obj) presentation

instance [IsLocallyNoetherian scheme] :
    (coherentModuleProperty scheme).IsClosedUnderIsomorphisms :=
  inferInstanceAs (SheafOfModules.isFinitePresentation
    scheme.ringCatSheaf).IsClosedUnderIsomorphisms

theorem isZero_freeEmpty :
    IsZero (SheafOfModules.free (R := scheme.ringCatSheaf) PEmpty.{schemeUniverse + 1}) := by
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.freeHomEquiv _).injective
  funext empty
  exact empty.elim

theorem finitePresentation_of_isZero (sheaf : scheme.Modules) (zero : IsZero sheaf) :
    sheaf.IsFinitePresentation := by
  let freeEmpty := SheafOfModules.free (R := scheme.ringCatSheaf)
    PEmpty.{schemeUniverse + 1}
  have freeZero : IsZero freeEmpty := isZero_freeEmpty scheme
  exact (SheafOfModules.isFinitePresentation scheme.ringCatSheaf).prop_of_iso
    (freeZero.isoZero ≪≫ zero.isoZero.symm) inferInstance

variable [HasDerivedCategory.{derivedUniverse} scheme.Modules]

def coherentCohomologyProperty [IsLocallyNoetherian scheme] :
    ObjectProperty (DerivedCategory scheme.Modules) :=
  fun complex => ∀ degree : ℤ,
    coherentModuleProperty scheme ((DerivedCategory.homologyFunctor scheme.Modules degree).obj
      complex)

def boundedCoherentProperty [IsLocallyNoetherian scheme] :
    ObjectProperty (DerivedCategory scheme.Modules) :=
  DerivedCategory.TStructure.t.bounded ⊓ coherentCohomologyProperty scheme

variable {scheme}

instance [IsLocallyNoetherian scheme] :
    (coherentCohomologyProperty scheme).IsClosedUnderIsomorphisms where
  of_iso equivalence coherent degree :=
    (coherentModuleProperty scheme).prop_of_iso
      ((DerivedCategory.homologyFunctor scheme.Modules degree).mapIso equivalence)
      (coherent degree)

instance [IsLocallyNoetherian scheme] :
    (boundedCoherentProperty scheme).IsClosedUnderIsomorphisms := by
  dsimp only [boundedCoherentProperty]
  infer_instance

instance [IsLocallyNoetherian scheme] :
    (coherentCohomologyProperty scheme).IsStableUnderShift ℤ where
  isStableUnderShiftBy shift :=
    { le_shift := fun complex coherent degree =>
        (coherentModuleProperty scheme).prop_of_iso
          (((DerivedCategory.homologyFunctor scheme.Modules 0).shiftIso
            shift degree (shift + degree) rfl).app complex).symm
          (coherent (shift + degree)) }

instance [IsLocallyNoetherian scheme] :
    (boundedCoherentProperty scheme).IsStableUnderShift ℤ := by
  dsimp only [boundedCoherentProperty]
  infer_instance

theorem boundedCoherent_single [IsLocallyNoetherian scheme] (sheaf : CoherentSheaf scheme) :
    boundedCoherentProperty scheme
      ((DerivedCategory.singleFunctor scheme.Modules 0).obj sheaf.obj) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
  intro degree
  by_cases degreeZero : degree = 0
  · subst degree
    exact (coherentModuleProperty scheme).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso scheme.Modules 0).app
        sheaf.obj).symm sheaf.property
  · apply finitePresentation_of_isZero
    rcases lt_or_gt_of_ne degreeZero with negative | positive
    · exact (DerivedCategory.isGE_iff _ 0).mp inferInstance degree negative
    · exact (DerivedCategory.isLE_iff _ 0).mp inferInstance degree positive

instance [IsLocallyNoetherian scheme] :
    (boundedCoherentProperty scheme).ContainsZero where
  exists_zero := by
    let zeroSheaf : CoherentSheaf scheme :=
      ⟨SheafOfModules.free (R := scheme.ringCatSheaf) PEmpty.{schemeUniverse + 1},
        inferInstance⟩
    exact ⟨(DerivedCategory.singleFunctor scheme.Modules 0).obj zeroSheaf.obj,
      (DerivedCategory.singleFunctor scheme.Modules 0).map_isZero
        (isZero_freeEmpty scheme), boundedCoherent_single zeroSheaf⟩

end

end BondalThomsen
