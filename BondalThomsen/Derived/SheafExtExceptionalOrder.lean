module

public import BondalThomsen.Derived.LineBundleGenericComposition
public import BondalThomsen.Collection.SectionThree.Equivalences

@[expose] public section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

namespace BondalThomsen.SectionThree

universe schemeUniverse derivedUniverse derivedHomUniverse fieldUniverse

variable {Index : Type*} {Derived : Type derivedUniverse}
    [Category.{derivedHomUniverse} Derived] [Preadditive Derived] [HasShift Derived ℤ]
    {scheme : Scheme.{schemeUniverse}}
    {line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme}
    {objects : Index → Derived}

noncomputable def zeroShiftHomAddEquiv (source target : Derived) :
    (source ⟶ (shiftFunctor Derived (0 : ℤ)).obj target) ≃+ (source ⟶ target) where
  toFun morphism := morphism ≫ (shiftFunctorZero Derived ℤ).hom.app target
  invFun morphism := morphism ≫ (shiftFunctorZero Derived ℤ).inv.app target
  left_inv morphism := by simp [Category.assoc]
  right_inv morphism := by simp [Category.assoc]
  map_add' first second := by simp only [Preadditive.add_comp]

noncomputable def degreeZeroSheafHomAddEquiv
    (comparison : DerivedSheafExtComparison scheme line_bundles objects)
    (source target : Index) :
    ((line_bundles source).obj ⟶ (line_bundles target).obj) ≃+
      (objects source ⟶ objects target) :=
  Ext.addEquiv₀.symm.trans ((comparison.nonnegative source target 0).trans
    (zeroShiftHomAddEquiv (objects source) (objects target)))

theorem derivedNonvanishing_zero_iff_nonzeroHom
    (comparison : DerivedSheafExtComparison scheme line_bundles objects)
    (source target : Index) :
    derivedNonvanishing objects 0 source target ↔
      OrderingObstruction.NonzeroHom (fun index => (line_bundles index).obj) source target := by
  let equivalence := Ext.addEquiv₀.symm.trans (comparison.nonnegative source target 0)
  constructor
  · rintro ⟨morphism, nonzero⟩
    refine ⟨equivalence.symm morphism, ?_⟩
    exact equivalence.symm.map_ne_zero_iff.mpr nonzero
  · rintro ⟨morphism, nonzero⟩
    exact ⟨equivalence morphism, equivalence.map_ne_zero_iff.mpr nonzero⟩

theorem derivedNonvanishing_zero_isPartialOrder_of_isIntegral
    [IsIntegral scheme] (BaseField : Type fieldUniverse) [Field BaseField]
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (comparison : DerivedSheafExtComparison scheme line_bundles objects)
    (distinct_classes : Function.Injective (fun index =>
      TauCeti.AlgebraicGeometry.LineBundleClass.mk (line_bundles index))) :
    IsPartialOrder Index (derivedNonvanishing objects 0) := by
  have relation_eq : derivedNonvanishing objects 0 =
      OrderingObstruction.NonzeroHom (fun index => (line_bundles index).obj) := by
    funext source target
    exact propext (derivedNonvanishing_zero_iff_nonzeroHom comparison source target)
  rw [relation_eq]
  exact BondalThomsen.invertibleSheaf_nonzeroHom_isPartialOrder_of_isIntegral
    global_functions line_bundles distinct_classes

noncomputable def derivedEndAddEquivOfGlobalFunctions
    {BaseField : Type fieldUniverse} [Field BaseField]
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (comparison : DerivedSheafExtComparison scheme line_bundles objects)
    (index : Index) : BaseField ≃+ End (objects index) :=
  (global_functions.trans
    (Scheme.Modules.globalSectionsActionRingEquiv (line_bundles index).obj)).toAddEquiv.trans
      (degreeZeroSheafHomAddEquiv comparison index index)

def DerivedSheafScalarCompatibility (BaseField : Type fieldUniverse) [Field BaseField]
    [Linear BaseField Derived]
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (comparison : DerivedSheafExtComparison scheme line_bundles objects) : Prop :=
  ∀ index (scalar : BaseField),
    degreeZeroSheafHomAddEquiv comparison index index
      (Scheme.Modules.globalSectionsSmul (line_bundles index).obj (global_functions scalar)) =
        scalar • 𝟙 (objects index)

theorem derived_scalar_endomorphisms_bijective_of_globalFunctions
    (BaseField : Type fieldUniverse) [Field BaseField] [Linear BaseField Derived]
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (comparison : DerivedSheafExtComparison scheme line_bundles objects)
    (scalar_compatibility : DerivedSheafScalarCompatibility BaseField global_functions comparison)
    (index : Index) : Function.Bijective (fun scalar : BaseField => scalar • 𝟙 (objects index)) := by
  have scalar_map_eq : (fun scalar : BaseField => scalar • 𝟙 (objects index)) =
      derivedEndAddEquivOfGlobalFunctions global_functions comparison index := by
    funext scalar
    exact (scalar_compatibility index scalar).symm
  rw [scalar_map_eq]
  exact (derivedEndAddEquivOfGlobalFunctions global_functions comparison index).bijective

theorem derived_self_shiftedHom_subsingleton_of_positive_sheafExt
    (comparison : DerivedSheafExtComparison scheme line_bundles objects) (index : Index)
    (positive_self : ∀ degree, 0 < degree →
      Subsingleton (Ext (line_bundles index).obj (line_bundles index).obj degree))
    (degree : ℤ) (nonzero_degree : degree ≠ 0) :
    Subsingleton (objects index ⟶ (shiftFunctor Derived degree).obj (objects index)) := by
  by_cases negative : degree < 0
  · exact comparison.negative index index degree negative
  · have degree_eq : (degree.toNat : ℤ) = degree := Int.toNat_of_nonneg (by omega)
    rw [← degree_eq]
    let := positive_self degree.toNat (by omega)
    exact ⟨fun first second => (comparison.nonnegative index index degree.toNat).symm.injective
      (Subsingleton.elim _ _)⟩

theorem isExceptionalDerivedObject_of_positive_self_sheafExt
    (BaseField : Type fieldUniverse) [Field BaseField] [Linear BaseField Derived]
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (comparison : DerivedSheafExtComparison scheme line_bundles objects)
    (scalar_compatibility : DerivedSheafScalarCompatibility BaseField global_functions comparison)
    (index : Index)
    (positive_self : ∀ degree, 0 < degree →
      Subsingleton (Ext (line_bundles index).obj (line_bundles index).obj degree)) :
    IsExceptionalDerivedObject BaseField (objects index) :=
  ⟨derived_scalar_endomorphisms_bijective_of_globalFunctions BaseField global_functions comparison
      scalar_compatibility index,
    derived_self_shiftedHom_subsingleton_of_positive_sheafExt comparison index positive_self⟩

theorem exists_strongExceptionalOrdering_of_integral_sheafExt
    [Fintype Index] [IsIntegral scheme]
    (BaseField : Type fieldUniverse) [Field BaseField] [Linear BaseField Derived]
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (comparison : DerivedSheafExtComparison scheme line_bundles objects)
    (scalar_compatibility : DerivedSheafScalarCompatibility BaseField global_functions comparison)
    (distinct_classes : Function.Injective (fun index =>
      TauCeti.AlgebraicGeometry.LineBundleClass.mk (line_bundles index)))
    (positive : PositiveSheafExtVanishing scheme line_bundles) :
    ∃ numbering : Index ≃ Fin (Fintype.card Index),
      OrderingObstruction.IsStrongExceptionalOrdering
        (fun index => IsExceptionalDerivedObject BaseField (objects index))
        (derivedNonvanishing objects) numbering := by
  let := derivedNonvanishing_zero_isPartialOrder_of_isIntegral BaseField global_functions
    comparison distinct_classes
  exact OrderingObstruction.exists_strongExceptionalOrdering _ _
    (fun index => isExceptionalDerivedObject_of_positive_self_sheafExt BaseField
      global_functions comparison scalar_compatibility index (positive index index))
    (derived_strongVanishing_of_positive_sheafExt scheme line_bundles objects comparison positive)

end BondalThomsen.SectionThree
