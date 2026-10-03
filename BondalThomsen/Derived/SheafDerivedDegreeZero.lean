module

public import BondalThomsen.Derived.SheafExtExceptionalOrder
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Linear.LinearFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

namespace BondalThomsen.SheafDerivedDegreeZero

universe schemeUniverse sourceUniverse sourceHomUniverse targetUniverse targetHomUniverse
    scalarUniverse derivedUniverse

section SheafScalarAction

variable {scheme : Scheme.{schemeUniverse}} {Scalar : Type scalarUniverse} [CommRing Scalar]

@[instance_reducible] noncomputable def globalFunctionHomModule
    (scalar_map : Scalar →+* Γ(scheme, ⊤))
    (source target : scheme.Modules) : Module Scalar (source ⟶ target) := by
  letI : SMul Scalar (source ⟶ target) :=
    ⟨fun scalar morphism => Scheme.Modules.globalSectionsSmul source (scalar_map scalar) ≫ morphism⟩
  apply Module.ofMinimalAxioms
  · intro scalar first second
    change Scheme.Modules.globalSectionsSmul source (scalar_map scalar) ≫ (first + second) =
      Scheme.Modules.globalSectionsSmul source (scalar_map scalar) ≫ first +
        Scheme.Modules.globalSectionsSmul source (scalar_map scalar) ≫ second
    exact Preadditive.comp_add source source target
      (Scheme.Modules.globalSectionsSmul source (scalar_map scalar)) first second
  · intro first second morphism
    change Scheme.Modules.globalSectionsSmul source (scalar_map (first + second)) ≫ morphism = _
    simp only [map_add, Scheme.Modules.globalSectionsSmul_add, Preadditive.add_comp]
    rfl
  · intro first second morphism
    change Scheme.Modules.globalSectionsSmul source (scalar_map (first * second)) ≫ morphism =
      Scheme.Modules.globalSectionsSmul source (scalar_map first) ≫
        (Scheme.Modules.globalSectionsSmul source (scalar_map second) ≫ morphism)
    rw [map_mul, mul_comm, Scheme.Modules.globalSectionsSmul_mul, Category.assoc]
  · intro morphism
    change Scheme.Modules.globalSectionsSmul source (scalar_map 1) ≫ morphism = morphism
    simp

@[instance_reducible] noncomputable def sheafModulesLinear
    (scalar_map : Scalar →+* Γ(scheme, ⊤)) :
    Linear Scalar scheme.Modules where
  homModule := globalFunctionHomModule scalar_map
  smul_comp := fun source middle target scalar first second => by
    change (Scheme.Modules.globalSectionsSmul source (scalar_map scalar) ≫ first) ≫ second =
      Scheme.Modules.globalSectionsSmul source (scalar_map scalar) ≫ (first ≫ second)
    exact Category.assoc _ _ _
  comp_smul := fun source middle target first scalar second => by
    change first ≫ (Scheme.Modules.globalSectionsSmul middle (scalar_map scalar) ≫ second) =
      Scheme.Modules.globalSectionsSmul source (scalar_map scalar) ≫ (first ≫ second)
    rw [← Category.assoc, ← Scheme.Modules.globalSectionsSmul_naturality, Category.assoc]

theorem sheafModulesLinear_scalar_identity (scalar_map : Scalar →+* Γ(scheme, ⊤))
    (object : scheme.Modules) (scalar : Scalar) :
    letI := sheafModulesLinear scalar_map
    scalar • 𝟙 object = Scheme.Modules.globalSectionsSmul object (scalar_map scalar) := by
  change Scheme.Modules.globalSectionsSmul object (scalar_map scalar) ≫ 𝟙 object = _
  exact Category.comp_id _

end SheafScalarAction

section InvertibleSheafTransport

variable {scheme : Scheme.{schemeUniverse}}
    {BaseField : Type scalarUniverse} [Field BaseField]

variable {Target : Type targetUniverse} [Category.{targetHomUniverse} Target]
    [Preadditive Target]

variable [Linear BaseField Target]

theorem embedding_map_globalSectionsSmul
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (embedding : scheme.Modules ⥤ Target)
    (linear_embedding : letI := sheafModulesLinear global_functions.toRingHom
      embedding.Linear BaseField)
    (object : scheme.Modules) (scalar : BaseField) :
    embedding.map (Scheme.Modules.globalSectionsSmul object (global_functions scalar)) =
      scalar • 𝟙 (embedding.obj object) := by
  let := sheafModulesLinear global_functions.toRingHom
  let := linear_embedding
  change embedding.map
    (Scheme.Modules.globalSectionsSmul object (global_functions.toRingHom scalar)) = _
  rw [← sheafModulesLinear_scalar_identity global_functions.toRingHom object scalar]
  simp

end InvertibleSheafTransport

section CanonicalDerivedEmbedding

variable {scheme : Scheme.{schemeUniverse}} {BaseField : Type scalarUniverse} [Field BaseField]
    [HasDerivedCategory.{derivedUniverse} scheme.Modules]

theorem canonicalDerived_negative_shiftedHom_subsingleton (source target : scheme.Modules)
    (degree : ℤ) (negative : degree < 0) :
    Subsingleton ((DerivedCategory.singleFunctor scheme.Modules 0).obj source ⟶
      (shiftFunctor (DerivedCategory scheme.Modules) degree).obj
        ((DerivedCategory.singleFunctor scheme.Modules 0).obj target)) := by
  let canonical_t := @DerivedCategory.TStructure.t scheme.Modules _ _ _
  let target_image := (DerivedCategory.singleFunctor scheme.Modules 0).obj target
  have : canonical_t.IsGE ((shiftFunctor (DerivedCategory scheme.Modules) degree).obj
      target_image) (-degree) :=
    canonical_t.isGE_shift target_image 0 degree (-degree) (by omega)
  exact ⟨fun first second => (canonical_t.zero first 0 (-degree) (by omega)).trans
    (canonical_t.zero second 0 (-degree) (by omega)).symm⟩

noncomputable def canonicalDerivedSheafExtComparison {Index : Type*}
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    BondalThomsen.SectionThree.DerivedSheafExtComparison scheme line_bundles
      (fun index => (DerivedCategory.singleFunctor scheme.Modules 0).obj
        (line_bundles index).obj) where
  nonnegative := fun _ _ _ => Ext.homAddEquiv
  negative := fun source target degree negative =>
    canonicalDerived_negative_shiftedHom_subsingleton (line_bundles source).obj
      (line_bundles target).obj degree negative

noncomputable def canonicalExtZeroHomAddEquiv (source target : scheme.Modules) :
    (source ⟶ target) ≃+ ((DerivedCategory.singleFunctor scheme.Modules 0).obj source ⟶
      (DerivedCategory.singleFunctor scheme.Modules 0).obj target) :=
  Ext.addEquiv₀.symm.trans (Ext.homAddEquiv.trans
    (BondalThomsen.SectionThree.zeroShiftHomAddEquiv
      ((DerivedCategory.singleFunctor scheme.Modules 0).obj source)
      ((DerivedCategory.singleFunctor scheme.Modules 0).obj target)))

@[simp] theorem canonicalExtZeroHomAddEquiv_apply (source target : scheme.Modules)
    (morphism : source ⟶ target) :
    canonicalExtZeroHomAddEquiv source target morphism =
      (DerivedCategory.singleFunctor scheme.Modules 0).map morphism := by
  change (Ext.mk₀ morphism).hom ≫
    (shiftFunctorZero (DerivedCategory scheme.Modules) ℤ).hom.app
      ((DerivedCategory.singleFunctor scheme.Modules 0).obj target) = _
  rw [Ext.mk₀_hom]
  simp [ShiftedHom.mk₀, shiftFunctorZero']

theorem canonicalExtZeroHomAddEquiv_scalar
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (object : scheme.Modules) (scalar : BaseField) :
    letI := sheafModulesLinear global_functions.toRingHom
    canonicalExtZeroHomAddEquiv object object
      (Scheme.Modules.globalSectionsSmul object (global_functions scalar)) =
      scalar • 𝟙 ((DerivedCategory.singleFunctor scheme.Modules 0).obj object) := by
  let := sheafModulesLinear global_functions.toRingHom
  rw [canonicalExtZeroHomAddEquiv_apply]
  exact embedding_map_globalSectionsSmul global_functions
    (DerivedCategory.singleFunctor scheme.Modules 0) (by infer_instance) object scalar

theorem canonicalDerivedSheafScalarCompatibility {Index : Type*}
    (global_functions : BaseField ≃+* Γ(scheme, ⊤))
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    letI := sheafModulesLinear global_functions.toRingHom
    BondalThomsen.SectionThree.DerivedSheafScalarCompatibility BaseField global_functions
      (canonicalDerivedSheafExtComparison line_bundles) := by
  let := sheafModulesLinear global_functions.toRingHom
  intro index scalar
  change canonicalExtZeroHomAddEquiv (line_bundles index).obj (line_bundles index).obj
    (Scheme.Modules.globalSectionsSmul (line_bundles index).obj (global_functions scalar)) = _
  exact canonicalExtZeroHomAddEquiv_scalar global_functions (line_bundles index).obj scalar

end CanonicalDerivedEmbedding

end BondalThomsen.SheafDerivedDegreeZero
