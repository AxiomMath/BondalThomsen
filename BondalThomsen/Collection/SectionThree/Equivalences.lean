module

public import BondalThomsen.DeepFan.CriterionForward
public import BondalThomsen.Derived.LineBundleGenericComposition
public import Mathlib.CategoryTheory.Triangulated.Generators

@[expose] public section

open Module Finset CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

namespace BondalThomsen

open TauCeti.Toric.Fan

universe schemeUniverse

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

def PrimitiveFloorPairSheafComparison (fan : TauCeti.Toric.Fan embedding)
    (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (realization : fan.InvariantRayDivisorClass → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) :
    Prop := by
  classical
  exact ∀ left : Finset fan.Ray, fan.IsPrimitiveCollection left →
    ∀ pairing moved : Lattice →+ ℚ,
      fan.floorRayDivisor moved - fan.floorRayDivisor pairing =
        fan.invariantDivisorOfCoefficients (fun ray => if ray ∈ left then -1 else 0) →
      (∃ morphism : (realization (fan.floorRayDivisorClass moved)).obj ⟶
          (realization (fan.floorRayDivisorClass pairing)).obj, morphism ≠ 0) ∧
      (∃ extension : Ext (realization (fan.floorRayDivisorClass pairing)).obj
          (realization (fan.floorRayDivisorClass moved)).obj (left.card - 1), extension ≠ 0)

def ToricFanoExtremalSupport (fan : TauCeti.Toric.Fan embedding) (dimension : ℕ)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop) :
    Prop :=
  ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
    extremal left right relation →
      ∃ drop_one : ∀ primitive : left, PrimitiveRelationConeBasis relation primitive dimension,
        (∑ ray : right, relation.coefficients ray : ℕ) < Fintype.card left ∧
        ∀ primitive : left, ∀ ray : fan.Ray,
          ray.val ∉ Set.range (drop_one primitive).basis →
            (-1 : ℚ) < (drop_one primitive).anticanonicalDatum ray.val

theorem small_extremal_of_sheafExt_backward_ordering
    (fan : TauCeti.Toric.Fan embedding) [Fintype fan.BondalThomsenClass]
    (complete : fan.IsComplete) (dimension : ℕ)
    (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (realization : fan.InvariantRayDivisorClass → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (extremal : ∀ left right : Finset fan.Ray, fan.PrimitiveLatticeRelation left right → Prop)
    (fano_support : ToricFanoExtremalSupport fan dimension extremal)
    (comparison : PrimitiveFloorPairSheafComparison fan scheme realization)
    (ordering : ∃ numbering : fan.BondalThomsenClass ≃ Fin (Fintype.card fan.BondalThomsenClass),
      ∀ source target, numbering target < numbering source →
        ∀ degree (extension : Ext (realization source.val).obj (realization target.val).obj degree),
          extension = 0) :
    ∀ left right (relation : fan.PrimitiveLatticeRelation left right),
      extremal left right relation → ∑ ray : right, relation.coefficients ray ≤ 1 := by
  classical
  intro left right relation is_extremal
  by_contra not_small
  have large : 2 ≤ ∑ ray : right, relation.coefficients ray := by omega
  obtain ⟨drop_one, degree_positive, support⟩ := fano_support left right relation is_extremal
  obtain ⟨distinguished, pairing, parameter, _, _, _, _, difference, different⟩ :=
    relation.exists_two_distinct_floorClasses_of_dropOne_support complete drop_one large
      degree_positive support
  obtain ⟨⟨morphism, morphism_nonzero⟩, ⟨extension, extension_nonzero⟩⟩ :=
    comparison left relation.primitive_collection pairing
      (pairing + parameter • (drop_one distinguished).badDirection) difference
  let first := fan.bondalThomsenClassOfPairing pairing
  let second := fan.bondalThomsenClassOfPairing
    (pairing + parameter • (drop_one distinguished).badDirection)
  have distinct : second ≠ first := by
    intro same
    exact different (congrArg Subtype.val same)
  exact sheafExt_two_cycle_obstructs_ordering scheme
    (fun member : fan.BondalThomsenClass => (realization member.val).obj)
    distinct morphism morphism_nonzero (left.card - 1) extension extension_nonzero ordering

end BondalThomsen

namespace BondalThomsen.SectionThree

universe schemeUniverse derivedUniverse derivedHomUniverse fieldUniverse

open TauCeti.Toric.Fan

variable {Index : Type*} {Derived : Type derivedUniverse}
    [Category.{derivedHomUniverse} Derived] [Preadditive Derived] [HasShift Derived ℤ]

def IsExceptionalDerivedObject (BaseField : Type fieldUniverse) [Field BaseField]
    [Linear BaseField Derived] (object : Derived) : Prop :=
  Function.Bijective (fun scalar : BaseField => scalar • 𝟙 object) ∧
    ∀ degree : ℤ, degree ≠ 0 →
      Subsingleton (object ⟶ (shiftFunctor Derived degree).obj object)

def derivedNonvanishing (objects : Index → Derived) (degree : ℤ) (source target : Index) : Prop :=
  ∃ morphism : objects source ⟶ (shiftFunctor Derived degree).obj (objects target), morphism ≠ 0

structure DerivedSheafExtComparison
    (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (objects : Index → Derived) where
  nonnegative : ∀ (source target : Index) (degree : ℕ),
    Ext (line_bundles source).obj (line_bundles target).obj degree ≃+
      (objects source ⟶ (shiftFunctor Derived (degree : ℤ)).obj (objects target))
  negative : ∀ (source target : Index) (degree : ℤ), degree < 0 →
    Subsingleton (objects source ⟶ (shiftFunctor Derived degree).obj (objects target))

def PositiveSheafExtVanishing (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme) : Prop :=
  ∀ source target degree, 0 < degree →
    Subsingleton (Ext (line_bundles source).obj (line_bundles target).obj degree)

theorem derived_strongVanishing_of_positive_sheafExt
    (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (objects : Index → Derived) (comparison : DerivedSheafExtComparison scheme line_bundles objects)
    (positive : PositiveSheafExtVanishing scheme line_bundles) :
    OrderingObstruction.IsStrongVanishing (derivedNonvanishing objects) := by
  intro degree nonzero source target
  rintro ⟨morphism, morphism_nonzero⟩
  by_cases negative_degree : degree < 0
  · let := comparison.negative source target degree negative_degree
    exact morphism_nonzero (Subsingleton.elim _ _)
  · have degree_eq : (degree.toNat : ℤ) = degree := Int.toNat_of_nonneg (by omega)
    have positive_degree : 0 < degree.toNat := by omega
    have vanished : Subsingleton
        (objects source ⟶ (shiftFunctor Derived degree).obj (objects target)) := by
      rw [← degree_eq]
      let := positive source target degree.toNat positive_degree
      refine ⟨fun first second => ?_⟩
      apply (comparison.nonnegative source target degree.toNat).symm.injective
      exact Subsingleton.elim _ _
    let := vanished
    exact morphism_nonzero (Subsingleton.elim _ _)

theorem sheafExt_backward_of_derivedExceptionalOrdering [Fintype Index]
    (BaseField : Type fieldUniverse) [Field BaseField] [Linear BaseField Derived]
    (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (objects : Index → Derived) (comparison : DerivedSheafExtComparison scheme line_bundles objects)
    (numbering : Index ≃ Fin (Fintype.card Index))
    (ordering : OrderingObstruction.IsExceptionalOrdering
      (fun index => IsExceptionalDerivedObject BaseField (objects index))
      (derivedNonvanishing objects) numbering) :
    ∀ source target, numbering target < numbering source →
      ∀ degree (extension : Ext (line_bundles source).obj (line_bundles target).obj degree),
        extension = 0 := by
  intro source target backward degree extension
  apply (comparison.nonnegative source target degree).injective
  rw [map_zero]
  by_contra nonzero
  exact ordering.2 source target backward (degree : ℤ) ⟨_, nonzero⟩

theorem positive_sheafExt_of_derived_strongVanishing
    (scheme : AlgebraicGeometry.Scheme.{schemeUniverse})
    (line_bundles : Index → TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (objects : Index → Derived) (comparison : DerivedSheafExtComparison scheme line_bundles objects)
    (strong : OrderingObstruction.IsStrongVanishing (derivedNonvanishing objects)) :
    PositiveSheafExtVanishing scheme line_bundles := by
  intro source target degree degree_positive
  refine ⟨fun first second => ?_⟩
  have mapped_zero : ∀ extension : Ext (line_bundles source).obj (line_bundles target).obj degree,
      comparison.nonnegative source target degree extension = 0 := by
    intro extension
    by_contra nonzero
    exact strong (degree : ℤ) (by omega) source target ⟨_, nonzero⟩
  apply (comparison.nonnegative source target degree).injective
  rw [mapped_zero, mapped_zero]

end BondalThomsen.SectionThree
