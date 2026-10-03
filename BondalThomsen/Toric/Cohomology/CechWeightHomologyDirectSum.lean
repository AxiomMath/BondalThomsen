module

public import BondalThomsen.Toric.Cohomology.CechCharacterDirectSum
public import BondalThomsen.Toric.Cohomology.PrimitiveBoundaryDerivedCohomology
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.Functor

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical DirectSum

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.ToricCechWeightHomologyDirectSum

noncomputable section

variable {Index : Type}

def directSumFunctor : (Discrete Index ⥤ AddCommGrpCat.{0}) ⥤ AddCommGrpCat.{0} where
  obj family := AddCommGrpCat.of (DirectSum Index (fun index => ↑(family.obj ⟨index⟩)))
  map transformation := AddCommGrpCat.ofHom (DirectSum.map
    (fun index => (transformation.app ⟨index⟩).hom))
  map_id family := by
    apply AddCommGrpCat.hom_ext
    exact DirectSum.map_id
  map_comp first second := by
    apply AddCommGrpCat.hom_ext
    exact DirectSum.map_comp _ _

def directSumCocone (family : Discrete Index ⥤ AddCommGrpCat.{0}) : Cocone family where
  pt := directSumFunctor.obj family
  ι := Discrete.natTrans (fun index =>
    AddCommGrpCat.ofHom (DirectSum.of (fun index => ↑(family.obj ⟨index⟩)) index.as))

def directSumCoconeIsColimit (family : Discrete Index ⥤ AddCommGrpCat.{0}) :
    IsColimit (directSumCocone family) where
  desc cocone := AddCommGrpCat.ofHom (DirectSum.toAddMonoid
    (β := fun index => ↑(family.obj ⟨index⟩)) (fun index => (cocone.ι.app ⟨index⟩).hom))
  fac cocone index := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro element
    exact DirectSum.toAddMonoid_of (β := fun index => ↑(family.obj ⟨index⟩)) (γ := ↑cocone.pt)
      (fun index => (cocone.ι.app ⟨index⟩).hom) index.as element
  uniq cocone morphism compatible := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro index element
    exact (ConcreteCategory.congr_hom (compatible ⟨index⟩) element).trans
      (DirectSum.toAddMonoid_of (β := fun index => ↑(family.obj ⟨index⟩)) (γ := ↑cocone.pt)
        (fun index => (cocone.ι.app ⟨index⟩).hom) index element).symm

def directSumColimitIso (family : Discrete Index ⥤ AddCommGrpCat.{0}) :
    directSumFunctor.obj family ≅ colimit family :=
    (directSumCoconeIsColimit family).coconePointUniqueUpToIso
      (colimit.isColimit family)

theorem directSumColimitIso_inclusion (family : Discrete Index ⥤ AddCommGrpCat.{0}) (index : Index) :
    AddCommGrpCat.ofHom (DirectSum.of (fun index => ↑(family.obj ⟨index⟩)) index) ≫
      (directSumColimitIso family).hom = colimit.ι family ⟨index⟩ := by
  exact (directSumCoconeIsColimit family).fac (colimit.cocone family) ⟨index⟩

theorem directSumFunctor_map_of {source target : Discrete Index ⥤ AddCommGrpCat.{0}}
    (transformation : source ⟶ target) (index : Index) :
    AddCommGrpCat.ofHom (DirectSum.of (fun index => ↑(source.obj ⟨index⟩)) index) ≫
      directSumFunctor.map transformation = transformation.app ⟨index⟩ ≫
        AddCommGrpCat.ofHom (DirectSum.of (fun index => ↑(target.obj ⟨index⟩)) index) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro element
  exact DirectSum.map_of _ _ _

def directSumFunctorIsoColim :
    directSumFunctor (Index := Index) ≅ colim :=
  NatIso.ofComponents directSumColimitIso (by
    intro source target transformation
    apply (directSumCoconeIsColimit source).hom_ext
    intro index
    change AddCommGrpCat.ofHom (DirectSum.of _ index.as) ≫
        directSumFunctor.map transformation ≫ (directSumColimitIso target).hom =
      AddCommGrpCat.ofHom (DirectSum.of _ index.as) ≫
        (directSumColimitIso source).hom ≫ colim.map transformation
    rw [← Category.assoc, directSumFunctor_map_of, Category.assoc,
      directSumColimitIso_inclusion, ← Category.assoc,
      directSumColimitIso_inclusion, colimit.ι_map])

local instance directSumFunctorAdditive : (directSumFunctor (Index := Index)).Additive :=
  Functor.additive_of_iso directSumFunctorIsoColim.symm

local instance directSumFunctorPreservesFiniteLimits :
    PreservesFiniteLimits (directSumFunctor (Index := Index)) :=
  preservesFiniteLimits_of_natIso directSumFunctorIsoColim.symm

local instance directSumFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (directSumFunctor (Index := Index)) :=
  preservesFiniteColimits_of_natIso directSumFunctorIsoColim.symm

local instance directSumFunctorPreservesHomology :
    (directSumFunctor (Index := Index)).PreservesHomology := inferInstance

def familyComplex (family : Index → CochainComplex AddCommGrpCat.{0} ℕ) :
    CochainComplex (Discrete Index ⥤ AddCommGrpCat.{0}) ℕ where
  X degree := Discrete.functor (fun index => (family index).X degree)
  d degree next := Discrete.natTrans (fun index => (family index.as).d degree next)
  shape degree next unrelated := by
    ext index element
    exact ConcreteCategory.congr_hom ((family index.as).shape degree next unrelated) element
  d_comp_d' first second third relatedFirst relatedSecond := by
    ext index element
    exact ConcreteCategory.congr_hom ((family index.as).d_comp_d first second third) element

def familyComplexEvaluationIso (family : Index → CochainComplex AddCommGrpCat.{0} ℕ)
    (index : Index) :
    (((evaluation (Discrete Index) AddCommGrpCat).obj ⟨index⟩).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (familyComplex family) ≅ family index :=
  HomologicalComplex.Hom.isoOfComponents (fun degree => Iso.refl _)
    (fun degree next related => by simp [familyComplex])

def familyComplexHomologyIso (family : Index → CochainComplex AddCommGrpCat.{0} ℕ)
    (degree : ℕ) :
    (familyComplex family).homology degree ≅
      Discrete.functor (fun index => (family index).homology degree) :=
  Discrete.natIso (fun index =>
    (((familyComplex family).sc degree).mapHomologyIso
      ((evaluation (Discrete Index) AddCommGrpCat).obj index)).symm ≪≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).mapIso
          (familyComplexEvaluationIso family index.as))

def directSumFamilyComplexHomologyIso (family : Index → CochainComplex AddCommGrpCat.{0} ℕ)
    (degree : ℕ) :
    ((directSumFunctor.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (familyComplex family)).homology degree ≅
        AddCommGrpCat.of (DirectSum Index (fun index => ↑((family index).homology degree))) :=
  ((familyComplex family).sc degree).mapHomologyIso directSumFunctor ≪≫
    directSumFunctor.mapIso (familyComplexHomologyIso family degree)

end

end BondalThomsen.ToricCechWeightHomologyDirectSum

namespace TauCeti.Toric.Fan

open BondalThomsen.ToricCechWeightHomologyDirectSum

attribute [local instance] directSumFunctorAdditive directSumFunctorPreservesFiniteLimits
  directSumFunctorPreservesFiniteColimits directSumFunctorPreservesHomology

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable section

def cechCharacterFamilyComplex (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    CochainComplex (Discrete (Lattice →+ ℤ) ⥤ AddCommGrpCat.{0}) ℕ :=
  familyComplex (fun character => fan.primitiveComplementComplex 𝕜 complete regular
    (divisor + fan.principalRayDivisor character))

def cechCharacterFamilyDirectSumIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    ((directSumFunctor.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (fan.cechCharacterFamilyComplex 𝕜 complete regular divisor)) ≅
        fan.cechWeightDirectSumComplex 𝕜 complete regular divisor :=
  HomologicalComplex.Hom.isoOfComponents (fun degree => Iso.refl _)
    (fun degree next related => by
      change degree + 1 = next at related
      subst next
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rw [show (fan.cechWeightDirectSumComplex 𝕜 complete regular divisor).d degree (degree + 1) =
        fan.cechWeightDirectSumDifferential 𝕜 complete regular divisor degree by
          exact CochainComplex.of_d _ _ degree]
      change fan.cechWeightDirectSumDifferential 𝕜 complete regular divisor degree
          = AddCommGrpCat.ofHom (DirectSum.map (fun character =>
          ((fan.primitiveComplementComplex 𝕜 complete regular
            (divisor + fan.principalRayDivisor character)).d degree (degree + 1)).hom))
      simp only [primitiveComplementComplex, CochainComplex.of_d]
      rfl)

def cechWeightHomologyDirectSumIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    (fan.cechWeightDirectSumComplex 𝕜 complete regular divisor).homology degree ≅
      AddCommGrpCat.of (DirectSum (Lattice →+ ℤ) (fun character =>
        ↑((fan.primitiveComplementComplex 𝕜 complete regular
          (divisor + fan.principalRayDivisor character)).homology degree))) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).mapIso
    (fan.cechCharacterFamilyDirectSumIso 𝕜 complete regular divisor).symm ≪≫
      directSumFamilyComplexHomologyIso (fun character =>
        fan.primitiveComplementComplex 𝕜 complete regular (divisor + fan.principalRayDivisor character)) degree

def cechCharacterHomologyDirectSumIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).homology degree ≅
      AddCommGrpCat.of (DirectSum (Lattice →+ ℤ) (fun character =>
        ↑((fan.primitiveComplementComplex 𝕜 complete regular
          (divisor + fan.principalRayDivisor character)).homology degree))) :=
  (fan.cechWeightDirectSumHomologyIso 𝕜 complete regular divisor degree).symm ≪≫
    fan.cechWeightHomologyDirectSumIso 𝕜 complete regular divisor degree

def invariantDivisorCohomologyWeightDirectSumIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    AddCommGrpCat.of (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj degree) ≅
        AddCommGrpCat.of (DirectSum (Lattice →+ ℤ) (fun character =>
          ↑((fan.primitiveComplementComplex 𝕜 complete regular
            (divisor + fan.principalRayDivisor character)).homology degree))) :=
  fan.primitiveWeightZeroCechCohomologyIso 𝕜 complete regular divisor degree ≪≫
    fan.cechCharacterHomologyDirectSumIso 𝕜 complete regular divisor degree

def invariantDivisorCohomologyWeightDirectSumEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (fan.invariantDivisorLineBundle 𝕜 complete regular divisor).obj degree ≃+
        DirectSum (Lattice →+ ℤ) (fun character =>
          ↑((fan.primitiveComplementComplex 𝕜 complete regular
            (divisor + fan.principalRayDivisor character)).homology degree)) :=
  (fan.invariantDivisorCohomologyWeightDirectSumIso 𝕜 complete regular divisor degree).addCommGroupIsoToAddEquiv

end

end TauCeti.Toric.Fan
