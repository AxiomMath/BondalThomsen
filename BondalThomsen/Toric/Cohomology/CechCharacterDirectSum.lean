module

public import BondalThomsen.Toric.Cohomology.CechWeightDecomposition
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive
open scoped Classical DirectSum

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

noncomputable section

abbrev CechCharacterDirectSumDegree (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :=
  DirectSum (Lattice →+ ℤ) (fun character =>
    ↑(fan.primitiveComplementDegree 𝕜 complete regular (divisor + fan.principalRayDivisor character) degree))

def cechWeightDirectSumDegree (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (fan.CechCharacterDirectSumDegree 𝕜 complete regular divisor degree)

def cechWeightDirectSumDifferential (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    fan.cechWeightDirectSumDegree 𝕜 complete regular divisor degree ⟶
      fan.cechWeightDirectSumDegree 𝕜 complete regular divisor (degree + 1) :=
  AddCommGrpCat.ofHom (DirectSum.map
    (α := fun character => ↑(fan.primitiveComplementDegree 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree))
    (β := fun character => ↑(fan.primitiveComplementDegree 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) (degree + 1))) (fun character =>
    (fan.primitiveComplementDifferential 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree).hom))

theorem cechWeightDirectSumDifferential_squared (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    fan.cechWeightDirectSumDifferential 𝕜 complete regular divisor degree ≫
      fan.cechWeightDirectSumDifferential 𝕜 complete regular divisor (degree + 1) = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro element
  apply DirectSum.ext
  intro character
  simp only [cechWeightDirectSumDifferential, AddCommGrpCat.hom_comp,
    AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply, AddCommGrpCat.hom_zero,
    AddMonoidHom.zero_apply, DirectSum.zero_apply]
  exact ConcreteCategory.congr_hom
    (fan.primitiveComplementDifferential_squared 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree)
    (DirectSum.coeFnAddMonoidHom (fun character => ↑(fan.primitiveComplementDegree 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree)) element character)

def cechWeightDirectSumComplex (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of (fan.cechWeightDirectSumDegree 𝕜 complete regular divisor)
    (fan.cechWeightDirectSumDifferential 𝕜 complete regular divisor)
    (fan.cechWeightDirectSumDifferential_squared 𝕜 complete regular divisor)

def cechWeightDirectSumDegreeMap (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    fan.CechCharacterDirectSumDegree 𝕜 complete regular divisor degree →+
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree :=
  DirectSum.toAddMonoid
    (β := fun character => ↑(fan.primitiveComplementDegree 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree)) (fun character =>
    (fan.cechCharacterDegreeInclusion 𝕜 complete regular divisor character degree).hom)

theorem cechWeightDirectSumDegreeMap_of (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (character : Lattice →+ ℤ)
    (scalar : fan.primitiveComplementDegree 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree) :
    fan.cechWeightDirectSumDegreeMap 𝕜 complete regular divisor degree
      (DirectSum.of (fun character => ↑(fan.primitiveComplementDegree 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) degree)) character scalar) =
      fan.cechCharacterDegreeInclusion 𝕜 complete regular divisor character degree scalar := by
  exact DirectSum.toAddMonoid_of _ _ _

theorem cechWeightDirectSumDifferential_of (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (character : Lattice →+ ℤ)
    (scalar : fan.primitiveComplementDegree 𝕜 complete regular
      (divisor + fan.principalRayDivisor character) degree) :
    fan.cechWeightDirectSumDifferential 𝕜 complete regular divisor degree
      (DirectSum.of (fun character => ↑(fan.primitiveComplementDegree 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) degree)) character scalar) =
      DirectSum.of (fun character => ↑(fan.primitiveComplementDegree 𝕜 complete regular
        (divisor + fan.principalRayDivisor character) (degree + 1))) character
          (fan.primitiveComplementDifferential 𝕜 complete regular
            (divisor + fan.principalRayDivisor character) degree scalar) := by
  exact DirectSum.map_of _ _ _

theorem cechWeightDirectSumDegreeMap_retraction (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (character : Lattice →+ ℤ)
    (element : fan.CechCharacterDirectSumDegree 𝕜 complete regular divisor degree) :
    fan.cechCharacterDegreeRetraction 𝕜 complete regular divisor character degree
      (fan.cechWeightDirectSumDegreeMap 𝕜 complete regular divisor degree element) = element character := by
  induction element using DirectSum.induction_on with
  | zero => simp only [map_zero, DirectSum.zero_apply]
  | of other scalar =>
    simp only [cechWeightDirectSumDegreeMap, DirectSum.of_apply]
    rw [DirectSum.toAddMonoid_of]
    by_cases same : other = character
    · subst other
      simpa using ConcreteCategory.congr_hom
        (fan.cechCharacterDegree_split 𝕜 complete regular divisor character degree) scalar
    · simp only [dite_eq_right same]
      exact ConcreteCategory.congr_hom
        (fan.cechCharacterDegree_other 𝕜 complete regular divisor other character same degree) scalar
  | add first second first_eq second_eq =>
    simp only [map_add, DirectSum.add_apply, first_eq, second_eq]

theorem cechWeightDirectSumDegreeMap_sum_support (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) (element : (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree) :
    fan.cechWeightDirectSumDegreeMap 𝕜 complete regular divisor degree
      (∑ character ∈ fan.cechDegreeCharacterSupport 𝕜 complete regular divisor degree element,
      DirectSum.of (fun character =>
        ↑(fan.primitiveComplementDegree 𝕜 complete regular
          (divisor + fan.principalRayDivisor character) degree)) character
            (fan.cechCharacterDegreeRetraction 𝕜 complete regular divisor character degree element)) = element := by
  rw [map_sum]
  calc
    _ = ∑ character ∈ fan.cechDegreeCharacterSupport 𝕜 complete regular divisor degree element,
        (fan.cechCharacterChainProjector 𝕜 complete regular divisor character).f degree element := by
      apply Finset.sum_congr rfl
      intro character supported
      rw [fan.cechWeightDirectSumDegreeMap_of 𝕜]
      rfl
    _ = element := fan.cechCharacterChainProjector_sum_support 𝕜 complete regular divisor degree element

theorem cechWeightDirectSumDegreeMap_bijective (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    Function.Bijective (fan.cechWeightDirectSumDegreeMap 𝕜 complete regular divisor degree) := by
  constructor
  · intro first second same
    apply DirectSum.ext
    intro character
    rw [← fan.cechWeightDirectSumDegreeMap_retraction 𝕜 complete regular divisor degree character first,
      ← fan.cechWeightDirectSumDegreeMap_retraction 𝕜 complete regular divisor degree character second, same]
  · intro element
    exact ⟨_, fan.cechWeightDirectSumDegreeMap_sum_support 𝕜 complete regular divisor degree element⟩

def cechWeightDirectSumDegreeEquiv (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    fan.cechWeightDirectSumDegree 𝕜 complete regular divisor degree ≃+
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).X degree :=
  AddEquiv.ofBijective (fan.cechWeightDirectSumDegreeMap 𝕜 complete regular divisor degree)
    (fan.cechWeightDirectSumDegreeMap_bijective 𝕜 complete regular divisor degree)

theorem cechWeightDirectSumDegreeMap_d (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    AddCommGrpCat.ofHom (fan.cechWeightDirectSumDegreeMap 𝕜 complete regular divisor degree) ≫
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).d degree (degree + 1) =
      fan.cechWeightDirectSumDifferential 𝕜 complete regular divisor degree ≫
        AddCommGrpCat.ofHom (fan.cechWeightDirectSumDegreeMap 𝕜 complete regular divisor (degree + 1)) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro element
  induction element using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of character scalar =>
    change (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).d degree (degree + 1)
        (fan.cechWeightDirectSumDegreeMap 𝕜 complete regular divisor degree
          (DirectSum.of _ character scalar)) =
      fan.cechWeightDirectSumDegreeMap 𝕜 complete regular divisor (degree + 1)
        (fan.cechWeightDirectSumDifferential 𝕜 complete regular divisor degree
          (DirectSum.of _ character scalar))
    rw [fan.cechWeightDirectSumDegreeMap_of 𝕜, fan.cechWeightDirectSumDifferential_of 𝕜,
      fan.cechWeightDirectSumDegreeMap_of 𝕜]
    exact ConcreteCategory.congr_hom
      (fan.cechCharacterDegreeInclusion_d 𝕜 complete regular divisor character degree) scalar
  | add first second first_eq second_eq =>
    simp only [map_add, first_eq, second_eq]

def cechWeightDirectSumIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor) :
    fan.cechWeightDirectSumComplex 𝕜 complete regular divisor ≅
      fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor :=
  HomologicalComplex.Hom.isoOfComponents
    (fun degree => (fan.cechWeightDirectSumDegreeEquiv 𝕜 complete regular divisor degree).toAddCommGrpIso)
    (fun degree next related => by
      change degree + 1 = next at related
      subst next
      have hom_eq : ∀ stage,
          (fan.cechWeightDirectSumDegreeEquiv 𝕜 complete regular divisor stage).toAddCommGrpIso.hom =
            AddCommGrpCat.ofHom (fan.cechWeightDirectSumDegreeMap 𝕜 complete regular divisor stage) := by
        intro stage
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro element
        rfl
      rw [hom_eq, hom_eq]
      rw [show (fan.cechWeightDirectSumComplex 𝕜 complete regular divisor).d degree (degree + 1) =
        fan.cechWeightDirectSumDifferential 𝕜 complete regular divisor degree by
          exact CochainComplex.of_d _ _ degree]
      exact fan.cechWeightDirectSumDegreeMap_d 𝕜 complete regular divisor degree)

def cechWeightDirectSumHomologyIso (fan : Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular) (divisor : fan.InvariantRayDivisor)
    (degree : ℕ) :
    (fan.cechWeightDirectSumComplex 𝕜 complete regular divisor).homology degree ≅
      (fan.primitiveWeightZeroCechComplex 𝕜 complete regular divisor).homology degree :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).mapIso
    (fan.cechWeightDirectSumIso 𝕜 complete regular divisor)

end

end TauCeti.Toric.Fan
