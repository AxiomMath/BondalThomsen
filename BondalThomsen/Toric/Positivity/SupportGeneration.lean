module

public import BondalThomsen.Toric.Positivity.SupportConcavity
public import BondalThomsen.Toric.Scheme.TransitionUnits
public import BondalThomsen.Fan.CompleteFanCharacters
public import Mathlib.Algebra.MonoidAlgebra.Module

@[expose] public section

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

open Set Module Multiplicative TauCeti.Toric

variable {Lattice Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def characterLaurentMonomial (fan : Fan embedding)
    (character : Lattice →+ ℤ) : fan.LaurentCharacterAlgebra 𝕜 :=
  MonoidAlgebra.single (ofAdd character) 1

noncomputable def coneCharacterSectionMap (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ) :
    affineCoordinateRing 𝕜 fan.lattice cone →ₗ[𝕜] (fan.LaurentCharacterAlgebra 𝕜) :=
  MonoidAlgebra.mapDomainLinearMap 𝕜 𝕜
    (fun exponent : Multiplicative (dualSemigroup fan.lattice cone) =>
      ofAdd (character + (toAdd exponent).val))

@[simp] theorem coneCharacterSectionMap_single (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (exponent : dualSemigroup fan.lattice cone) (coefficient : 𝕜) :
    fan.coneCharacterSectionMap 𝕜 cone character
      (MonoidAlgebra.single (ofAdd exponent) coefficient) =
        MonoidAlgebra.single (ofAdd (character + (exponent : Lattice →+ ℤ))) coefficient := by
  exact MonoidAlgebra.mapDomainLinearMap_single _ _ _

theorem coneCharacterSectionMap_injective (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ) :
    Function.Injective (fan.coneCharacterSectionMap 𝕜 cone character) := by
  apply MonoidAlgebra.mapDomain_injective
  intro first second same
  apply Subtype.ext
  exact add_left_cancel (congrArg toAdd same)

theorem coneCharacterSectionMap_eq_mul (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (polynomial : affineCoordinateRing 𝕜 fan.lattice cone) :
    fan.coneCharacterSectionMap 𝕜 cone character polynomial =
      fan.coneLaurentMap 𝕜 cone polynomial * fan.characterLaurentMonomial 𝕜 character := by
  induction polynomial using MonoidAlgebra.induction_on with
  | of exponent =>
      change fan.coneCharacterSectionMap 𝕜 cone character
        (MonoidAlgebra.single (ofAdd (toAdd exponent)) 1) =
          fan.coneLaurentMap 𝕜 cone (MonoidAlgebra.single (ofAdd (toAdd exponent)) 1) * _
      rw [coneCharacterSectionMap_single, coneLaurentMap_single]
      simp only [characterLaurentMonomial, MonoidAlgebra.single_mul_single, one_mul]
      congr 1
      change character + (toAdd exponent).val = (toAdd exponent).val + character
      exact add_comm _ _
  | add first second first_eq second_eq =>
      simp only [map_add, add_mul, first_eq, second_eq]
  | smul coefficient polynomial polynomial_eq =>
      simp only [map_smul, polynomial_eq, smul_mul_assoc]

theorem mem_range_coneCharacterSectionMap_iff (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (character : Lattice →+ ℤ)
    (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    polynomial ∈ (fan.coneCharacterSectionMap 𝕜 cone character).range ↔
      ∀ exponent ∈ polynomial.coeff.support,
        toAdd exponent - character ∈ dualSemigroup fan.lattice cone := by
  classical
  let translate : Multiplicative (dualSemigroup fan.lattice cone) →
      Multiplicative (Lattice →+ ℤ) :=
    fun exponent => ofAdd (character + (toAdd exponent).val)
  have injective : Function.Injective translate := by
    intro first second same
    apply Subtype.ext
    exact add_left_cancel (congrArg toAdd same)
  have range_translate : ∀ exponent,
      exponent ∈ Set.range translate ↔
        toAdd exponent - character ∈ dualSemigroup fan.lattice cone := by
    intro exponent
    constructor
    · rintro ⟨source, rfl⟩
      simpa only [translate, toAdd_ofAdd, add_sub_cancel_left] using (toAdd source).property
    · intro member
      refine ⟨ofAdd ⟨toAdd exponent - character, member⟩, ?_⟩
      apply congrArg ofAdd
      change character + (toAdd exponent - character) = toAdd exponent
      abel
  constructor
  · rintro ⟨source, rfl⟩ exponent contains
    change exponent ∈ (MonoidAlgebra.mapDomain translate source).coeff.support at contains
    rw [MonoidAlgebra.coeff_mapDomain] at contains
    change exponent ∈ (Finsupp.mapDomain (⟨translate, injective⟩ : _ ↪ _) source.coeff).support at contains
    rw [Finsupp.support_mapDomain_embedding] at contains
    obtain ⟨original, _, same⟩ := Finset.mem_map.mp contains
    exact (range_translate exponent).mp ⟨original, same⟩
  · intro supported
    have range_supported : ↑polynomial.coeff.support ⊆ Set.range translate := by
      intro exponent contains
      exact (range_translate exponent).mpr (supported exponent contains)
    refine ⟨MonoidAlgebra.comapDomain translate injective polynomial, ?_⟩
    exact MonoidAlgebra.mapDomain_comapDomain range_supported injective

section ChartModule

variable (fan : Fan embedding) (cone : PointedCone ℝ Ambient)

variable {𝕜} in
noncomputable local instance chartLaurentModule :
    Module (affineCoordinateRing 𝕜 fan.lattice cone) (fan.LaurentCharacterAlgebra 𝕜) :=
  Module.compHom _ (fan.coneLaurentMap 𝕜 cone).toRingHom

noncomputable def coneCharacterModuleMap (character : Lattice →+ ℤ) :
    affineCoordinateRing 𝕜 fan.lattice cone →ₗ[affineCoordinateRing 𝕜 fan.lattice cone]
      (fan.LaurentCharacterAlgebra 𝕜) where
  toFun := fan.coneCharacterSectionMap 𝕜 cone character
  map_add' := (fan.coneCharacterSectionMap 𝕜 cone character).map_add
  map_smul' scalar polynomial := by
    change fan.coneCharacterSectionMap 𝕜 cone character (scalar * polynomial) =
      fan.coneLaurentMap 𝕜 cone scalar * fan.coneCharacterSectionMap 𝕜 cone character polynomial
    rw [coneCharacterSectionMap_eq_mul, coneCharacterSectionMap_eq_mul, map_mul, mul_assoc]

noncomputable def coneMonomialSectionModule (character : Lattice →+ ℤ) :
    Submodule (affineCoordinateRing 𝕜 fan.lattice cone) (fan.LaurentCharacterAlgebra 𝕜) :=
  (fan.coneCharacterModuleMap 𝕜 cone character).range

theorem mem_coneMonomialSectionModule_iff (character : Lattice →+ ℤ)
    (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    polynomial ∈ fan.coneMonomialSectionModule 𝕜 cone character ↔
      ∀ exponent ∈ polynomial.coeff.support,
        toAdd exponent - character ∈ dualSemigroup fan.lattice cone :=
  fan.mem_range_coneCharacterSectionMap_iff 𝕜 cone character polynomial

noncomputable def coneMonomialSectionEquiv (character : Lattice →+ ℤ) :
    affineCoordinateRing 𝕜 fan.lattice cone ≃ₗ[affineCoordinateRing 𝕜 fan.lattice cone]
      (fan.coneMonomialSectionModule 𝕜) cone character :=
  LinearEquiv.ofInjective (fan.coneCharacterModuleMap 𝕜 cone character)
    (fan.coneCharacterSectionMap_injective 𝕜 cone character)

@[simp] theorem coneMonomialSectionEquiv_val (character : Lattice →+ ℤ)
    (polynomial : affineCoordinateRing 𝕜 fan.lattice cone) :
    (fan.coneMonomialSectionEquiv 𝕜 cone character polynomial : fan.LaurentCharacterAlgebra 𝕜) =
      fan.coneLaurentMap 𝕜 cone polynomial * fan.characterLaurentMonomial 𝕜 character :=
  fan.coneCharacterSectionMap_eq_mul 𝕜 cone character polynomial

end ChartModule

def divisorSectionExponents (fan : Fan embedding) (cone : PointedCone ℝ Ambient)
    (divisor : fan.InvariantRayDivisor) : Set (Multiplicative (Lattice →+ ℤ)) :=
  {exponent | ∀ ray : fan.Ray, embedding ray.val ∈ cone →
    -divisor ray ≤ toAdd exponent ray.val}

noncomputable def divisorLaurentSectionSpace (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (divisor : fan.InvariantRayDivisor) :
    Submodule 𝕜 (fan.LaurentCharacterAlgebra 𝕜) :=
  MonoidAlgebra.supported 𝕜 𝕜 (fan.divisorSectionExponents cone divisor)

theorem mem_divisorLaurentSectionSpace_iff (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (divisor : fan.InvariantRayDivisor)
    (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    polynomial ∈ fan.divisorLaurentSectionSpace 𝕜 cone divisor ↔
      ∀ exponent ∈ polynomial.coeff.support, ∀ ray : fan.Ray,
        embedding ray.val ∈ cone → -divisor ray ≤ toAdd exponent ray.val := by
  rfl

theorem sub_coneDivisorCharacter_mem_dualSemigroup_iff (fan : Fan embedding)
    {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (divisor : fan.InvariantRayDivisor)
    (character : Lattice →+ ℤ) :
    character - fan.coneDivisorCharacter basis cone_basis divisor ∈
      dualSemigroup fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) ↔
      ofAdd character ∈ fan.divisorSectionExponents
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) divisor := by
  have same_range : Set.range (fun index => embedding (basis index)) =
      embedding '' Set.range basis := by
    ext vector
    simp
  rw [same_range, mem_dualSemigroup_hull_image]
  constructor
  · intro nonnegative ray contains
    rw [← same_range] at contains
    obtain ⟨index, same⟩ := fan.ray_eq_basis_of_mem_coneBasis basis cone_basis ray contains
    have bound := nonnegative (basis index) (Set.mem_range_self index)
    have same_ray : fan.basisRay basis cone_basis index = ray := Subtype.ext same
    simp only [AddMonoidHom.sub_apply, fan.coneDivisorCharacter_basis, same_ray] at bound
    change -divisor ray ≤ character ray.val
    rw [← same]
    omega
  · intro inequalities vector contains
    obtain ⟨index, rfl⟩ := contains
    have bound := inequalities (fan.basisRay basis cone_basis index) (by
      change embedding (basis index) ∈ PointedCone.hull ℝ (embedding '' Set.range basis)
      exact PointedCone.subset_hull ⟨basis index, Set.mem_range_self index, rfl⟩)
    change 0 ≤ character (basis index) -
      fan.coneDivisorCharacter basis cone_basis divisor (basis index)
    rw [fan.coneDivisorCharacter_basis]
    change -divisor (fan.basisRay basis cone_basis index) ≤ character (basis index) at bound
    omega

section DivisorChart

variable (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)

variable {𝕜} in
noncomputable local instance divisorChartLaurentModule :
    Module (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) )
      (fan.LaurentCharacterAlgebra 𝕜) :=
  Module.compHom _ (fan.coneLaurentMap 𝕜 _).toRingHom

noncomputable def coneDivisorSectionModule (divisor : fan.InvariantRayDivisor) :
    Submodule (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
      (fan.LaurentCharacterAlgebra 𝕜) :=
  fan.coneMonomialSectionModule 𝕜 _ (fan.coneDivisorCharacter basis cone_basis divisor)

theorem mem_coneDivisorSectionModule_iff (divisor : fan.InvariantRayDivisor)
    (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    polynomial ∈ fan.coneDivisorSectionModule 𝕜 basis cone_basis divisor ↔
      polynomial ∈ fan.divisorLaurentSectionSpace 𝕜
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) divisor := by
  rw [coneDivisorSectionModule, mem_coneMonomialSectionModule_iff,
    mem_divisorLaurentSectionSpace_iff]
  exact forall_congr' (fun exponent => forall_congr' (fun _ =>
    fan.sub_coneDivisorCharacter_mem_dualSemigroup_iff basis cone_basis divisor (toAdd exponent)))

noncomputable def coneDivisorSectionEquiv (divisor : fan.InvariantRayDivisor) :
    affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))
      ≃ₗ[affineCoordinateRing 𝕜 fan.lattice
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))]
      (fan.coneDivisorSectionModule 𝕜) basis cone_basis divisor :=
  fan.coneMonomialSectionEquiv 𝕜 _ (fan.coneDivisorCharacter basis cone_basis divisor)

noncomputable def coneDivisorSectionGenerator (divisor : fan.InvariantRayDivisor) :
    fan.coneDivisorSectionModule 𝕜 basis cone_basis divisor :=
  fan.coneDivisorSectionEquiv 𝕜 basis cone_basis divisor 1

@[simp] theorem coneDivisorSectionGenerator_val (divisor : fan.InvariantRayDivisor) :
    (fan.coneDivisorSectionGenerator 𝕜 basis cone_basis divisor : fan.LaurentCharacterAlgebra 𝕜) =
      fan.characterLaurentMonomial 𝕜 (fan.coneDivisorCharacter basis cone_basis divisor) := by
  change (fan.coneMonomialSectionEquiv 𝕜 _ _ 1 : fan.LaurentCharacterAlgebra 𝕜) = _
  rw [coneMonomialSectionEquiv_val, map_one, one_mul]

end DivisorChart

theorem coneLaurentMap_face_restriction (fan : Fan embedding)
    {cone face : PointedCone ℝ Ambient} (face_of : face.IsFaceOf cone)
    (polynomial : affineCoordinateRing 𝕜 fan.lattice cone) :
    fan.coneLaurentMap 𝕜 face (faceAffineCoordinateRingMap 𝕜 fan.lattice face_of polynomial) =
      fan.coneLaurentMap 𝕜 cone polynomial := by
  induction polynomial using MonoidAlgebra.induction_on with
  | of exponent =>
      change fan.coneLaurentMap 𝕜 face
        (faceAffineCoordinateRingMap 𝕜 fan.lattice face_of
          (MonoidAlgebra.single (ofAdd (toAdd exponent)) 1)) = _
      rw [faceAffineCoordinateRingMap_single, coneLaurentMap_single]
      exact fan.coneLaurentMap_single 𝕜 cone (toAdd exponent) 1 |>.symm
  | add first second first_eq second_eq =>
      simp only [map_add, first_eq, second_eq]
  | smul coefficient polynomial polynomial_eq =>
      simp only [map_smul, polynomial_eq]

theorem coneCharacterSectionMap_face_restriction (fan : Fan embedding)
    {cone face : PointedCone ℝ Ambient} (face_of : face.IsFaceOf cone)
    (character : Lattice →+ ℤ) (polynomial : affineCoordinateRing 𝕜 fan.lattice cone) :
    fan.coneCharacterSectionMap 𝕜 face character
        (faceAffineCoordinateRingMap 𝕜 fan.lattice face_of polynomial) =
      fan.coneCharacterSectionMap 𝕜 cone character polynomial := by
  rw [coneCharacterSectionMap_eq_mul, coneLaurentMap_face_restriction,
    coneCharacterSectionMap_eq_mul]

theorem coneCharacterSectionMap_change_character (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (first second : Lattice →+ ℤ)
    (positive : first - second ∈ dualSemigroup fan.lattice cone)
    (negative : -(first - second) ∈ dualSemigroup fan.lattice cone)
    (polynomial : affineCoordinateRing 𝕜 fan.lattice cone) :
    fan.coneCharacterSectionMap 𝕜 cone second
        ((toricMonomialUnit 𝕜 fan.lattice cone (first - second) positive negative :
          affineCoordinateRing 𝕜 fan.lattice cone) * polynomial) =
      fan.coneCharacterSectionMap 𝕜 cone first polynomial := by
  rw [coneCharacterSectionMap_eq_mul, map_mul, toricMonomialUnit_val,
    coneLaurentMap_single, coneCharacterSectionMap_eq_mul]
  have monomial_identity :
      (MonoidAlgebra.single (ofAdd (first - second)) 1 : fan.LaurentCharacterAlgebra 𝕜) *
        fan.characterLaurentMonomial 𝕜 second = fan.characterLaurentMonomial 𝕜 first := by
    simp only [characterLaurentMonomial, MonoidAlgebra.single_mul_single, one_mul]
    congr 1
    change first - second + second = first
    abel
  calc
    _ = fan.coneLaurentMap 𝕜 cone polynomial *
        (MonoidAlgebra.single (ofAdd (first - second)) 1 *
          fan.characterLaurentMonomial 𝕜 second) := by ring
    _ = _ := by rw [monomial_identity]

def globalDivisorSectionExponents (fan : Fan embedding) (divisor : fan.InvariantRayDivisor) :
    Set (Multiplicative (Lattice →+ ℤ)) :=
  {exponent | ∀ ray : fan.Ray, -divisor ray ≤ toAdd exponent ray.val}

noncomputable def globalDivisorLaurentSectionSpace (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) : Submodule 𝕜 (fan.LaurentCharacterAlgebra 𝕜) :=
  MonoidAlgebra.supported 𝕜 𝕜 (fan.globalDivisorSectionExponents divisor)

theorem mem_globalDivisorLaurentSectionSpace_iff (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) (polynomial : fan.LaurentCharacterAlgebra 𝕜) :
    polynomial ∈ fan.globalDivisorLaurentSectionSpace 𝕜 divisor ↔
      ∀ exponent ∈ polynomial.coeff.support, ∀ ray : fan.Ray,
        -divisor ray ≤ toAdd exponent ray.val := by
  rfl

theorem characterLaurentMonomial_mem_global_iff (fan : Fan embedding)
    (divisor : fan.InvariantRayDivisor) (character : Lattice →+ ℤ) :
    fan.characterLaurentMonomial 𝕜 character ∈ fan.globalDivisorLaurentSectionSpace 𝕜 divisor ↔
      ∀ ray : fan.Ray, -divisor ray ≤ character ray.val := by
  classical
  simp [globalDivisorLaurentSectionSpace, MonoidAlgebra.mem_supported,
    characterLaurentMonomial, globalDivisorSectionExponents]

theorem globalDivisorLaurentSectionSpace_le_cone (fan : Fan embedding)
    (cone : PointedCone ℝ Ambient) (divisor : fan.InvariantRayDivisor) :
    fan.globalDivisorLaurentSectionSpace 𝕜 divisor ≤ fan.divisorLaurentSectionSpace 𝕜 cone divisor := by
  apply MonoidAlgebra.supported_mono
  intro exponent inequalities ray _
  exact inequalities ray

section Generation

variable [FiniteDimensional ℝ Ambient]
    (fan : Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)

variable {𝕜} in
noncomputable local instance generationChartLaurentModule :
    Module (affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))))
      (fan.LaurentCharacterAlgebra 𝕜) :=
  Module.compHom _ (fan.coneLaurentMap 𝕜 _).toRingHom

noncomputable def globalDivisorSectionOnChart (divisor : fan.InvariantRayDivisor)
    (global_section : fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :
    fan.coneDivisorSectionModule 𝕜 basis cone_basis divisor :=
  ⟨global_section.val,
    (fan.mem_coneDivisorSectionModule_iff 𝕜 basis cone_basis divisor global_section.val).mpr
      (fan.globalDivisorLaurentSectionSpace_le_cone 𝕜 _ divisor global_section.property)⟩

noncomputable def globalDivisorChartCoefficient (divisor : fan.InvariantRayDivisor)
    (global_section : fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :
    affineCoordinateRing 𝕜 fan.lattice
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) :=
  (fan.coneDivisorSectionEquiv 𝕜 basis cone_basis divisor).symm
    (fan.globalDivisorSectionOnChart 𝕜 basis cone_basis divisor global_section)

omit [FiniteDimensional ℝ Ambient] in
theorem globalDivisorChartCoefficient_reconstruct (divisor : fan.InvariantRayDivisor)
    (global_section : fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :
    fan.coneCharacterSectionMap 𝕜
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))
        (fan.coneDivisorCharacter basis cone_basis divisor)
        (fan.globalDivisorChartCoefficient 𝕜 basis cone_basis divisor global_section) =
      (global_section : fan.LaurentCharacterAlgebra 𝕜) := by
  have same := congrArg (fun section_element : fan.coneDivisorSectionModule 𝕜 basis cone_basis divisor =>
      (section_element : fan.LaurentCharacterAlgebra 𝕜))
    ((fan.coneDivisorSectionEquiv 𝕜 basis cone_basis divisor).apply_symm_apply
      (fan.globalDivisorSectionOnChart 𝕜 basis cone_basis divisor global_section))
  exact same

end Generation

theorem globalDivisorChartCoefficient_overlap (fan : Fan embedding)
    {firstDimension secondDimension : ℕ}
    (first : Basis (Fin firstDimension) ℤ Lattice) (first_cone : fan.IsConeBasis first)
    (second : Basis (Fin secondDimension) ℤ Lattice) (second_cone : fan.IsConeBasis second)
    (divisor : fan.InvariantRayDivisor)
    (global_section : fan.globalDivisorLaurentSectionSpace 𝕜 divisor) :
    faceAffineCoordinateRingMap 𝕜 fan.lattice
        (fan.inf_isFaceOf_right first_cone second_cone)
        (fan.globalDivisorChartCoefficient 𝕜 second second_cone divisor global_section) =
      (fan.coneDivisorTransitionUnit 𝕜 first first_cone second second_cone divisor :
        affineCoordinateRing 𝕜 fan.lattice
          (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
            PointedCone.hull ℝ (Set.range (fun index => embedding (second index))))) *
        faceAffineCoordinateRingMap 𝕜 fan.lattice
          (fan.inf_isFaceOf_left first_cone second_cone)
          (fan.globalDivisorChartCoefficient 𝕜 first first_cone divisor global_section) := by
  apply fan.coneCharacterSectionMap_injective 𝕜 _
    (fan.coneDivisorCharacter second second_cone divisor)
  have memberships := fan.coneDivisorCharacter_transition_dualSemigroup first first_cone
    second second_cone divisor
  change fan.coneCharacterSectionMap 𝕜 _ _
      (faceAffineCoordinateRingMap 𝕜 _ _ _) =
    fan.coneCharacterSectionMap 𝕜 _ _
      ((toricMonomialUnit 𝕜 fan.lattice _
        (fan.coneDivisorCharacter first first_cone divisor -
          fan.coneDivisorCharacter second second_cone divisor) memberships.1 memberships.2 :
        affineCoordinateRing 𝕜 fan.lattice
          (PointedCone.hull ℝ (Set.range (fun index => embedding (first index))) ⊓
            PointedCone.hull ℝ (Set.range (fun index => embedding (second index))))) * _)
  rw [coneCharacterSectionMap_change_character,
    coneCharacterSectionMap_face_restriction, coneCharacterSectionMap_face_restriction,
    globalDivisorChartCoefficient_reconstruct, globalDivisorChartCoefficient_reconstruct]

end TauCeti.Toric.Fan
