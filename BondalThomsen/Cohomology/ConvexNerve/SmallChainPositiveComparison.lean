module

public import BondalThomsen.Cohomology.ConvexNerve.SmallChainQuasiIso
public import Mathlib.Geometry.Convex.ConvexSpace.AffineMapCone
public import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ConvexNerveAcyclicCarrierAssembly
open BondalThomsen.ConvexNerveSmallSingularComparison
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveSmallChainQuasiIso
open scoped Classical Simplicial

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveSmallChainPositiveComparison

@[implicit_reducible] def affineTupleSet (Point : Type) : SSet.{0} where
  obj simplex := Fin (simplex.unop.len + 1) → Point
  map selection := ↾fun tuple => tuple ∘ selection.unop.toOrderHom
  map_id _simplex := rfl
  map_comp _first _second := rfl

noncomputable abbrev affineTupleChains (Point : Type) : ChainComplex AddCommGrpCat.{0} ℕ :=
  (affineTupleSet Point).chainComplex (AddCommGrpCat.of ℤ)

def augmentedAffineTupleSet (Point : Type) : SimplicialObject.Augmented Type where
  left := affineTupleSet Point
  right := Unit
  hom := {app := fun _simplex => ↾fun _tuple => ()}

def affineTupleExtraDegeneracy {Point : Type} (anchor : Point) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmentedAffineTupleSet Point) where
  s' := ↾fun _point => fun _column => anchor
  s degree := ↾fun tuple => Fin.cons anchor tuple
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro point
    rfl
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro tuple
    funext column
    fin_cases column
    rfl
  s_comp_δ₀ degree := by
    apply ConcreteCategory.hom_ext
    intro tuple
    funext column
    simp [SimplicialObject.δ, SimplexCategory.δ, affineTupleSet, augmentedAffineTupleSet]
  s_comp_δ degree deleted := by
    apply ConcreteCategory.hom_ext
    intro tuple
    funext column
    dsimp [SimplicialObject.δ, SimplexCategory.δ, affineTupleSet, augmentedAffineTupleSet]
    cases column using Fin.cases <;> simp
  s_comp_σ degree repeated := by
    apply ConcreteCategory.hom_ext
    intro tuple
    funext column
    dsimp [SimplicialObject.σ, SimplexCategory.σ, affineTupleSet, augmentedAffineTupleSet]
    cases column using Fin.cases <;> simp

noncomputable def affineTupleChainHomotopyEquiv {Point : Type} (anchor : Point) :
    HomotopyEquiv (affineTupleChains Point)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject) :=
  ((affineTupleExtraDegeneracy anchor).map (sigmaConst.obj (AddCommGrpCat.of ℤ))).homotopyEquiv

noncomputable def affineTupleChainAugmentationMap (Point : Type) :
    affineTupleChains Point ⟶
      (ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((SimplicialObject.Augmented.whiskering (Type) AddCommGrpCat.{0}).obj
      (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj (augmentedAffineTupleSet Point))

noncomputable def affineTupleChainAugmentation (Point : Type) :
    (affineTupleChains Point).X 0 ⟶ incidenceAugmentationObject :=
  (affineTupleChainAugmentationMap Point).f 0

theorem affineTupleChainAugmentation_zero (Point : Type) :
    (affineTupleChains Point).d 1 0 ≫ affineTupleChainAugmentation Point = 0 := by
  have equality := (affineTupleChainAugmentationMap Point).comm 1 0
  rw [HomologicalComplex.single_obj_d, comp_zero] at equality
  exact equality.symm

noncomputable def affineTupleCone {Point : Type} (anchor : Point) (degree : ℕ) :
    (affineTupleChains Point).X degree ⟶ (affineTupleChains Point).X (degree + 1) :=
  -((affineTupleChainHomotopyEquiv anchor).homotopyHomInvId.hom degree (degree + 1))

theorem affineTupleCone_generator {Point : Type} (anchor : Point) (degree : ℕ)
    (tuple : Fin (degree + 1) → Point) :
    (affineTupleSet Point).ιChainComplex tuple ≫ affineTupleCone anchor degree =
      (affineTupleSet Point).ιChainComplex (Fin.cons anchor tuple) := by
  simp only [affineTupleCone, affineTupleChainHomotopyEquiv,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, Pi.single_eq_same, neg_neg]
  change Sigma.ι (fun _tuple : Fin (degree + 1) → Point => AddCommGrpCat.of ℤ) tuple ≫
    (Sigma.desc fun original : Fin (degree + 1) → Point =>
      𝟙 (AddCommGrpCat.of ℤ) ≫ Sigma.ι
        (fun _tuple : Fin (degree + 2) → Point => AddCommGrpCat.of ℤ)
        (Fin.cons anchor original)) = _
  rw [Sigma.ι_comp_desc, Category.id_comp]
  rfl

theorem affineTupleCone_identity_zero {Point : Type} (anchor : Point) :
    affineTupleCone anchor 0 ≫ (affineTupleChains Point).d 1 0 =
      𝟙 ((affineTupleChains Point).X 0) -
        affineTupleChainAugmentation Point ≫ (affineTupleChainHomotopyEquiv anchor).inv.f 0 := by
  let equivalence := affineTupleChainHomotopyEquiv anchor
  have identity := equivalence.homotopyHomInvId.comm 0
  rw [Homotopy.dNext_zero_chainComplex, zero_add, Homotopy.prevD_chainComplex] at identity
  change affineTupleChainAugmentation Point ≫ equivalence.inv.f 0 = _ at identity
  change (-equivalence.homotopyHomInvId.hom 0 1) ≫ _ = _
  rw [neg_comp]
  have rearranged := congrArg (fun value => 𝟙 ((affineTupleChains Point).X 0) - value) identity
  have reversed := rearranged.symm
  change 𝟙 ((affineTupleChains Point).X 0) -
    (equivalence.homotopyHomInvId.hom 0 1 ≫ (affineTupleChains Point).d 1 0 + 𝟙 _) = _ at reversed
  have cancellation (value : (affineTupleChains Point).X 0 ⟶ (affineTupleChains Point).X 0) :
      𝟙 _ - (value + 𝟙 _) = -value := by abel
  rwa [cancellation] at reversed

theorem affineTupleCone_identity_positive {Point : Type} (anchor : Point) (degree : ℕ) :
    (affineTupleChains Point).d (degree + 1) degree ≫ affineTupleCone anchor degree +
      affineTupleCone anchor (degree + 1) ≫ (affineTupleChains Point).d (degree + 2) (degree + 1) =
      𝟙 ((affineTupleChains Point).X (degree + 1)) := by
  let equivalence := affineTupleChainHomotopyEquiv anchor
  have middleZero : IsZero
      (((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject).X (degree + 1)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have collapse : equivalence.hom.f (degree + 1) ≫ equivalence.inv.f (degree + 1) = 0 := by
    rw [middleZero.eq_of_tgt (equivalence.hom.f (degree + 1)) 0, zero_comp]
  have identity := equivalence.homotopyHomInvId.comm (degree + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at identity
  change equivalence.hom.f (degree + 1) ≫ equivalence.inv.f (degree + 1) = _ at identity
  rw [collapse] at identity
  change _ ≫ (-equivalence.homotopyHomInvId.hom degree (degree + 1)) +
    (-equivalence.homotopyHomInvId.hom (degree + 1) (degree + 2)) ≫ _ = _
  rw [comp_neg, neg_comp, ← neg_add]
  exact (eq_neg_of_add_eq_zero_right identity.symm).symm

def affineTupleMap {Point Target : Type} (mapping : Point → Target) :
    affineTupleSet Point ⟶ affineTupleSet Target where
  app _simplex := ↾fun tuple => mapping ∘ tuple

noncomputable def affineTupleChainMap {Point Target : Type} (mapping : Point → Target) :
    affineTupleChains Point ⟶ affineTupleChains Target :=
  SSet.chainComplexMap (affineTupleMap mapping) (AddCommGrpCat.of ℤ)

theorem affineTupleChainMap_generator {Point Target : Type} (mapping : Point → Target)
    (degree : ℕ) (tuple : Fin (degree + 1) → Point) :
    (affineTupleSet Point).ιChainComplex tuple ≫ (affineTupleChainMap mapping).f degree =
      (affineTupleSet Target).ιChainComplex (mapping ∘ tuple) :=
  SSet.ι_chainComplexMap_f _ _ _ _ _

theorem affineTupleCone_naturality {Point Target : Type} (mapping : Point → Target)
    (anchor : Point) (degree : ℕ) :
    affineTupleCone anchor degree ≫ (affineTupleChainMap mapping).f (degree + 1) =
      (affineTupleChainMap mapping).f degree ≫ affineTupleCone (mapping anchor) degree := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  rw [← Category.assoc, affineTupleCone_generator, affineTupleChainMap_generator,
    ← Category.assoc, affineTupleChainMap_generator, affineTupleCone_generator]
  congr 1
  funext column
  cases column using Fin.cases <;> rfl

noncomputable def affineTupleBarycenter (ambient degree : ℕ)
    (tuple : Fin (degree + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :
    Convexity.StdSimplex ℝ (Fin (ambient + 1)) :=
  Convexity.StdSimplex.affineMapMk (R := ℝ) tuple
    (Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (degree + 1)))

theorem affineTupleBarycenter_naturality {ambient target degree : ℕ}
    (mapping : Convexity.ConvexSpace.AffineMap ℝ
      (Convexity.StdSimplex ℝ (Fin (ambient + 1)))
      (Convexity.StdSimplex ℝ (Fin (target + 1))))
    (tuple : Fin (degree + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :
    mapping (affineTupleBarycenter ambient degree tuple) =
      affineTupleBarycenter target degree (mapping ∘ tuple) := by
  exact congrArg (fun affine => affine (Convexity.StdSimplex.barycenter (K := ℝ) (M := Fin (degree + 1))))
    (Convexity.StdSimplex.comp_affineMapMk mapping tuple)

theorem affineTupleCone_fill_zero {Point : Type} (anchor : Point)
    (cycle : AddCommGrpCat.of ℤ ⟶ (affineTupleChains Point).X 0)
    (closed : cycle ≫ affineTupleChainAugmentation Point = 0) :
    cycle ≫ affineTupleCone anchor 0 ≫ (affineTupleChains Point).d 1 0 = cycle := by
  rw [affineTupleCone_identity_zero, comp_sub, Category.comp_id,
    ← Category.assoc, closed, zero_comp, sub_zero]

theorem affineTupleCone_fill_positive {Point : Type} (anchor : Point) (degree : ℕ)
    (cycle : AddCommGrpCat.of ℤ ⟶ (affineTupleChains Point).X (degree + 1))
    (closed : cycle ≫ (affineTupleChains Point).d (degree + 1) degree = 0) :
    cycle ≫ affineTupleCone anchor (degree + 1) ≫
      (affineTupleChains Point).d (degree + 2) (degree + 1) = cycle := by
  have equality := congrArg (fun mapping => cycle ≫ mapping)
    (affineTupleCone_identity_positive anchor degree)
  simpa only [comp_add, ← Category.assoc, closed, zero_comp, zero_add, Category.comp_id] using equality

noncomputable def affineSubdivisionComponents (ambient : ℕ) : ∀ degree,
    (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).X degree ⟶
      (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).X degree :=
  Nat.rec (motive := fun degree =>
    (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).X degree ⟶
      (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).X degree)
    (𝟙 _) (fun degree previous => Sigma.desc fun tuple =>
      (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
        (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 1) degree ≫
          previous ≫ affineTupleCone (affineTupleBarycenter ambient (degree + 1) tuple) degree)

theorem affineSubdivisionComponents_zero (ambient : ℕ) :
    affineSubdivisionComponents ambient 0 = 𝟙 _ := rfl

theorem affineSubdivisionComponents_generator (ambient degree : ℕ)
    (tuple : Fin (degree + 2) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
      affineSubdivisionComponents ambient (degree + 1) =
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
      (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 1) degree ≫
        affineSubdivisionComponents ambient degree ≫
          affineTupleCone (affineTupleBarycenter ambient (degree + 1) tuple) degree :=
  Sigma.ι_comp_desc _ _

theorem affineSubdivisionComponents_comm (ambient degree : ℕ) :
    affineSubdivisionComponents ambient (degree + 1) ≫
      (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 1) degree =
    (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 1) degree ≫
      affineSubdivisionComponents ambient degree := by
  induction degree with
  | zero =>
    apply SSet.chainComplex_hom_ext
    intro tuple
    rw [← Category.assoc, affineSubdivisionComponents_generator]
    have closed : ((affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
        (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d 1 0 ≫
          affineSubdivisionComponents ambient 0) ≫
        affineTupleChainAugmentation (Convexity.StdSimplex ℝ (Fin (ambient + 1))) = 0 := by
      rw [affineSubdivisionComponents_zero, Category.comp_id, Category.assoc,
        affineTupleChainAugmentation_zero, comp_zero]
    simpa only [Category.assoc] using affineTupleCone_fill_zero
      (affineTupleBarycenter ambient 1 tuple) _ closed
  | succ degree previous =>
    apply SSet.chainComplex_hom_ext
    intro tuple
    rw [← Category.assoc, affineSubdivisionComponents_generator]
    have closed : ((affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
        (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 2) (degree + 1) ≫
          affineSubdivisionComponents ambient (degree + 1)) ≫
        (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 1) degree = 0 := by
      simp only [Category.assoc]
      rw [previous, HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]
    simpa only [Category.assoc] using affineTupleCone_fill_positive
      (affineTupleBarycenter ambient (degree + 2) tuple) degree _ closed

noncomputable def affineBarycentricSubdivision (ambient : ℕ) :
    affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1))) ⟶
      affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1))) where
  f := affineSubdivisionComponents ambient
  comm' source target related := by
    have equal : target + 1 = source := related
    subst source
    exact affineSubdivisionComponents_comm ambient target

theorem affineBarycentricSubdivision_naturality {ambient target : ℕ}
    (mapping : Convexity.ConvexSpace.AffineMap ℝ
      (Convexity.StdSimplex ℝ (Fin (ambient + 1)))
      (Convexity.StdSimplex ℝ (Fin (target + 1)))) (degree : ℕ) :
    (affineBarycentricSubdivision ambient).f degree ≫ (affineTupleChainMap mapping).f degree =
      (affineTupleChainMap mapping).f degree ≫ (affineBarycentricSubdivision target).f degree := by
  induction degree with
  | zero => simp [affineBarycentricSubdivision, affineSubdivisionComponents_zero]
  | succ degree previous =>
    change affineSubdivisionComponents ambient degree ≫ (affineTupleChainMap mapping).f degree =
      (affineTupleChainMap mapping).f degree ≫ affineSubdivisionComponents target degree at previous
    apply SSet.chainComplex_hom_ext
    intro tuple
    change (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
      (affineSubdivisionComponents ambient (degree + 1) ≫ (affineTupleChainMap mapping).f (degree + 1)) =
      (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
        ((affineTupleChainMap mapping).f (degree + 1) ≫ affineSubdivisionComponents target (degree + 1))
    rw [← Category.assoc, affineSubdivisionComponents_generator]
    simp only [Category.assoc]
    rw [affineTupleCone_naturality, reassoc_of% previous,
      ← reassoc_of% (affineTupleChainMap mapping).comm (degree + 1) degree,
      ← Category.assoc, affineTupleChainMap_generator, affineTupleBarycenter_naturality]
    conv_rhs => rw [← Category.assoc, affineTupleChainMap_generator, affineSubdivisionComponents_generator]

noncomputable def affineSubdivisionHomotopyValues (ambient : ℕ) : ∀ degree,
    (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).X degree ⟶
      (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).X (degree + 1) :=
  Nat.rec (motive := fun degree =>
    (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).X degree ⟶
      (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).X (degree + 1))
    0 (fun degree previous => Sigma.desc fun tuple =>
      ((affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple -
        (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
          (affineBarycentricSubdivision ambient).f (degree + 1) -
        (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
          (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 1) degree ≫ previous) ≫
        affineTupleCone (tuple 0) (degree + 1))

theorem affineSubdivisionHomotopyValues_zero (ambient : ℕ) :
    affineSubdivisionHomotopyValues ambient 0 = 0 := rfl

theorem affineSubdivisionHomotopyValues_generator (ambient degree : ℕ)
    (tuple : Fin (degree + 2) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
      affineSubdivisionHomotopyValues ambient (degree + 1) =
    ((affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple -
      (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
        (affineBarycentricSubdivision ambient).f (degree + 1) -
      (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
        (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 1) degree ≫
          affineSubdivisionHomotopyValues ambient degree) ≫ affineTupleCone (tuple 0) (degree + 1) :=
  Sigma.ι_comp_desc _ _

theorem affineSubdivisionHomotopyValues_boundary (ambient degree : ℕ) :
    affineSubdivisionHomotopyValues ambient (degree + 1) ≫
      (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 2) (degree + 1) =
    𝟙 _ - (affineBarycentricSubdivision ambient).f (degree + 1) -
      (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 1) degree ≫
        affineSubdivisionHomotopyValues ambient degree := by
  induction degree with
  | zero =>
    apply SSet.chainComplex_hom_ext
    intro tuple
    rw [← Category.assoc, affineSubdivisionHomotopyValues_generator]
    have closed : ((affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple -
        (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
          (affineBarycentricSubdivision ambient).f 1 -
        (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
          (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d 1 0 ≫
            affineSubdivisionHomotopyValues ambient 0) ≫
        (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d 1 0 = 0 := by
      simp only [affineSubdivisionHomotopyValues_zero, comp_zero, sub_zero, sub_comp, Category.assoc]
      rw [(affineBarycentricSubdivision ambient).comm 1 0]
      simp [affineBarycentricSubdivision, affineSubdivisionComponents_zero]
    simp only [Category.assoc]
    rw [affineTupleCone_fill_positive (tuple 0) 0 _ closed]
    simp only [comp_sub, Category.comp_id]
  | succ degree previous =>
    apply SSet.chainComplex_hom_ext
    intro tuple
    rw [← Category.assoc, affineSubdivisionHomotopyValues_generator]
    have closed : ((affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple -
        (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
          (affineBarycentricSubdivision ambient).f (degree + 2) -
        (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
          (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 2) (degree + 1) ≫
            affineSubdivisionHomotopyValues ambient (degree + 1)) ≫
        (affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).d (degree + 2) (degree + 1) = 0 := by
      simp only [sub_comp, Category.assoc]
      rw [(affineBarycentricSubdivision ambient).comm (degree + 2) (degree + 1), previous]
      simp only [comp_sub, Category.comp_id, HomologicalComplex.d_comp_d_assoc,
        zero_comp, sub_zero]
      abel
    simp only [Category.assoc]
    rw [affineTupleCone_fill_positive (tuple 0) (degree + 1) _ closed]
    simp only [comp_sub, Category.comp_id]

theorem affineSubdivisionHomotopyValues_naturality {ambient target : ℕ}
    (mapping : Convexity.ConvexSpace.AffineMap ℝ
      (Convexity.StdSimplex ℝ (Fin (ambient + 1)))
      (Convexity.StdSimplex ℝ (Fin (target + 1)))) (degree : ℕ) :
    affineSubdivisionHomotopyValues ambient degree ≫ (affineTupleChainMap mapping).f (degree + 1) =
      (affineTupleChainMap mapping).f degree ≫ affineSubdivisionHomotopyValues target degree := by
  induction degree with
  | zero => simp [affineSubdivisionHomotopyValues_zero]
  | succ degree previous =>
    apply SSet.chainComplex_hom_ext
    intro tuple
    rw [← Category.assoc, affineSubdivisionHomotopyValues_generator]
    simp only [Category.assoc]
    rw [affineTupleCone_naturality]
    simp only [sub_comp, Category.assoc]
    rw [reassoc_of% affineBarycentricSubdivision_naturality mapping (degree + 1),
      reassoc_of% previous,
      ← reassoc_of% (affineTupleChainMap mapping).comm (degree + 1) degree]
    simp only [← Category.assoc, affineTupleChainMap_generator]
    rw [affineSubdivisionHomotopyValues_generator]
    simp only [sub_comp, Category.assoc]
    rfl

noncomputable def affineTupleSimplex (ambient degree : ℕ)
    (tuple : Fin (degree + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :
    C(Convexity.StdSimplex ℝ (Fin (degree + 1)), Convexity.StdSimplex ℝ (Fin (ambient + 1))) where
  toFun := Convexity.StdSimplex.affineMapMk (R := ℝ) tuple
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (ambient + 1))).continuous_iff]
    apply continuous_pi
    intro coordinate
    have weights (point : Convexity.StdSimplex ℝ (Fin (degree + 1))) :
        (Convexity.StdSimplex.affineMapMk (R := ℝ) tuple point).weights =
          ∑ column : Fin (degree + 1), point.weights column • (tuple column).weights := by
      rw [Convexity.StdSimplex.affineMapMk_apply,
        (Convexity.StdSimplex.isAffineMap_weights ℝ (Fin (ambient + 1))).map_iConvexComb,
        Convexity.iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)]
      rfl
    simp only [Function.comp_apply, weights, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    fun_prop

theorem affineTupleSimplex_precomp {ambient : ℕ} {source target : SimplexCategory}
    (selection : source ⟶ target)
    (tuple : Fin (target.len + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1)))
    (point : Convexity.StdSimplex ℝ (Fin (source.len + 1))) :
    affineTupleSimplex ambient source.len (tuple ∘ selection.toOrderHom) point =
      affineTupleSimplex ambient target.len tuple (point.map selection.toOrderHom) := by
  have equality : (Convexity.StdSimplex.affineMapMk (R := ℝ) tuple).comp
      (Convexity.StdSimplex.affineMap (R := ℝ) selection.toOrderHom) =
      Convexity.StdSimplex.affineMapMk (R := ℝ) (tuple ∘ selection.toOrderHom) := by
    apply Convexity.StdSimplex.affineMap_ext
    intro column
    simp
  exact (congrArg (fun mapping => mapping point) equality).symm

noncomputable def affineTupleSingularMap (ambient : ℕ) :
    affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1))) ⟶
      TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin (ambient + 1)))) where
  app simplex := ↾fun tuple => (TopCat.toSSetObjEquiv _ _).symm
    (affineTupleSimplex ambient simplex.unop.len tuple)
  naturality {source target} selection := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply (TopCat.toSSetObjEquiv _ _).injective
    apply ContinuousMap.ext
    intro point
    exact affineTupleSimplex_precomp selection.unop tuple point

noncomputable def affineTupleSingularChains (ambient : ℕ) :
    affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1))) ⟶
      integralSingularChains (Convexity.StdSimplex ℝ (Fin (ambient + 1))) :=
  SSet.chainComplexMap (affineTupleSingularMap ambient) (AddCommGrpCat.of ℤ)

variable {Space : Type} [TopologicalSpace Space]

noncomputable def singularPushChainMap {ambient : ℕ}
    (mapping : C(Convexity.StdSimplex ℝ (Fin (ambient + 1)), Space)) :
    integralSingularChains (Convexity.StdSimplex ℝ (Fin (ambient + 1))) ⟶
      integralSingularChains Space :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom mapping)) (AddCommGrpCat.of ℤ)

noncomputable def affineTupleEvaluation {ambient : ℕ}
    (mapping : C(Convexity.StdSimplex ℝ (Fin (ambient + 1)), Space)) :
    affineTupleChains (Convexity.StdSimplex ℝ (Fin (ambient + 1))) ⟶ integralSingularChains Space :=
  affineTupleSingularChains ambient ≫ singularPushChainMap mapping

theorem affineTupleEvaluation_generator {ambient degree : ℕ}
    (mapping : C(Convexity.StdSimplex ℝ (Fin (ambient + 1)), Space))
    (tuple : Fin (degree + 1) → Convexity.StdSimplex ℝ (Fin (ambient + 1))) :
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
      (affineTupleEvaluation mapping).f degree =
    (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      ((TopCat.toSSetObjEquiv _ _).symm (mapping.comp (affineTupleSimplex ambient degree tuple))) := by
  change (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
    ((affineTupleSingularChains ambient).f degree ≫ (singularPushChainMap mapping).f degree) = _
  rw [← Category.assoc]
  unfold affineTupleSingularChains
  rw [SSet.ι_chainComplexMap_f]
  unfold singularPushChainMap
  rw [SSet.ι_chainComplexMap_f]
  congr 1

theorem affineTupleEvaluation_naturality {ambient target : ℕ}
    (mapping : C(Convexity.StdSimplex ℝ (Fin (target + 1)), Space))
    (selection : Convexity.ConvexSpace.AffineMap ℝ
      (Convexity.StdSimplex ℝ (Fin (ambient + 1)))
      (Convexity.StdSimplex ℝ (Fin (target + 1))))
    (continuousSelection : Continuous selection) :
    affineTupleChainMap selection ≫ affineTupleEvaluation mapping =
      affineTupleEvaluation (mapping.comp ⟨selection, continuousSelection⟩) := by
  apply HomologicalComplex.Hom.ext
  funext degree
  apply SSet.chainComplex_hom_ext
  intro tuple
  change (affineTupleSet (Convexity.StdSimplex ℝ (Fin (ambient + 1)))).ιChainComplex tuple ≫
    ((affineTupleChainMap selection).f degree ≫ (affineTupleEvaluation mapping).f degree) = _
  rw [← Category.assoc, affineTupleChainMap_generator, affineTupleEvaluation_generator,
    affineTupleEvaluation_generator]
  congr 1
  apply congrArg (TopCat.toSSetObjEquiv (TopCat.of Space) (.op ⦋degree⦌)).symm
  apply ContinuousMap.ext
  intro point
  exact congrArg mapping (congrArg (fun affine => affine point)
    (Convexity.StdSimplex.comp_affineMapMk selection tuple)).symm

noncomputable def standardAffineTuple (degree : ℕ) :
    Fin (degree + 1) → Convexity.StdSimplex ℝ (Fin (degree + 1)) :=
  Convexity.StdSimplex.single

theorem standardAffineTuple_simplex (degree : ℕ) :
    affineTupleSimplex degree degree (standardAffineTuple degree) = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro point
  have identity : Convexity.StdSimplex.affineMapMk (R := ℝ) (standardAffineTuple degree) =
      Convexity.ConvexSpace.AffineMap.id (R := ℝ) (Convexity.StdSimplex ℝ (Fin (degree + 1))) := by
    apply Convexity.StdSimplex.affineMap_ext
    intro column
    simp [standardAffineTuple]
  exact congrArg (fun mapping => mapping point) identity

noncomputable def singularSubdivisionComponent (degree : ℕ) :
    (integralSingularChains Space).X degree ⟶ (integralSingularChains Space).X degree :=
  Sigma.desc fun simplex =>
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 1)))).ιChainComplex
      (standardAffineTuple degree) ≫ (affineBarycentricSubdivision degree).f degree ≫
        (affineTupleEvaluation (TopCat.toSSetObjEquiv (TopCat.of Space) (.op ⦋degree⦌) simplex)).f degree

noncomputable def singularSubdivisionHomotopyComponent (degree : ℕ) :
    (integralSingularChains Space).X degree ⟶ (integralSingularChains Space).X (degree + 1) :=
  Sigma.desc fun simplex =>
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 1)))).ιChainComplex
      (standardAffineTuple degree) ≫ affineSubdivisionHomotopyValues degree degree ≫
        (affineTupleEvaluation (TopCat.toSSetObjEquiv (TopCat.of Space) (.op ⦋degree⦌) simplex)).f (degree + 1)

theorem singularSubdivisionComponent_generator (degree : ℕ)
    (simplex : (TopCat.toSSet.obj (TopCat.of Space)) _⦋degree⦌) :
    (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex ≫
      singularSubdivisionComponent (Space := Space) degree =
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 1)))).ιChainComplex
      (standardAffineTuple degree) ≫ (affineBarycentricSubdivision degree).f degree ≫
        (affineTupleEvaluation (TopCat.toSSetObjEquiv (TopCat.of Space) (.op ⦋degree⦌) simplex)).f degree :=
  Sigma.ι_comp_desc _ _

theorem singularSubdivisionHomotopyComponent_generator (degree : ℕ)
    (simplex : (TopCat.toSSet.obj (TopCat.of Space)) _⦋degree⦌) :
    (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex ≫
      singularSubdivisionHomotopyComponent (Space := Space) degree =
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 1)))).ιChainComplex
      (standardAffineTuple degree) ≫ affineSubdivisionHomotopyValues degree degree ≫
        (affineTupleEvaluation (TopCat.toSSetObjEquiv (TopCat.of Space) (.op ⦋degree⦌) simplex)).f (degree + 1) :=
  Sigma.ι_comp_desc _ _

theorem standardAffineTuple_evaluation (degree : ℕ)
    (simplex : (TopCat.toSSet.obj (TopCat.of Space)) _⦋degree⦌) :
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 1)))).ιChainComplex
      (standardAffineTuple degree) ≫
        (affineTupleEvaluation (TopCat.toSSetObjEquiv (TopCat.of Space) (.op ⦋degree⦌) simplex)).f degree =
      (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex := by
  rw [affineTupleEvaluation_generator, standardAffineTuple_simplex, ContinuousMap.comp_id]
  rw [Equiv.symm_apply_apply]

theorem standardAffineTuple_face (degree : ℕ) (deleted : Fin (degree + 2)) :
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 2)))).ιChainComplex (R := AddCommGrpCat.of ℤ)
      ((affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 2)))).δ deleted (standardAffineTuple (degree + 1))) =
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 1)))).ιChainComplex
      (standardAffineTuple degree) ≫
        (affineTupleChainMap (Convexity.StdSimplex.affineMap (R := ℝ)
          (SimplexCategory.δ deleted).toOrderHom)).f degree := by
  rw [affineTupleChainMap_generator]
  congr 1
  funext column
  simp [standardAffineTuple, affineTupleSet, SimplicialObject.δ]

theorem subdivisionFaceEvaluation (degree : ℕ) (deleted : Fin (degree + 2))
    (simplex : (TopCat.toSSet.obj (TopCat.of Space)) _⦋degree + 1⦌) :
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 2)))).ιChainComplex
      ((affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 2)))).δ deleted (standardAffineTuple (degree + 1))) ≫
      (affineBarycentricSubdivision (degree + 1)).f degree ≫
        (affineTupleEvaluation (TopCat.toSSetObjEquiv (TopCat.of Space) (.op ⦋degree + 1⦌) simplex)).f degree =
    (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      ((TopCat.toSSet.obj (TopCat.of Space)).δ deleted simplex) ≫
        singularSubdivisionComponent (Space := Space) degree := by
  rw [standardAffineTuple_face, Category.assoc,
    ← reassoc_of% affineBarycentricSubdivision_naturality
      (Convexity.StdSimplex.affineMap (R := ℝ) (SimplexCategory.δ deleted).toOrderHom) degree]
  have evaluation := congrArg (fun mapping => mapping.f degree)
    (affineTupleEvaluation_naturality
      (TopCat.toSSetObjEquiv (TopCat.of Space) (.op ⦋degree + 1⦌) simplex)
      (Convexity.StdSimplex.affineMap (R := ℝ) (SimplexCategory.δ deleted).toOrderHom)
      (Convexity.StdSimplex.continuous_map ℝ (SimplexCategory.δ deleted).toOrderHom))
  rw [HomologicalComplex.comp_f] at evaluation
  rw [evaluation, singularSubdivisionComponent_generator]
  rfl

theorem homotopyFaceEvaluation (degree : ℕ) (deleted : Fin (degree + 2))
    (simplex : (TopCat.toSSet.obj (TopCat.of Space)) _⦋degree + 1⦌) :
    (affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 2)))).ιChainComplex
      ((affineTupleSet (Convexity.StdSimplex ℝ (Fin (degree + 2)))).δ deleted (standardAffineTuple (degree + 1))) ≫
      affineSubdivisionHomotopyValues (degree + 1) degree ≫
        (affineTupleEvaluation (TopCat.toSSetObjEquiv (TopCat.of Space) (.op ⦋degree + 1⦌) simplex)).f (degree + 1) =
    (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex (R := AddCommGrpCat.of ℤ)
      ((TopCat.toSSet.obj (TopCat.of Space)).δ deleted simplex) ≫
        singularSubdivisionHomotopyComponent (Space := Space) degree := by
  rw [standardAffineTuple_face, Category.assoc,
    ← reassoc_of% affineSubdivisionHomotopyValues_naturality
      (Convexity.StdSimplex.affineMap (R := ℝ) (SimplexCategory.δ deleted).toOrderHom) degree]
  have evaluation := congrArg (fun mapping => mapping.f (degree + 1))
    (affineTupleEvaluation_naturality
      (TopCat.toSSetObjEquiv (TopCat.of Space) (.op ⦋degree + 1⦌) simplex)
      (Convexity.StdSimplex.affineMap (R := ℝ) (SimplexCategory.δ deleted).toOrderHom)
      (Convexity.StdSimplex.continuous_map ℝ (SimplexCategory.δ deleted).toOrderHom))
  rw [HomologicalComplex.comp_f] at evaluation
  rw [evaluation, singularSubdivisionHomotopyComponent_generator]
  rfl

theorem singularSubdivisionComponent_comm (degree : ℕ) :
    singularSubdivisionComponent (Space := Space) (degree + 1) ≫
      (integralSingularChains Space).d (degree + 1) degree =
    (integralSingularChains Space).d (degree + 1) degree ≫
      singularSubdivisionComponent (Space := Space) degree := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, singularSubdivisionComponent_generator]
  simp only [Category.assoc]
  rw [(affineTupleEvaluation _).comm (degree + 1) degree,
    reassoc_of% (affineBarycentricSubdivision (degree + 1)).comm (degree + 1) degree]
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [sum_comp, zsmul_comp]
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [sum_comp, zsmul_comp]
  apply Finset.sum_congr rfl
  intro deleted _present
  simpa only [Category.assoc] using congrArg (fun mapping => ((-1 : ℤ) ^ deleted.val) • mapping)
    (subdivisionFaceEvaluation degree deleted simplex)

noncomputable def singularBarycentricSubdivision : integralSingularChains Space ⟶ integralSingularChains Space where
  f := singularSubdivisionComponent
  comm' source target related := by
    have equal : target + 1 = source := related
    subst source
    exact singularSubdivisionComponent_comm target

theorem singularSubdivisionHomotopyComponent_zero :
    singularSubdivisionHomotopyComponent (Space := Space) 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [singularSubdivisionHomotopyComponent_generator, affineSubdivisionHomotopyValues_zero]
  simp

theorem singularBarycentricSubdivision_zero :
    (singularBarycentricSubdivision (Space := Space)).f 0 = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  change (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex ≫
    singularSubdivisionComponent (Space := Space) 0 = _
  rw [singularSubdivisionComponent_generator]
  change _ ≫ (𝟙 _ ≫ _) = _
  rw [Category.id_comp, standardAffineTuple_evaluation, Category.comp_id]

theorem singularSubdivisionHomotopyComponent_boundary (degree : ℕ) :
    singularSubdivisionHomotopyComponent (Space := Space) (degree + 1) ≫
      (integralSingularChains Space).d (degree + 2) (degree + 1) =
    𝟙 _ - (singularBarycentricSubdivision (Space := Space)).f (degree + 1) -
      (integralSingularChains Space).d (degree + 1) degree ≫
        singularSubdivisionHomotopyComponent (Space := Space) degree := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, singularSubdivisionHomotopyComponent_generator]
  simp only [Category.assoc]
  rw [(affineTupleEvaluation _).comm (degree + 2) (degree + 1),
    reassoc_of% affineSubdivisionHomotopyValues_boundary (degree + 1) degree]
  simp only [sub_comp, comp_sub, Category.comp_id, Category.id_comp, Category.assoc]
  rw [standardAffineTuple_evaluation]
  change _ = _ -
    (TopCat.toSSet.obj (TopCat.of Space)).ιChainComplex (R := AddCommGrpCat.of ℤ) simplex ≫
      singularSubdivisionComponent (Space := Space) (degree + 1) - _
  rw [singularSubdivisionComponent_generator]
  congr 1
  rw [← Category.assoc, ← Category.assoc, SSet.ιChainComplex_d]
  simp only [sum_comp, zsmul_comp, Category.assoc]
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [sum_comp, zsmul_comp]
  apply Finset.sum_congr rfl
  intro deleted _present
  simpa only [Category.assoc] using congrArg (fun mapping => ((-1 : ℤ) ^ deleted.val) • mapping)
    (homotopyFaceEvaluation degree deleted simplex)

noncomputable def singularSubdivisionChainHomotopy :
    Homotopy (𝟙 (integralSingularChains Space)) (singularBarycentricSubdivision (Space := Space)) where
  hom degree := Pi.single (degree + 1) (singularSubdivisionHomotopyComponent degree)
  zero source target unrelated := Pi.single_eq_of_ne (Ne.symm unrelated) _
  comm degree := by
    cases degree with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, zero_add, Homotopy.prevD_chainComplex]
      simp [singularSubdivisionHomotopyComponent_zero, singularBarycentricSubdivision_zero]
    | succ degree =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [Pi.single_eq_same]
      rw [singularSubdivisionHomotopyComponent_boundary]
      change 𝟙 _ = _
      abel

end BondalThomsen.ConvexNerveSmallChainPositiveComparison
