module

public import BondalThomsen.Cohomology.FiniteAffineCechDegreeOneComparison
public import BondalThomsen.Cohomology.FiniteAffineCechHigherFlasqueAcyclicity

@[expose] public section

set_option maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.FiniteAffineCechDerivedIso
open BondalThomsen.FiniteAffineCechDegreeOneComparison

open BondalThomsen.FiniteAffineCechFlasqueAcyclicity
open BondalThomsen.FiniteAffineCechHigherFlasqueAcyclicity
open BondalThomsen.FiniteQuasicoherentCohomologyTower
open BondalThomsen.FiniteAffineCoverQuasicoherentExtensions

namespace BondalThomsen.FiniteAffineCechAllDegreeComparison

universe u

noncomputable section

variable {scheme : Scheme.{u}} {Index : Type u}

def schemeCohomologyPositiveBoundaryIso {sequence : ShortComplex scheme.Modules}
    (exactSequence : sequence.ShortExact) [sequence.X₂.presheaf.IsFlasque]
    (degree : ℕ) :
    AddCommGrpCat.of (Cohomology sequence.X₃ (degree + 1)) ≅
      AddCommGrpCat.of (Cohomology sequence.X₁ (degree + 2)) :=
  AddEquiv.toAddCommGrpIso
    (AddEquiv.ofBijective (cohomologyδ exactSequence (degree + 1) (degree + 2) rfl)
    ⟨cohomologyδ_injective_of_isFlasque exactSequence degree,
      cohomologyδ_surjective_of_isFlasque exactSequence (degree + 1) (degree + 2) rfl⟩)

def towerDegreeOneComparison [scheme.IsSeparated] [Finite Index]
    (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (affine : ∀ index, IsAffineOpen (opens index)) (coefficient : scheme.Modules)
    (tower : QuasicoherentResolutionTower coefficient)
    (flasque : ∀ stage, (tower.middle stage).presheaf.IsFlasque) (stage : ℕ) :
    AddCommGrpCat.of (Cohomology (tower.object stage) 1) ≅
      (schemeCechComplex opens (tower.object stage)).homology 1 := by
  letI : (tower.sequence stage).X₁.IsQuasicoherent := tower.object_quasicoherent stage
  letI : (tower.sequence stage).X₂.IsQuasicoherent := tower.middle_quasicoherent stage
  letI : (tower.sequence stage).X₃.IsQuasicoherent := tower.object_quasicoherent (stage + 1)
  letI : (tower.sequence stage).X₂.presheaf.IsFlasque := flasque stage
  exact cechOneSchemeCohomologyIso_of_flasque_extension opens cover affine
    (tower.sequence_shortExact stage)

def towerComparisonStep [scheme.IsSeparated]
    (opens : Index → scheme.Opens) (affine : ∀ index, IsAffineOpen (opens index))
    (coefficient : scheme.Modules) (tower : QuasicoherentResolutionTower coefficient)
    (flasque : ∀ stage, (tower.middle stage).presheaf.IsFlasque)
    (cechAcyclic : ∀ stage degree, IsZero
      ((schemeCechComplex opens (tower.middle stage)).homology (degree + 1)))
    (degree stage : ℕ)
    (previous : AddCommGrpCat.of (Cohomology (tower.object (stage + 1)) (degree + 1)) ≅
      (schemeCechComplex opens (tower.object (stage + 1))).homology (degree + 1)) :
    AddCommGrpCat.of (Cohomology (tower.object stage) (degree + 2)) ≅
      (schemeCechComplex opens (tower.object stage)).homology (degree + 2) := by
  letI : (tower.sequence stage).X₁.IsQuasicoherent := tower.object_quasicoherent stage
  letI : (tower.sequence stage).X₂.IsQuasicoherent := tower.middle_quasicoherent stage
  letI : (tower.sequence stage).X₃.IsQuasicoherent := tower.object_quasicoherent (stage + 1)
  letI : (tower.sequence stage).X₂.presheaf.IsFlasque := flasque stage
  exact (schemeCohomologyPositiveBoundaryIso (tower.sequence_shortExact stage) degree).symm ≪≫
    previous ≪≫
    schemeCechBoundaryIso opens affine (tower.sequence_shortExact stage) (degree + 1)
      (cechAcyclic stage degree) (cechAcyclic stage (degree + 1))

def towerPositiveComparison [scheme.IsSeparated] [Finite Index]
    (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (affine : ∀ index, IsAffineOpen (opens index)) (coefficient : scheme.Modules)
    (tower : QuasicoherentResolutionTower coefficient)
    (flasque : ∀ stage, (tower.middle stage).presheaf.IsFlasque)
    (cechAcyclic : ∀ stage degree, IsZero
      ((schemeCechComplex opens (tower.middle stage)).homology (degree + 1)))
    (degree : ℕ) : ∀ stage,
    AddCommGrpCat.of (Cohomology (tower.object stage) (degree + 1)) ≅
      (schemeCechComplex opens (tower.object stage)).homology (degree + 1) := by
  induction degree with
  | zero => exact towerDegreeOneComparison opens cover affine coefficient tower flasque
  | succ degree previous =>
    intro stage
    exact towerComparisonStep opens affine coefficient tower flasque cechAcyclic degree stage
      (previous (stage + 1))

def cechSchemeCohomologyIso_of_tower [scheme.IsSeparated] [Finite Index]
    (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (affine : ∀ index, IsAffineOpen (opens index)) (coefficient : scheme.Modules)
    (tower : QuasicoherentResolutionTower coefficient)
    (flasque : ∀ stage, (tower.middle stage).presheaf.IsFlasque)
    (cechAcyclic : ∀ stage degree, IsZero
      ((schemeCechComplex opens (tower.middle stage)).homology (degree + 1))) :
    ∀ degree, AddCommGrpCat.of (Cohomology coefficient degree) ≅
      (schemeCechComplex opens coefficient).homology degree
  | 0 => cechZeroSchemeCohomologyIso opens cover coefficient
  | degree + 1 =>
    (cohomologyFunctor scheme (degree + 1)).mapIso tower.initial.symm ≪≫
      towerPositiveComparison opens cover affine coefficient tower flasque cechAcyclic degree 0 ≪≫
      Functor.mapIso ((schemeCechComplexFunctor opens) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) (degree + 1))
        tower.initial

def cechSchemeCohomologyIso_of_flasque_tower [scheme.IsSeparated] [Finite Index]
    (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (affine : ∀ index, IsAffineOpen (opens index)) (coefficient : scheme.Modules)
    (tower : QuasicoherentResolutionTower coefficient)
    (flasque : ∀ stage, (tower.middle stage).presheaf.IsFlasque) (degree : ℕ) :
    AddCommGrpCat.of (Cohomology coefficient degree) ≅
      (schemeCechComplex opens coefficient).homology degree := by
  apply cechSchemeCohomologyIso_of_tower opens cover affine coefficient tower flasque
    (degree := degree)
  intro stage positiveDegree
  let := flasque stage
  exact standardCech_homology_positive_isZero opens (tower.middle stage) positiveDegree

def cechSchemeCohomologyIso_of_noetherian_cover
    [IsLocallyNoetherian scheme] [scheme.IsSeparated] [Finite Index]
    (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (affine : ∀ index, IsAffineOpen (opens index))
    (towerCover : Scheme.AffineOpenCover.{u} scheme) [Finite towerCover.I₀]
    (coefficient : scheme.Modules) [coefficient.IsQuasicoherent] (degree : ℕ) :
    AddCommGrpCat.of (Cohomology coefficient degree) ≅
      (schemeCechComplex opens coefficient).homology degree :=
  cechSchemeCohomologyIso_of_flasque_tower opens cover affine coefficient
    (noetherianQuasicoherentFlasqueResolutionTower towerCover coefficient)
    (noetherianQuasicoherentFlasqueTower_middle_isFlasque towerCover coefficient) degree

def cechSchemeCohomologyIso [IsNoetherian scheme] [scheme.IsSeparated] [Finite Index]
    (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (affine : ∀ index, IsAffineOpen (opens index))
    (coefficient : scheme.Modules) [coefficient.IsQuasicoherent] (degree : ℕ) :
    AddCommGrpCat.of (Cohomology coefficient degree) ≅
      (schemeCechComplex opens coefficient).homology degree :=
  cechSchemeCohomologyIso_of_noetherian_cover opens cover affine
    (finiteAffineOpenCover scheme) coefficient degree

end

end BondalThomsen.FiniteAffineCechAllDegreeComparison

