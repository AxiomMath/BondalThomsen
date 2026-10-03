module

public import BondalThomsen.Cohomology.FiniteAffineCechFlasqueAcyclicity
public import BondalThomsen.Ports.LeanPool.CohomologyCokernel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.FiniteAffineCechDerivedIso
open BondalThomsen.FiniteAffineCechFlasqueAcyclicity
open BondalThomsen.FiniteQuasicoherentCohomologyTower
open BondalThomsen.FiniteAffineCoverQuasicoherentExtensions
open BondalThomsen.Ports.LeanPool

namespace BondalThomsen.FiniteAffineCechDegreeOneComparison

universe u

noncomputable section

variable {scheme : Scheme.{u}} {Index : Type u}

def cechOneHomologyCokernelIso
    {sequence : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ)}
    (exact_sequence : sequence.ShortExact)
    (middle_zero : IsZero (sequence.X₂.homology 1)) :
    cokernel (HomologicalComplex.homologyMap sequence.g 0) ≅ sequence.X₁.homology 1 := by
  letI := exact_sequence.epi_δ 0 1 rfl middle_zero
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (HomologicalComplex.homologyMap sequence.g 0))
    (exact_sequence.homology_exact₃ 0 1 rfl).gIsCokernel

def globalSectionsUnionIso (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (coefficient : scheme.Modules) :
    coefficient.presheaf.obj (op ⊤) ≅ coefficient.presheaf.obj (op (iSup opens)) :=
  coefficient.presheaf.mapIso (eqToIso (congrArg op cover).symm)

theorem globalSectionsUnionIso_naturality (opens : Index → scheme.Opens)
    (cover : iSup opens = ⊤) {first second : scheme.Modules}
    (coefficient_map : first ⟶ second) :
    coefficient_map.app ⊤ ≫ (globalSectionsUnionIso opens cover second).hom =
      (globalSectionsUnionIso opens cover first).hom ≫ coefficient_map.app (iSup opens) := by
  exact ((PresheafOfModules.toPresheaf.{u} scheme.ringCatSheaf.obj).map
    coefficient_map.val).naturality _ |>.symm

def cechZeroGlobalSectionsIso (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (coefficient : scheme.Modules) :
    coefficient.presheaf.obj (op ⊤) ≅ (schemeCechComplex opens coefficient).homology 0 :=
  globalSectionsUnionIso opens cover coefficient ≪≫ cechZeroSectionsIso opens coefficient

theorem cechZeroGlobalSectionsIso_naturality (opens : Index → scheme.Opens)
    (cover : iSup opens = ⊤) {first second : scheme.Modules}
    (coefficient_map : first ⟶ second) :
    coefficient_map.app ⊤ ≫ (cechZeroGlobalSectionsIso opens cover second).hom =
      (cechZeroGlobalSectionsIso opens cover first).hom ≫
        HomologicalComplex.homologyMap ((schemeCechComplexFunctor opens).map coefficient_map) 0 := by
  dsimp only [cechZeroGlobalSectionsIso, Iso.trans_hom]
  rw [← Category.assoc, globalSectionsUnionIso_naturality, Category.assoc,
    cechZeroSectionsIso_naturality, ← Category.assoc]

def cechOneSchemeCohomologyIso_of_flasque_extension [scheme.IsSeparated] [Finite Index]
    (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (affine : ∀ index, IsAffineOpen (opens index))
    {sequence : ShortComplex scheme.Modules} [sequence.X₁.IsQuasicoherent]
    [sequence.X₂.IsQuasicoherent] [sequence.X₃.IsQuasicoherent]
    [sequence.X₂.presheaf.IsFlasque] (exact_sequence : sequence.ShortExact) :
    AddCommGrpCat.of (Cohomology sequence.X₁ 1) ≅
      (schemeCechComplex opens sequence.X₁).homology 1 :=
  (schemeCohomologyOneCokernelIso exact_sequence
    (AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isFlasque
      sequence.X₂ 0)).symm ≪≫
    cokernel.mapIso (sequence.g.app ⊤)
      (HomologicalComplex.homologyMap ((schemeCechComplexFunctor opens).map sequence.g) 0)
      (cechZeroGlobalSectionsIso opens cover sequence.X₂)
      (cechZeroGlobalSectionsIso opens cover sequence.X₃)
      (cechZeroGlobalSectionsIso_naturality opens cover sequence.g) ≪≫
    cechOneHomologyCokernelIso (schemeCechComplex_shortExact opens affine exact_sequence)
      (standardCech_homology_one_isZero opens sequence.X₂)

end

end BondalThomsen.FiniteAffineCechDegreeOneComparison
