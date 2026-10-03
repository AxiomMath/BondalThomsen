module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sheaves.Flasque
public import Challenge.Defs.Ports.TauCeti.AlgebraicGeometry.Modules.GlobalSections

@[expose] public section
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite
namespace TauCeti
namespace AlgebraicGeometry
universe u
noncomputable section
namespace Scheme
variable (X : Scheme.{u}) [IrreducibleSpace X]
def fromSpecFunctionField : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

variable {X}
theorem germ_smul_functionField {U : X.Opens} [Nonempty U] {x : X} (hx : x ∈ U) (r : Γ(X, U))
    (f : X.functionField) : X.presheaf.germ U x hx r • f = r • f :=
  sorry

def rationalFunctionsRing (X : Scheme.{u}) [IrreducibleSpace X] :
    TopCat.Sheaf CommRingCat X :=
  (TopCat.Sheaf.pushforward CommRingCat (fromSpecFunctionField X).base).obj
    (Spec X.functionField).sheaf

def toRationalFunctionsRing (X : Scheme.{u}) [IrreducibleSpace X] :
    X.sheaf ⟶ rationalFunctionsRing X where
  hom := (fromSpecFunctionField X).c

def rationalFunctions (X : Scheme.{u}) [IrreducibleSpace X] : X.Modules :=
  (Scheme.Modules.pushforward (fromSpecFunctionField X)).obj (SheafOfModules.unit _)

@[simp]
theorem fromSpecFunctionField_preimage (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X) ⁻¹ᵁ U = ⊤ :=
  sorry

def functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U) ≅ X.functionField :=
  ((Spec X.functionField).presheaf.mapIso
    (eqToIso (fromSpecFunctionField_preimage U)).op).symm ≪≫ Scheme.ΓSpecIso X.functionField

def rationalFunctionsRingEquiv (U : X.Opens) [Nonempty U] :
    ((rationalFunctionsRing X).presheaf.obj (.op U) : Type u) ≃+* X.functionField :=
  (functionFieldSectionsIso U).commRingCatIsoToRingEquiv

theorem app_comp_functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X).app U ≫ (functionFieldSectionsIso U).hom =
      X.germToFunctionField U :=
  sorry

def rationalFunctionsEquiv (U : X.Opens) [Nonempty U] :
    Γ(rationalFunctions X, U) ≃ₗ[Γ(X, U)] X.functionField :=
  { rationalFunctionsRingEquiv U with
    map_smul' r s := by
      change (functionFieldSectionsIso U).hom (r • s) =
        r • (functionFieldSectionsIso U).hom s
      have h : (functionFieldSectionsIso U).hom (r • s) =
          (functionFieldSectionsIso U).hom ((fromSpecFunctionField X).app U r *
            (id s : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U))) := rfl
      rw [h, map_mul, ← CategoryTheory.ConcreteCategory.comp_apply,
        app_comp_functionFieldSectionsIso, Algebra.smul_def]
      rfl
  }

@[simp]
theorem rationalFunctionsEquiv_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V)
    (s : Γ(rationalFunctions X, V)) :
    rationalFunctionsEquiv U ((rationalFunctions X).presheaf.map i.op s) =
      rationalFunctionsEquiv V s :=
  sorry

section SectionsMul
end SectionsMul
section Mul
variable (X)
variable {X}
end Mul
variable [IsIntegral X]
end Scheme
end
end AlgebraicGeometry
end TauCeti
end
