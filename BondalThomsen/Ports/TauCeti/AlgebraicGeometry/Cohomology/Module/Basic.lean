module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Cohomology.Basic
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.GlobalSections

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyAction
    (M : X.Modules) (i : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (Cohomology M i) where
  toFun r := ((cohomologyFunctor X i).map (globalSectionsSmul M r)).hom
  map_one' := by
    ext x
    rw [globalSectionsSmul_one]
    exact ConcreteCategory.congr_hom ((cohomologyFunctor X i).map_id M) x
  map_mul' r s := by
    ext x
    rw [globalSectionsSmul_mul, Functor.map_comp]
    rfl
  map_zero' := by
    ext x
    rw [globalSectionsSmul_zero]
    exact ConcreteCategory.congr_hom (Functor.map_zero (cohomologyFunctor X i) M M) x
  map_add' r s := by
    ext x
    rw [globalSectionsSmul_add, Functor.map_add]
    rfl

instance _root_.AlgebraicGeometry.Scheme.Modules.cohomologyModule
    (M : X.Modules) (i : ℕ) : Module Γ(X, ⊤) (Cohomology M i) :=
  Module.compHom (Cohomology M i) (cohomologyAction M i)

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
