module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Monoidal
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed

@[expose] public section

namespace TauCeti

open AlgebraicGeometry

universe v

noncomputable section

variable (X : Scheme.{v})

open CategoryTheory MonoidalCategory

instance _root_.AlgebraicGeometry.Scheme.Modules.instMonoidalCategory :
    MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

instance _root_.AlgebraicGeometry.Scheme.Modules.instSymmetricCategory :
    SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategory X.sheaf

instance _root_.AlgebraicGeometry.Scheme.Modules.instMonoidalClosed :
    MonoidalClosed X.Modules :=
  SheafOfModules.monoidalClosed X.sheaf

instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊗ N).IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_tensorObj (R := X.sheaf)

instance _root_.AlgebraicGeometry.Scheme.Modules.isMonoidal_isQuasicoherent :
    ObjectProperty.IsMonoidal (C := X.Modules)
      (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf) :=
  SheafOfModules.isMonoidal_isQuasicoherent (R := X.sheaf)

end

end TauCeti
