module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory

namespace BondalThomsen

universe schemeUniverse

variable {Source Target : Scheme.{schemeUniverse}}

noncomputable def pullbackGeneratingSections (morphism : Source ⟶ Target)
    {sheaf : Target.Modules} (generators : sheaf.GeneratingSections) :
    ((Scheme.Modules.pullback morphism).obj sheaf).GeneratingSections := by
  letI : CategoryTheory.Limits.PreservesColimitsOfSize.{schemeUniverse, schemeUniverse}
      (Scheme.Modules.pullback morphism) :=
    (Scheme.Modules.pullbackPushforwardAdjunction morphism).leftAdjoint_preservesColimits
  exact generators.map (Scheme.Modules.pullback morphism)
    (Scheme.Modules.pullbackObjUnitIso morphism).symm

theorem globallyGenerated_pullback (morphism : Source ⟶ Target)
    (sheaf : Target.Modules) (generated : Nonempty sheaf.GeneratingSections) :
    Nonempty ((Scheme.Modules.pullback morphism).obj sheaf).GeneratingSections :=
  generated.map (pullbackGeneratingSections morphism)

end BondalThomsen
