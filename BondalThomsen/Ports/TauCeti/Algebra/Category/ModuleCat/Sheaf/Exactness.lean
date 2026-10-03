module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section

open CategoryTheory Limits

universe v v' u u'

noncomputable section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace TauCeti

namespace SheafOfModules

open _root_.SheafOfModules

instance preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (toSheaf.{v} R) := by
  constructor
  intro D _ _
  have hLF : PreservesColimitsOfShape D
      (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙ toSheaf.{v} R) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf.{v} (𝟙 R.obj)).symm
  constructor
  intro K
  set L := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
  set G := forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have e : (K ⋙ G) ⋙ L ≅ K :=
    Functor.isoWhiskerLeft K
        (asIso (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).counit) ≪≫
      K.rightUnitor
  have h₁ := isColimitOfPreserves L (colimit.isColimit (K ⋙ G))
  have h₂ := isColimitOfPreserves (L ⋙ toSheaf.{v} R) (colimit.isColimit (K ⋙ G))
  have := preservesColimit_of_preserves_colimit_cocone (F := toSheaf.{v} R) h₁ h₂
  exact preservesColimit_of_iso_diagram _ e

theorem shortExact_map_toSheaf {S : ShortComplex (_root_.SheafOfModules.{v} R)}
    (hS : S.ShortExact) : (S.map (toSheaf.{v} R)).ShortExact :=
  hS.map_of_exact _

end SheafOfModules

end TauCeti

end
