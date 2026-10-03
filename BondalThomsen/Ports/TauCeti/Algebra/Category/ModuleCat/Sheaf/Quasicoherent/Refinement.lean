module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.GeneratingSections

@[expose] public section

open CategoryTheory Limits

namespace TauCeti

universe w u v₁ v₂ u₁ u₂

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

section Map

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R} (P : M.Presentation)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
  (η : unit S ≅ F.obj (unit R))

instance _root_.SheafOfModules.Presentation.isFinite_map [P.IsFinite] :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by simp only [Presentation.map_generators_I]; infer_instance⟩
  isFiniteType_relations := ⟨by simp only [Presentation.map_relations_I]; infer_instance⟩

end Map

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

@[simps I X presentation]
def _root_.SheafOfModules.QuasicoherentData.ofRefinement {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y)
    (index : I → q.I) (map : ∀ i, Y i ⟶ q.X (index i)) : M.QuasicoherentData where
  I := I
  X := Y
  coversTop := coversTop
  presentation i :=
    ((q.presentation (index i)).map (overMap R (map i)) (overMapUnitIso (map i)).symm).ofIsIso
      ((overFunctorMap R (map i)).hom.app M)

def _root_.SheafOfModules.GeneratingSections.restrict {M : SheafOfModules.{u} R} {X Y : C}
    (G : (M.over X).GeneratingSections) (f : Y ⟶ X) : (M.over Y).GeneratingSections :=
  G.mapIso (overMap R f) (overMapUnitIso f).symm ((overFunctorMap R f).app M)

instance _root_.SheafOfModules.GeneratingSections.isIso_restrict_π {M : SheafOfModules.{u} R}
    {X Y : C} (G : (M.over X).GeneratingSections) (f : Y ⟶ X) [IsIso G.π] :
    IsIso (G.restrict f).π :=
  GeneratingSections.isIso_mapIso_π _ _ _ _

instance _root_.SheafOfModules.GeneratingSections.isFiniteType_restrict
    {M : SheafOfModules.{u} R} {X Y : C} (G : (M.over X).GeneratingSections) (f : Y ⟶ X)
    [hG : G.IsFiniteType] : (G.restrict f).IsFiniteType :=
  GeneratingSections.isFiniteType_mapIso _ _ _ _

@[simps I X generators]
def _root_.SheafOfModules.LocalGeneratorsData.ofRefinement {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y)
    (index : I → q.I) (map : ∀ i, Y i ⟶ q.X (index i)) : M.LocalGeneratorsData where
  I := I
  X := Y
  coversTop := coversTop
  generators i := (q.generators (index i)).restrict (map i)

instance {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) [q.IsLocallyFreeData]
    {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y) (index : I → q.I)
    (map : ∀ i, Y i ⟶ q.X (index i)) :
    (q.ofRefinement Y coversTop index map).IsLocallyFreeData where
  isIso _ := GeneratingSections.isIso_restrict_π _ _

instance {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) [q.IsFiniteType]
    {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y) (index : I → q.I)
    (map : ∀ i, Y i ⟶ q.X (index i)) :
    (q.ofRefinement Y coversTop index map).IsFiniteType where
  isFiniteType i := GeneratingSections.isFiniteType_restrict _ _
    (hG := LocalGeneratorsData.IsFiniteType.isFiniteType (index i))

theorem _root_.SheafOfModules.QuasicoherentData.isFinite_ofRefinement_presentation
    {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) [q.IsFinitePresentation]
    {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y) (index : I → q.I)
    (map : ∀ i, Y i ⟶ q.X (index i)) (i : I) :
    ((q.ofRefinement Y coversTop index map).presentation i).IsFinite := by
  rw [QuasicoherentData.ofRefinement_presentation]
  exact @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _
    (((overFunctorMap R (map i)).app M).isIso_hom) _ inferInstance

instance {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) [q.IsFinitePresentation]
    {I : Type w} (Y : I → C) (coversTop : J.CoversTop Y) (index : I → q.I)
    (map : ∀ i, Y i ⟶ q.X (index i)) :
    (q.ofRefinement Y coversTop index map).IsFinitePresentation where
  isFinite_presentation := q.isFinite_ofRefinement_presentation Y coversTop index map

end SheafOfModules

end

end TauCeti
