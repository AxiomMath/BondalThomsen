module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Refinement
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Adjunction.Mates

@[expose] public section

set_option maxRecDepth 4096

open CategoryTheory Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe w u

noncomputable section

variable {X Y : Scheme.{u}}

section Unit

variable {Z : Scheme.{u}}

def pullbackObjUnitIso (f : X ⟶ Y) : (pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  let : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) this

@[simp]
lemma pullbackObjUnitIso_hom (f : X ⟶ Y) :
    (pullbackObjUnitIso f).hom =
      (letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
        inferInstanceAs (pushforward f).IsRightAdjoint
       SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := by
  rfl

lemma pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom (f : X ⟶ Y) :
    (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackObjUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  Equiv.apply_symm_apply _ _

lemma unitToPushforwardObjUnit_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (pushforward g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (pushforwardComp f g).hom.app _ =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom := by
  ext U
  rfl

@[reassoc]
lemma pullbackObjUnitIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackComp f g).inv.app _ ≫ (pullback f).map (pullbackObjUnitIso g).hom ≫
      (pullbackObjUnitIso f).hom = (pullbackObjUnitIso (f ≫ g)).hom := by
  apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [← Adjunction.homEquiv_conjugateEquiv ((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f)), conjugateEquiv_pullbackComp_inv,
    Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
  refine (congrArg (· ≫ (pushforwardComp f g).hom.app _)
    ((pullbackPushforwardAdjunction g).homEquiv_naturality_right _ _)).trans ?_
  rw [pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom]
  exact (Category.assoc _ _ _).trans (unitToPushforwardObjUnit_comp f g)

end Unit

section Over

variable (f : X ⟶ Y)

def restrictPullbackObjIso (V : Y.Opens) (M : Y.Modules) :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ V).ι ≅ (pullback (f ∣_ V)).obj (M.restrict V.ι) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app _ ≪≫ (pullbackComp (f ⁻¹ᵁ V).ι f).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f V).symm).app M ≪≫
    ((pullbackComp (f ∣_ V) V.ι).app M).symm ≪≫
    (pullback (f ∣_ V)).mapIso ((restrictFunctorIsoPullback V.ι).app M).symm

variable (V : Y.Opens)

def pullbackOver : SheafOfModules (Y.ringCatSheaf.over V) ⥤
    SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ V)) :=
  (overEquiv V).functor ⋙ pullback (f ∣_ V) ⋙ (overEquiv (f ⁻¹ᵁ V)).inverse

instance : (pullbackOver f V).IsLeftAdjoint := by
  unfold pullbackOver
  infer_instance

def pullbackOverUnitIso :
    SheafOfModules.unit _ ≅ (pullbackOver f V).obj (SheafOfModules.unit _) :=
  (overEquiv (f ⁻¹ᵁ V)).unitIso.app _ ≪≫
    (overEquiv (f ⁻¹ᵁ V)).inverse.mapIso (pullbackObjUnitIso (f ∣_ V)).symm

def pullbackOverObjIso (M : Y.Modules) :
    (pullbackOver f V).obj (M.over V) ≅ ((pullback f).obj M).over (f ⁻¹ᵁ V) :=
  ((overEquiv (f ⁻¹ᵁ V)).inverse.mapIso
      ((overFunctorEquiv (f ⁻¹ᵁ V)).app _ ≪≫ restrictPullbackObjIso f V M ≪≫
        (pullback (f ∣_ V)).mapIso ((overFunctorEquiv V).app M).symm)).symm ≪≫
    ((overEquiv (f ⁻¹ᵁ V)).unitIso.app _).symm

end Over

@[simps I X generators]
def _root_.SheafOfModules.LocalGeneratorsData.pullback {M : Y.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{w} (R := Y.ringCatSheaf) M) (f : X ⟶ Y) :
    SheafOfModules.LocalGeneratorsData.{w} (R := X.ringCatSheaf) ((pullback f).obj M) where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := by
    have hq := (Opens.coversTop_iff _ _).mp q.coversTop
    rw [Opens.coversTop_iff, IsOpenCover, ← Scheme.Hom.preimage_iSup, hq.iSup_eq_top,
      Scheme.Hom.preimage_top]
  generators i :=
    (q.generators i).mapIso (pullbackOver f (q.X i)) (pullbackOverUnitIso f _)
      (pullbackOverObjIso f _ M)

instance {M : Y.Modules} (q : SheafOfModules.LocalGeneratorsData.{w} (R := Y.ringCatSheaf) M)
    [q.IsFiniteType] (f : X ⟶ Y) : (q.pullback f).IsFiniteType where
  isFiniteType i := SheafOfModules.GeneratingSections.isFiniteType_mapIso (q.generators i)
    (pullbackOver f (q.X i)) (pullbackOverUnitIso f _) (pullbackOverObjIso f _ M)
    (hσ := SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i)

instance {M : Y.Modules} (q : SheafOfModules.LocalGeneratorsData.{w} (R := Y.ringCatSheaf) M)
    [q.IsLocallyFreeData] (f : X ⟶ Y) : (q.pullback f).IsLocallyFreeData where
  isIso i := by
    let := SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) i
    change IsIso ((q.generators i).mapIso (pullbackOver f (q.X i))
      (pullbackOverUnitIso f _) (pullbackOverObjIso f _ M)).π
    exact SheafOfModules.GeneratingSections.isIso_mapIso_π (q.generators i)
      (pullbackOver f (q.X i)) (pullbackOverUnitIso f _) (pullbackOverObjIso f _ M)

@[simps I X presentation]
def _root_.SheafOfModules.QuasicoherentData.pullback {M : Y.Modules}
    (q : SheafOfModules.QuasicoherentData.{w} (R := Y.ringCatSheaf) M) (f : X ⟶ Y) :
    SheafOfModules.QuasicoherentData.{w} (R := X.ringCatSheaf) ((pullback f).obj M) where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := (q.localGeneratorsData.pullback f).coversTop
  presentation i :=
    ((q.presentation i).map (pullbackOver f (q.X i)) (pullbackOverUnitIso f _)).ofIsIso
      (pullbackOverObjIso f _ M).hom

instance {M : Y.Modules} (q : SheafOfModules.QuasicoherentData.{w} (R := Y.ringCatSheaf) M)
    [q.IsFinitePresentation] (f : X ⟶ Y) : (q.pullback f).IsFinitePresentation where
  isFinite_presentation i :=
    have := SheafOfModules.QuasicoherentData.IsFinitePresentation.isFinite_presentation (q := q) i
    SheafOfModules.instIsFiniteOfIsIso (pullbackOverObjIso f _ M).hom _

instance isQuasicoherent_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent :=
  ((SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)).some.pullback
    f).isQuasicoherent

instance isFiniteType_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType := by
  obtain ⟨q, _⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (M := M)
  exact SheafOfModules.IsFiniteType.mk (R := X.ringCatSheaf) ⟨q.pullback f, inferInstance⟩

instance isFinitePresentation_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsFinitePresentation] :
    ((pullback f).obj M).IsFinitePresentation := by
  obtain ⟨q, _⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  exact SheafOfModules.IsFinitePresentation.mk (R := X.ringCatSheaf) ⟨q.pullback f, inferInstance⟩

instance isLocallyFree_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsLocallyFree] :
    ((pullback f).obj M).IsLocallyFree := by
  obtain ⟨q, _⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  exact (q.pullback f).isLocallyFree

end

end AlgebraicGeometry.Scheme.Modules
