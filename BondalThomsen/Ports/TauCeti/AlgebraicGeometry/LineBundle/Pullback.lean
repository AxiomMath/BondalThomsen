module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.Pullback
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic

@[expose] public section

open CategoryTheory TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace SheafOfModules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance isInvertible_pullback (M : Y.Modules) [hM : isInvertible Y M] :
    isInvertible X ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨ι, V, hV, e⟩ :=
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mp hM
  refine TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
    ⟨ι, fun i ↦ f ⁻¹ᵁ V i, ?_, fun i ↦
      ⟨(Scheme.Modules.pullbackObjUnitIso (f ∣_ V i)).symm ≪≫
        (Scheme.Modules.pullback (f ∣_ V i)).mapIso (e i).some ≪≫
        (Scheme.Modules.restrictPullbackObjIso f (V i) M).symm⟩⟩
  rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hV.iSup_eq_top, Scheme.Hom.preimage_top]

end SheafOfModules

namespace InvertibleSheaf

variable {X Y : Scheme.{u}}

def pullback (f : X ⟶ Y) : InvertibleSheaf Y ⥤ InvertibleSheaf X :=
  (SheafOfModules.isInvertible X).lift
    ((SheafOfModules.isInvertible Y).ι ⋙ Scheme.Modules.pullback f)
    fun L ↦ SheafOfModules.isInvertible_pullback f L.obj

@[simp]
lemma pullback_obj_obj (f : X ⟶ Y) (L : InvertibleSheaf Y) :
    ((pullback f).obj L).obj = (Scheme.Modules.pullback f).obj L.obj :=
  (rfl)

@[simp]
lemma pullback_map (f : X ⟶ Y) {L K : InvertibleSheaf Y} (φ : L ⟶ K) :
    ((pullback f).map φ).hom =
      eqToHom (pullback_obj_obj f L) ≫ (Scheme.Modules.pullback f).map φ.hom ≫
        eqToHom (pullback_obj_obj f K).symm := by
  cases pullback_obj_obj f L
  cases pullback_obj_obj f K
  unfold pullback
  simp

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
