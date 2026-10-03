module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Refinement
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Presentation
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Sites.CoversTop

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}} {M N : SheafOfModules.{u} (ringCatSheaf R)}

@[simps I X presentation]
def _root_.SheafOfModules.QuasicoherentData.tensor (qM : M.QuasicoherentData)
    (qN : N.QuasicoherentData) : (M ⊗ N).QuasicoherentData :=
  let r := GrothendieckTopology.CoversTop.commonRefinement qM.coversTop qN.coversTop
  { I := r.I
    X := r.X
    coversTop := r.coversTop
    presentation i :=
      @Presentation.ofIsIso _ _ _ _ _ _ _ _ (overTensorIso M N (r.X i)).inv (Iso.isIso_inv _)
        (Presentation.tensor (R := R.over (r.X i))
          ((qM.ofRefinement r.X r.coversTop r.leftIndex r.left).presentation i)
          ((qN.ofRefinement r.X r.coversTop r.rightIndex r.right).presentation i)) }

instance isQuasicoherent_tensorObj [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊗ N).IsQuasicoherent :=
  ((IsQuasicoherent.nonempty_quasicoherentData (M := M)).some.tensor
    (IsQuasicoherent.nonempty_quasicoherentData (M := N)).some).isQuasicoherent

instance isMonoidal_isQuasicoherent [HasBinaryProducts C] :
    ObjectProperty.IsMonoidal (isQuasicoherent (ringCatSheaf R)) where
  prop_unit := (isQuasicoherent (ringCatSheaf R)).prop_of_iso
    (freePUnitIsoUnit (ringCatSheaf R)) inferInstance
  prop_tensor M N _ _ := inferInstanceAs (M ⊗ N).IsQuasicoherent

omit [HasPullbacks C] in

theorem isFinite_ofIsIso_overTensorIso_tensor (X : C) (P : (M.over X).Presentation)
    (Q : (N.over X).Presentation) (hP : P.IsFinite) (hQ : Q.IsFinite) :
    (@Presentation.ofIsIso _ _ _ _ _ _ _ _ (overTensorIso M N X).inv (Iso.isIso_inv _)
      (Presentation.tensor (R := R.over X) P Q)).IsFinite :=
  @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _ (Iso.isIso_inv _) _
    (@Presentation.isFinite_tensor _ _ _ (R.over X) _ _ P Q hP hQ)

instance (qM : M.QuasicoherentData) (qN : N.QuasicoherentData) [qM.IsFinitePresentation]
    [qN.IsFinitePresentation] : (qM.tensor qN).IsFinitePresentation where
  isFinite_presentation i := by
    refine isFinite_ofIsIso_overTensorIso_tensor _ _ _ ?_ ?_
    · exact qM.isFinite_ofRefinement_presentation _ _ _ _ i
    · exact qN.isFinite_ofRefinement_presentation _ _ _ _ i

instance isFinitePresentation_tensorObj [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (M ⊗ N).IsFinitePresentation := by
  obtain ⟨qM, _⟩ := IsFinitePresentation.exists_quasicoherentData M
  obtain ⟨qN, _⟩ := IsFinitePresentation.exists_quasicoherentData N
  exact IsFinitePresentation.mk (M := M ⊗ N) ⟨qM.tensor qN, inferInstance⟩

instance isMonoidal_isFinitePresentation [HasBinaryProducts C] :
    ObjectProperty.IsMonoidal (isFinitePresentation (ringCatSheaf R)) where
  prop_unit := (isFinitePresentation (ringCatSheaf R)).prop_of_iso
    (freePUnitIsoUnit (ringCatSheaf R)) inferInstance
  prop_tensor M N _ _ := inferInstanceAs (M ⊗ N).IsFinitePresentation

end SheafOfModules

end

end TauCeti
