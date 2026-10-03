module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

def freeTensorFreeIso (I I' : Type u) :
    free (R := ringCatSheaf R) I ⊗ free I' ≅ free (I × I') :=
  (isColimitFreeCofan (R := ringCatSheaf R) (I × I')).coconePointsIsoOfNatIso
    (Cofan.IsColimit.prod
      (fun _ ↦ Cofan.mk (unit _ ⊗ free I') fun j ↦ unit _ ◁ ιFree j)
      (fun _ ↦ isColimitCofanMkObjOfIsColimit (tensorLeft (unit _)) _ _
        (isColimitFreeCofan (R := ringCatSheaf R) I'))
      (Cofan.mk (free I ⊗ free I') fun i ↦ ιFree i ▷ free I')
      (isColimitCofanMkObjOfIsColimit (tensorRight (free I')) _ _
        (isColimitFreeCofan (R := ringCatSheaf R) I)))
    (Discrete.natIso fun _ ↦ (λ_ (unit (ringCatSheaf R))).symm)
  |>.symm

variable {M N : SheafOfModules.{u} (ringCatSheaf R)}

@[simps! generators_I relations_I relations_s]
def _root_.SheafOfModules.Presentation.tensor (P : M.Presentation) (Q : N.Presentation) :
    (M ⊗ N).Presentation :=
  presentationOfIsCokernelFree
    (ι := P.relations.I × Q.generators.I ⊕ P.generators.I × Q.relations.I)
    (σ := P.generators.I × Q.generators.I)
    ((freeSumIso _ _).inv ≫ coprod.map (freeTensorFreeIso _ _).inv (freeTensorFreeIso _ _).inv ≫
      coprod.desc
        (((freeHomEquiv _).symm P.relations.s ≫ kernel.ι _) ▷ free Q.generators.I)
        (free P.generators.I ◁ ((freeHomEquiv _).symm Q.relations.s ≫ kernel.ι _)) ≫
      (freeTensorFreeIso _ _).hom)
    ((freeTensorFreeIso _ _).inv ≫ (P.generators.π ⊗ₘ Q.generators.π))
    (by
      have h := ((CokernelCofork.ofπ (f := (freeHomEquiv _).symm P.relations.s ≫ kernel.ι _)
        P.generators.π (by simp)).tensor
        (CokernelCofork.ofπ (f := (freeHomEquiv _).symm Q.relations.s ≫ kernel.ι _)
          Q.generators.π (by simp))).condition
      simp only [CokernelCofork.π_ofπ] at h
      simp only [Category.assoc, Iso.hom_inv_id_assoc, h, comp_zero]) <|
  IsCokernel.ofIso _ (CokernelCofork.isColimitTensor P.isColimit Q.isColimit) _
    (coprod.mapIso (freeTensorFreeIso _ _) (freeTensorFreeIso _ _) ≪≫ freeSumIso _ _)
    (freeTensorFreeIso _ _) (Iso.refl _) (by simp) (by simp)

instance _root_.SheafOfModules.Presentation.isFinite_tensor (P : M.Presentation)
    (Q : N.Presentation) [P.IsFinite] [Q.IsFinite] :
    (P.tensor Q).IsFinite where
  isFiniteType_generators := ⟨by simp only [Presentation.tensor_generators_I]; infer_instance⟩
  isFiniteType_relations := ⟨by simp only [Presentation.tensor_relations_I]; infer_instance⟩

end SheafOfModules

end

end TauCeti
