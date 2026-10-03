module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.RationalFunctions

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

variable {X : Scheme.{u}} [IsIntegral X]

theorem map_injective_on_chart (L : InvertibleSheaf X) {T U V : X.Opens}
    (e : L.obj.over T ≅ SheafOfModules.unit (X.ringCatSheaf.over T))
    (i : V ⟶ U) (hU : U ≤ T) [Nonempty V] :
    Function.Injective (L.obj.presheaf.map i.op) := by
  let e' : (L.obj.over T).val.presheaf ≅
      (SheafOfModules.unit (X.ringCatSheaf.over T)).val.presheaf :=
    (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso e
  let A : Over T := Over.mk (homOfLE hU)
  let B : Over T := Over.mk (homOfLE (i.le.trans hU))
  let f : B ⟶ A := Over.homMk i
  have hnat (s : Γ(L.obj, U)) :
      e'.hom.app (op B) (L.obj.presheaf.map i.op s) =
        X.presheaf.map i.op (e'.hom.app (op A) s) :=
    e'.hom.naturality_apply f.op s
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (e'.hom.app (op A))).injective
  apply AlgebraicGeometry.map_injective_of_isIntegral X i
  rw [← hnat, ← hnat, hab]

theorem map_injective_of_isIntegral (L : InvertibleSheaf X) {U V : X.Opens} (i : V ⟶ U)
    [Nonempty V] : Function.Injective (L.obj.presheaf.map i.op) := by
  classical
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible L.obj
  let W : t.I → X.Opens := fun j ↦ U ⊓ t.X j
  intro a b hab
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨L.obj.presheaf, L.obj.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    W U (fun _ ↦ homOfLE inf_le_left)
  · intro x hx
    have hcover := (Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop
    rw [IsOpenCover] at hcover
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcover.symm ▸ Opens.mem_top x)
    exact Opens.mem_iSup.mpr ⟨j, hx, hj⟩
  · intro j
    by_cases hW : Nonempty (W j)
    · let := hW
      let Z : X.Opens := V ⊓ W j
      have : Nonempty Z := ⟨⟨genericPoint X,
        Scheme.genericPoint_mem V, Scheme.genericPoint_mem (W j)⟩⟩
      apply map_injective_on_chart L
        ((t.iso j).symm ≪≫
          TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over (t.X j)))
        (homOfLE (inf_le_right : Z ≤ W j)) inf_le_right
      have h := congrArg (L.obj.presheaf.map (homOfLE (inf_le_left : Z ≤ V)).op) hab
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at h ⊢
      exact h
    · apply TopCat.Presheaf.section_ext
        (⟨L.obj.presheaf, L.obj.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
      intro x hx
      exact (hW ⟨⟨x, hx⟩⟩).elim

theorem germ_injective_of_isIntegral (L : InvertibleSheaf X) {U : X.Opens} (x : X)
    (hx : x ∈ U) :
    Function.Injective (L.obj.presheaf.germ U x hx) := by
  intro a b hab
  obtain ⟨V, hxV, i, j, h⟩ := L.obj.presheaf.germ_eq x hx hx a b hab
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact L.map_injective_of_isIntegral i (by simpa only [Subsingleton.elim j i] using h)

end TauCeti.AlgebraicGeometry.InvertibleSheaf
