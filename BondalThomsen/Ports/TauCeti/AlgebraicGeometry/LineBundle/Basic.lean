module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SheafOfModules

variable (X : Scheme.{u})

def LocalTrivializations.ofIsOpenCover {M : X.Modules} {ι : Type u} (W : ι → X.Opens)
    (hW : IsOpenCover W)
    (e : ∀ i, _root_.SheafOfModules.unit (X.ringCatSheaf.over (W i)) ≅ M.over (W i)) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} M :=
  { I := ι
    X := W
    coversTop := (Opens.coversTop_iff (X : Type u) W).mpr hW
    iso := fun i ↦ TauCeti.SheafOfModules.freePUnitIsoUnit
      (X.ringCatSheaf.over (W i)) ≪≫ e i }

def LocalTrivializations.ofForallMem {M : X.Modules} (V : X → X.Opens)
    (hx : ∀ x, x ∈ V x)
    (e : ∀ x, _root_.SheafOfModules.unit (X.ringCatSheaf.over (V x)) ≅ M.over (V x)) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} M :=
  LocalTrivializations.ofIsOpenCover X V
    (TopologicalSpace.IsOpenCover.mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)) e

abbrev isInvertible : ObjectProperty X.Modules :=
  TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf)

instance : (isInvertible X).IsClosedUnderIsomorphisms where
  of_iso e hM := by
    have := hM
    exact TauCeti.SheafOfModules.IsInvertible.of_iso (R := X.ringCatSheaf) e

instance isInvertible_unit :
    isInvertible X (_root_.SheafOfModules.unit X.ringCatSheaf) :=
  TauCeti.SheafOfModules.IsInvertible.of_iso
    (M := _root_.SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1})
    (N := _root_.SheafOfModules.unit X.ringCatSheaf)
    (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf)

end SheafOfModules

variable {X : Scheme.{u}}

abbrev InvertibleSheaf (X : Scheme.{u}) : Type _ :=
  ObjectProperty.FullSubcategory (SheafOfModules.isInvertible X)

namespace InvertibleSheaf

instance (L : InvertibleSheaf X) : SheafOfModules.isInvertible X L.obj :=
  L.property

def free (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    InvertibleSheaf X :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) I, inferInstance⟩

def trivial (X : Scheme.{u}) : InvertibleSheaf X :=
  free X PUnit

@[simp]
lemma trivial_obj (X : Scheme.{u}) :
    (trivial X).obj = SheafOfModules.free (R := X.ringCatSheaf) PUnit :=
  (rfl)

end InvertibleSheaf

end

end AlgebraicGeometry

namespace SheafOfModules.LocalTrivializations

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {U : X.Opens}

noncomputable def unitIsoRestrict
    (e : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) :
    _root_.SheafOfModules.unit (U : AlgebraicGeometry.Scheme).ringCatSheaf ≅
      M.restrict (AlgebraicGeometry.Scheme.Opens.ι U) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.mapIso
      ((TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U)).symm ≪≫ e) ≪≫
    (AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app M

end SheafOfModules.LocalTrivializations

namespace AlgebraicGeometry.SheafOfModules

open _root_.AlgebraicGeometry TopologicalSpace

universe u

variable {X : Scheme.{u}} {M : X.Modules}

theorem isInvertible_iff_exists_isOpenCover :
    isInvertible X M ↔ ∃ (ι : Type u) (W : ι → X.Opens), IsOpenCover W ∧
      ∀ i, Nonempty (_root_.SheafOfModules.unit (W i : Scheme).ringCatSheaf ≅
        M.restrict (W i).ι) := by
  constructor
  · intro hM
    let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
    exact ⟨t.I, t.X, (Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop,
      fun i ↦ ⟨TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict (t.iso i)⟩⟩
  · rintro ⟨ι, W, hW, e⟩
    exact (LocalTrivializations.ofIsOpenCover X W hW fun i ↦
      (Scheme.Modules.overEquiv (W i)).fullyFaithfulFunctor.preimageIso
        ((e i).some ≪≫ ((Scheme.Modules.overFunctorEquiv (W i)).app M).symm)).isInvertible

end AlgebraicGeometry.SheafOfModules

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Opposite

universe u

noncomputable section

variable {X : Scheme.{u}}

def trivializationCoordinateIso (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  e.symm ≪≫ TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U)

def trivializationCoordinate (M : X.Modules) {U W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) (i : W ⟶ U) :
    Γ(M, W) ≃ₗ[Γ(X, W)] Γ(X, W) where
  toFun s := (trivializationCoordinateIso M e).hom.val.app (op (Over.mk i)) s
  invFun r := (trivializationCoordinateIso M e).inv.val.app (op (Over.mk i)) r
  map_add' := map_add _
  map_smul' := ((trivializationCoordinateIso M e).hom.val.app (op (Over.mk i))).hom.map_smul
  left_inv s := Iso.hom_inv_id_apply ((SheafOfModules.forget _ ⋙
    PresheafOfModules.toPresheaf _).mapIso (trivializationCoordinateIso M e) |>.app
      (op (Over.mk i))) (s : Γ(M, W))
  right_inv r := Iso.inv_hom_id_apply ((SheafOfModules.forget _ ⋙
    PresheafOfModules.toPresheaf _).mapIso (trivializationCoordinateIso M e) |>.app
      (op (Over.mk i))) (r : Γ(X, W))

theorem trivializationCoordinate_apply (M : X.Modules) {U W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) (i : W ⟶ U)
    (s : Γ(M, W)) :
    trivializationCoordinate M e i s =
      (trivializationCoordinateIso M e).hom.val.app (op (Over.mk i)) s := by
  rfl

@[simp]
theorem trivializationCoordinate_map (M : X.Modules) {U W W' : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) (i : W ⟶ U)
    (j : W' ⟶ W) (s : Γ(M, W)) :
    trivializationCoordinate M e (j ≫ i) (M.presheaf.map j.op s) =
      X.presheaf.map j.op (trivializationCoordinate M e i s) :=
  ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (trivializationCoordinateIso M e).hom).naturality_apply
      (Over.homMk j : Over.mk (j ≫ i) ⟶ Over.mk i).op s

def trivializationGenerator (M : X.Modules) {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) : Γ(M, V) :=
  (trivializationCoordinate M t (𝟙 V)).symm 1

@[simp]
theorem trivializationCoordinate_map_trivializationGenerator (M : X.Modules) {V W : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V) :
    trivializationCoordinate M t i (M.presheaf.map i.op (trivializationGenerator M t)) = 1 := by
  let c := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (trivializationCoordinateIso M t).inv
  have h := c.naturality_apply (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 V)).op (1 : Γ(X, V))
  have h' : M.presheaf.map i.op (trivializationGenerator M t) =
      (trivializationCoordinate M t i).symm (X.presheaf.map i.op 1) := by
    have hM : M.presheaf.map i.op (trivializationGenerator M t) =
        (M.over V).val.presheaf.map (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 V)).op
          (trivializationGenerator M t) := rfl
    have hX : (X.presheaf.map i.op 1 : Γ(X, W)) =
        (SheafOfModules.unit (X.ringCatSheaf.over V)).val.presheaf.map
          (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 V)).op (1 : Γ(X, V)) := rfl
    rw [hM, hX]
    exact h.symm
  rw [h', map_one, LinearEquiv.apply_symm_apply]

@[simp]
theorem trivializationCoordinate_trivializationGenerator (M : X.Modules) {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) :
    trivializationCoordinate M t (𝟙 V) (trivializationGenerator M t) = 1 := by
  have h := trivializationCoordinate_map_trivializationGenerator M t (𝟙 V)
  rwa [op_id, M.presheaf.map_id, ConcreteCategory.id_apply] at h

theorem eq_trivializationCoordinate_smul_map_trivializationGenerator (M : X.Modules)
    {V W : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V)
    (s : Γ(M, W)) :
    s = trivializationCoordinate M t i s •
      M.presheaf.map i.op (trivializationGenerator M t) := by
  apply (trivializationCoordinate M t i).injective
  rw [LinearEquiv.map_smul, trivializationCoordinate_map_trivializationGenerator,
    smul_eq_mul, mul_one]

theorem existsUnique_eq_smul_map_trivializationGenerator (M : X.Modules) {V W : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V)
    (s : Γ(M, W)) :
    ∃! r : Γ(X, W), s = r • M.presheaf.map i.op (trivializationGenerator M t) := by
  refine ⟨trivializationCoordinate M t i s,
    eq_trivializationCoordinate_smul_map_trivializationGenerator M t i s, ?_⟩
  intro r hr
  rw [hr, LinearEquiv.map_smul, trivializationCoordinate_map_trivializationGenerator,
    smul_eq_mul, mul_one]

theorem existsUnique_map_trivializationGenerator_eq_smul (M : X.Modules) {V₁ V₂ W : X.Opens}
    (t₁ : SheafOfModules.free (R := X.ringCatSheaf.over V₁) PUnit ≅ M.over V₁)
    (t₂ : SheafOfModules.free (R := X.ringCatSheaf.over V₂) PUnit ≅ M.over V₂)
    (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂) :
    ∃! u : Γ(X, W)ˣ, M.presheaf.map i₁.op (trivializationGenerator M t₁) =
      (u : Γ(X, W)) • M.presheaf.map i₂.op (trivializationGenerator M t₂) := by
  obtain ⟨r, hr, hr_unique⟩ := existsUnique_eq_smul_map_trivializationGenerator M t₂ i₂
    (M.presheaf.map i₁.op (trivializationGenerator M t₁))
  obtain ⟨s, hs, -⟩ := existsUnique_eq_smul_map_trivializationGenerator M t₁ i₁
    (M.presheaf.map i₂.op (trivializationGenerator M t₂))
  obtain ⟨r₁, -, h_unique⟩ := existsUnique_eq_smul_map_trivializationGenerator M t₁ i₁
    (M.presheaf.map i₁.op (trivializationGenerator M t₁))
  have hrs : r * s = 1 := by
    refine (h_unique (r * s) ?_).trans (h_unique 1 (one_smul _ _).symm).symm
    beta_reduce
    rw [mul_smul, ← hs, ← hr]
  refine ⟨Units.mkOfMulEqOne r s hrs, hr, fun u hu ↦ Units.ext ?_⟩
  rw [Units.val_mkOfMulEqOne]
  exact hr_unique _ hu

open TopologicalSpace in

theorem exists_mem_trivialization (M : X.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] (x : X) :
    ∃ (V : X.Opens) (_ : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V),
      x ∈ V := by
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
  have ht : ⨆ i, t.X i = ⊤ := by
    simpa only [IsOpenCover] using (Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (ht ▸ Opens.mem_top x : x ∈ ⨆ i, t.X i)
  exact ⟨t.X i, t.iso i, hi⟩

end

end AlgebraicGeometry.Scheme.Modules
