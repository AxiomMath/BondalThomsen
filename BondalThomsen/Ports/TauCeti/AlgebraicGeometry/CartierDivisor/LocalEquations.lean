module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Basic
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

variable {X} in
def CartierDivisor.IsLocalEquationAt (D : CartierDivisor X) (x : X) (f : X.functionFieldˣ) : Prop :=
  ∃ (V : X.Opens) (hx : x ∈ V),
    haveI : Nonempty V := ⟨⟨x, hx⟩⟩
    rationalUnitClass X V (Additive.ofMul f) = D |_ V

theorem exists_local_equation {U : X.Opens}
    (D : ((cartierDivisorSheaf X).obj.obj (op U) : Type u)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ f : Additive (((rationalFunctionsRing X).presheaf.obj (op V))ˣ),
        ((toCartierDivisorSheaf X).hom.app (op V)).hom f = D |_ V := by
  have hlocal : TopCat.Presheaf.IsLocallySurjective (toCartierDivisorSheaf X).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (toCartierDivisorSheaf X)).mpr inferInstance
  obtain ⟨V, hVU, ⟨f, hf⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (toCartierDivisorSheaf X).hom).mp hlocal
      U D x hx
  exact ⟨V, hVU, hxV, f, hf⟩

theorem toCartierDivisorSheaf_app_eq_iff {U : X.Opens}
    (f g : Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ)) :
    ((toCartierDivisorSheaf X).hom.app (op U)).hom f =
        ((toCartierDivisorSheaf X).hom.app (op U)).hom g ↔
      ∃ r : Additive (((X.presheaf.obj (op U)) : Type u)ˣ),
        ((toRationalUnitSheaf X).hom.app (op U)).hom r = f - g := by
  constructor
  · intro h
    let S : ShortComplex (TopCat.Sheaf AddCommGrpCat X) :=
      ShortComplex.mk (toRationalUnitSheaf X) (toCartierDivisorSheaf X)
        (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)
    have hS : S.Exact := exact_toRationalUnitSheaf_toCartierDivisorSheaf X
    have hzero : ((toCartierDivisorSheaf X).hom.app (op U)).hom (f - g) = 0 :=
      (map_sub _ f g).trans (sub_eq_zero.mpr h)
    exact _root_.TopCat.Sheaf.sections_exact_of_left_exact hS (inferInstance : Mono S.f)
      (f - g) hzero
  · rintro ⟨r, hr⟩
    have hcomp := toRationalUnitSheaf_comp_toCartierDivisorSheaf X
    have happ := congrArg (fun k ↦ k.hom.app (op U)) hcomp
    have hrzero := ConcreteCategory.congr_hom happ r
    have hq_sub : ((toCartierDivisorSheaf X).hom.app (op U)).hom (f - g) = 0 :=
      (congrArg ((toCartierDivisorSheaf X).hom.app (op U)).hom hr.symm).trans hrzero
    apply sub_eq_zero.mp
    exact (map_sub _ f g).symm.trans hq_sub

theorem rationalUnitClass_eq_rationalUnitClass_iff (U : X.Opens) [Nonempty U]
    (f g : X.functionFieldˣ) :
    rationalUnitClass X U (Additive.ofMul f) = rationalUnitClass X U (Additive.ofMul g) ↔
      ∃ r : Γ(X, U)ˣ, regularUnitToFunctionField X U r * g = f := by
  rw [rationalUnitClass_apply, rationalUnitClass_apply, toCartierDivisorSheaf_app_eq_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨Additive.toMul r, Additive.ofMul.injective ?_⟩
    have h := (rationalUnitSectionsEquiv_toRationalUnitSheaf_app X U (Additive.toMul r)).symm.trans
      (congrArg (rationalUnitSectionsEquiv X U) hr)
    rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h
    rw [ofMul_mul, h, sub_add_cancel]
  · rintro ⟨r, hr⟩
    refine ⟨Additive.ofMul r, (rationalUnitSectionsEquiv X U).injective ?_⟩
    refine (rationalUnitSectionsEquiv_toRationalUnitSheaf_app X U r).trans ?_
    rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← hr, ofMul_mul,
      add_sub_cancel_right]

namespace CartierDivisor

variable {X}

lemma rationalUnitClass_eq_of_le {D : CartierDivisor X} {V W : X.Opens} [Nonempty V]
    [Nonempty W] (hWV : W ≤ V) {f : X.functionFieldˣ}
    (hf : rationalUnitClass X V (Additive.ofMul f) = D |_ V) :
    rationalUnitClass X W (Additive.ofMul f) = D |_ W := by
  rw [← rationalUnitClass_restrict X hWV, hf, TopCat.Presheaf.restrict_restrict]

lemma isLocalEquationAt_iff {D : CartierDivisor X} {x : X} {f : X.functionFieldˣ} :
    D.IsLocalEquationAt x f ↔ ∃ (V : X.Opens) (hx : x ∈ V),
      haveI : Nonempty V := ⟨⟨x, hx⟩⟩
      rationalUnitClass X V (Additive.ofMul f) = D |_ V :=
  Iff.rfl

lemma isLocalEquationAt_of_rationalUnitClass_eq {D : CartierDivisor X} {V : X.Opens} [Nonempty V]
    {f : X.functionFieldˣ} (hf : rationalUnitClass X V (Additive.ofMul f) = D |_ V) {x : X}
    (hx : x ∈ V) : D.IsLocalEquationAt x f :=
  ⟨V, hx, hf⟩

lemma IsLocalEquationAt.mul {D E : CartierDivisor X} {x : X} {f g : X.functionFieldˣ}
    (hf : D.IsLocalEquationAt x f) (hg : E.IsLocalEquationAt x g) :
    (D + E).IsLocalEquationAt x (f * g) := by
  obtain ⟨V, hxV, hV⟩ := hf
  obtain ⟨W, hxW, hW⟩ := hg
  have hx : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : Nonempty (V ⊓ W : X.Opens) := ⟨⟨x, hx⟩⟩
  refine ⟨V ⊓ W, hx, ?_⟩
  rw [ofMul_mul, map_add, rationalUnitClass_eq_of_le inf_le_left hV,
    rationalUnitClass_eq_of_le inf_le_right hW]
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_add]

lemma IsLocalEquationAt.inv {D : CartierDivisor X} {x : X} {f : X.functionFieldˣ}
    (hf : D.IsLocalEquationAt x f) : (-D).IsLocalEquationAt x f⁻¹ := by
  obtain ⟨V, hx, hV⟩ := hf
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  refine ⟨V, hx, ?_⟩
  rw [ofMul_inv, map_neg, hV]
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_neg]

lemma isLocalEquationAt_zero (x : X) : (0 : CartierDivisor X).IsLocalEquationAt x 1 := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨x, Opens.mem_top x⟩⟩
  refine ⟨⊤, Opens.mem_top x, ?_⟩
  simp

theorem exists_isLocalEquationAt (D : CartierDivisor X) (x : X) :
    ∃ f : X.functionFieldˣ, D.IsLocalEquationAt x f := by
  obtain ⟨V, hVU, hx, f, hf⟩ := exists_local_equation X D x (Opens.mem_top x)
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  refine ⟨Additive.toMul (rationalUnitSectionsEquiv X V f), V, hx, ?_⟩
  rw [rationalUnitClass_apply]
  exact ((congrArg _ ((rationalUnitSectionsEquiv X V).symm_apply_apply f)).trans hf)

theorem exists_localEquation_le (D : CartierDivisor X) (U : X.Opens) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (_hVU : V ≤ U) (hxV : x ∈ V) (g : X.functionFieldˣ),
      haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
      rationalUnitClass X V (Additive.ofMul g) = D |_ V := by
  obtain ⟨g, hg⟩ := D.exists_isLocalEquationAt x
  obtain ⟨W, hxW, hg⟩ := isLocalEquationAt_iff.mp hg
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : Nonempty (U ⊓ W : X.Opens) := ⟨⟨x, hx, hxW⟩⟩
  exact ⟨U ⊓ W, inf_le_left, ⟨hx, hxW⟩, g,
    rationalUnitClass_eq_of_le inf_le_right hg⟩

theorem IsLocalEquationAt.exists_unit_mul_eq {D : CartierDivisor X} {x : X}
    {f g : X.functionFieldˣ} (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g) :
    ∃ u : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField u * g = f := by
  obtain ⟨V, hxV, hV⟩ := hf
  obtain ⟨W, hxW, hW⟩ := hg
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hx : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  have : Nonempty (V ⊓ W : X.Opens) := ⟨⟨x, hx⟩⟩
  obtain ⟨r, hr⟩ := (rationalUnitClass_eq_rationalUnitClass_iff X (V ⊓ W) f g).mp
    ((rationalUnitClass_eq_of_le inf_le_left hV).trans
      (rationalUnitClass_eq_of_le inf_le_right hW).symm)
  refine ⟨Units.map (X.presheaf.germ (V ⊓ W) x hx).hom.toMonoidHom r, ?_⟩
  rw [← hr, Units.val_mul, regularUnitToFunctionField_apply]
  exact congrArg (· * (g : X.functionField))
    (_root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hx (r : Γ(X, V ⊓ W)))

lemma IsLocalEquationAt.mul_mem_range_iff {D : CartierDivisor X} {x : X}
    {f g : X.functionFieldˣ} (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g)
    (c : X.functionField) :
    (f : X.functionField) * c ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ↔
      (g : X.functionField) * c ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  obtain ⟨u, hu⟩ := hf.exists_unit_mul_eq hg
  have hu' : algebraMap (X.presheaf.stalk x) X.functionField ↑u⁻¹ * f = g := by
    rw [← hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  constructor
  · intro h
    rw [← hu', mul_assoc]
    exact Subring.mul_mem _ (RingHom.mem_range_self _ _) h
  · intro h
    rw [← hu, mul_assoc]
    exact Subring.mul_mem _ (RingHom.mem_range_self _ _) h

lemma isLocalEquationAt_congr {D E : CartierDivisor X} {V : X.Opens} (h : D |_ V = E |_ V)
    {x : X} (hx : x ∈ V) (f : X.functionFieldˣ) :
    D.IsLocalEquationAt x f ↔ E.IsLocalEquationAt x f := by
  suffices key : ∀ {D E : CartierDivisor X}, D |_ V = E |_ V →
      D.IsLocalEquationAt x f → E.IsLocalEquationAt x f from ⟨key h, key h.symm⟩
  intro D E h ⟨W, hxW, hW⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : Nonempty (W ⊓ V : X.Opens) := ⟨⟨x, hxW, hx⟩⟩
  refine isLocalEquationAt_of_rationalUnitClass_eq (V := W ⊓ V) ?_ ⟨hxW, hx⟩
  rw [rationalUnitClass_eq_of_le inf_le_left hW,
    ← TopCat.Presheaf.restrict_restrict (inf_le_right : W ⊓ V ≤ V) le_top D, h,
    TopCat.Presheaf.restrict_restrict]

end CartierDivisor

end Scheme

end

end AlgebraicGeometry

end TauCeti
