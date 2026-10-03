module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import BondalThomsen.Ports.TauCeti.CategoryTheory.Sites.Units
public import Mathlib.Topology.Sheaves.Abelian

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

noncomputable abbrev regularUnitSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).obj X.sheaf

noncomputable abbrev rationalUnitSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).obj
    (rationalFunctionsRing X)

def toRationalUnitSheaf : regularUnitSheaf X ⟶ rationalUnitSheaf X :=
  (CategoryTheory.Sheaf.additiveUnitsFunctor (Opens.grothendieckTopology X)).map
    (toRationalFunctionsRing X)

theorem toRationalUnitSheaf_app_injective (U : X.Opens) :
    Function.Injective ((toRationalUnitSheaf X).hom.app (op U)) := by
  intro f g h
  apply Additive.toMul.injective
  apply Units.map_injective (toRationalFunctionsRing_app_injective U)
  exact congrArg Additive.toMul h

instance : Mono (toRationalUnitSheaf X) := by
  have hU : ∀ U : (Opens X)ᵒᵖ, Mono ((toRationalUnitSheaf X).hom.app U) := fun U ↦
    ConcreteCategory.mono_of_injective _ (toRationalUnitSheaf_app_injective X U.unop)
  have : Mono (toRationalUnitSheaf X).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ (toRationalUnitSheaf X)

def cartierDivisorSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  cokernel (toRationalUnitSheaf X)

def toCartierDivisorSheaf : rationalUnitSheaf X ⟶ cartierDivisorSheaf X :=
  cokernel.π (toRationalUnitSheaf X)

instance : Epi (toCartierDivisorSheaf X) := by
  dsimp only [toCartierDivisorSheaf]
  exact Cofork.IsColimit.epi (colimit.isColimit _)

@[reassoc (attr := simp)]
lemma toRationalUnitSheaf_comp_toCartierDivisorSheaf :
    toRationalUnitSheaf X ≫ toCartierDivisorSheaf X = 0 :=
  cokernel.condition (toRationalUnitSheaf X)

theorem exact_toRationalUnitSheaf_toCartierDivisorSheaf :
    (ShortComplex.mk (toRationalUnitSheaf X) (toCartierDivisorSheaf X)
      (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)).Exact :=
  ShortComplex.exact_cokernel (toRationalUnitSheaf X)

abbrev CartierDivisor : Type u :=
  ((cartierDivisorSheaf X).obj.obj (op (⊤ : X.Opens)) : Type u)

local instance instNonemptyTopOpens (X : Scheme.{u}) [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice (inferInstanceAs (Nonempty X)), by simp⟩⟩

def rationalUnitSectionsEquiv (U : X.Opens) [Nonempty U] :
    Additive (((rationalFunctionsRing X).presheaf.obj (op U))ˣ) ≃+
      Additive X.functionFieldˣ := by
  exact (Units.mapEquiv (rationalFunctionsRingEquiv U).toMulEquiv).toAdditive

@[simp]
lemma rationalUnitSectionsEquiv_apply (U : X.Opens) [Nonempty U]
    (f : ((rationalFunctionsRing X).presheaf.obj (op U))ˣ) :
    rationalUnitSectionsEquiv X U (Additive.ofMul f) =
      Additive.ofMul (Units.map
        (rationalFunctionsRingEquiv U).toMonoidHom f) := by
  rfl

noncomputable def regularUnitToFunctionField (U : X.Opens) [Nonempty U] :
    ((X.presheaf.obj (op U)) : Type u)ˣ →* X.functionFieldˣ := by
  exact Units.map (X.germToFunctionField U).hom.toMonoidHom

@[simp]
lemma regularUnitToFunctionField_apply (U : X.Opens) [Nonempty U]
    (f : ((X.presheaf.obj (op U)) : Type u)ˣ) :
    regularUnitToFunctionField X U f =
      Units.map (X.germToFunctionField U).hom.toMonoidHom f := by
  rfl

lemma rationalUnitSectionsEquiv_toRationalUnitSheaf_app (U : X.Opens) [Nonempty U]
    (f : ((X.presheaf.obj (op U)) : Type u)ˣ) :
    rationalUnitSectionsEquiv X U
        (((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f)) =
      Additive.ofMul (regularUnitToFunctionField X U f) := by
  have hunit :
      ((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f) =
        Additive.ofMul (Units.map
          ((toRationalFunctionsRing X).hom.app
            (op U)).hom.toMonoidHom f) :=
    CategoryTheory.Sheaf.additiveUnitsFunctor_map_app_apply
      (Opens.grothendieckTopology X) (toRationalFunctionsRing X)
        (op U) (Additive.ofMul f)
  rw [hunit, rationalUnitSectionsEquiv_apply, regularUnitToFunctionField_apply]
  apply congrArg Additive.ofMul
  apply Units.ext
  simp only [Units.coe_map]
  change rationalFunctionsRingEquiv U
      ((toRationalFunctionsRing X).hom.app (op U) (f : Γ(X, U))) =
    X.germToFunctionField U f
  rw [← toRationalFunctionsRing_app, ← rationalFunctionsEquiv_apply,
    rationalFunctionsEquiv_toRationalFunctions_app]

def rationalUnitClass (U : X.Opens) [Nonempty U] :
    Additive X.functionFieldˣ →+ ((cartierDivisorSheaf X).obj.obj (op U) : Type u) :=
  (((toCartierDivisorSheaf X).hom.app (op U)).hom).comp
    (rationalUnitSectionsEquiv X U).symm.toAddMonoidHom

lemma rationalUnitClass_apply (U : X.Opens) [Nonempty U] (g : Additive X.functionFieldˣ) :
    rationalUnitClass X U g = ((toCartierDivisorSheaf X).hom.app (op U)).hom
      ((rationalUnitSectionsEquiv X U).symm g) :=
  AddMonoidHom.comp_apply _ _ _

@[simp]
lemma rationalUnitSectionsEquiv_symm_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (g : Additive X.functionFieldˣ) :
    TopCat.Presheaf.restrictOpen (F := (rationalUnitSheaf X).obj)
        ((rationalUnitSectionsEquiv X U).symm g) V h =
      (rationalUnitSectionsEquiv X V).symm g := by
  apply (rationalUnitSectionsEquiv X V).injective
  rw [AddEquiv.apply_symm_apply]
  set t := (rationalUnitSectionsEquiv X U).symm g with ht
  have hgt : rationalUnitSectionsEquiv X U t = g := by
    rw [ht, AddEquiv.apply_symm_apply]
  have hgt' : g = Additive.ofMul (Units.map
      (rationalFunctionsRingEquiv U).toMonoidHom (Additive.toMul t)) := by
    rw [← hgt]
    exact rationalUnitSectionsEquiv_apply X U (Additive.toMul t)
  have hrestrict :
      TopCat.Presheaf.restrictOpen (F := (rationalUnitSheaf X).obj) t V h =
        Additive.ofMul (Units.map
          ((rationalFunctionsRing X).presheaf.map (homOfLE h).op).hom.toMonoidHom
            (Additive.toMul t)) :=
    CategoryTheory.Sheaf.additiveUnitsFunctor_obj_map_apply
      (Opens.grothendieckTopology X) (rationalFunctionsRing X) (homOfLE h).op t
  rw [hrestrict, hgt', rationalUnitSectionsEquiv_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  simp

@[simp]
lemma rationalUnitClass_restrict {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (g : Additive X.functionFieldˣ) :
    rationalUnitClass X U g |_ V = rationalUnitClass X V g := by
  rw [rationalUnitClass_apply]
  calc
    _ = ((toCartierDivisorSheaf X).hom.app (op V)).hom
          (TopCat.Presheaf.restrictOpen (F := (rationalUnitSheaf X).obj)
            ((rationalUnitSectionsEquiv X U).symm g) V h) :=
      (TopCat.Presheaf.map_restrict (toCartierDivisorSheaf X).hom h _).symm
    _ = _ := by rw [rationalUnitSectionsEquiv_symm_restrict, ← rationalUnitClass_apply]

@[simp]
lemma rationalUnitClass_germToFunctionField_eq_zero (U : X.Opens) [Nonempty U]
    (f : ((X.presheaf.obj (op U)) : Type u)ˣ) :
    rationalUnitClass X U
      (Additive.ofMul (Units.map (X.germToFunctionField U).hom f)) = 0 := by
  have hsymm :
      (rationalUnitSectionsEquiv X U).symm
          (Additive.ofMul (regularUnitToFunctionField X U f)) =
        ((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f) := by
    apply (rationalUnitSectionsEquiv X U).injective
    rw [AddEquiv.apply_symm_apply]
    exact (rationalUnitSectionsEquiv_toRationalUnitSheaf_app X U f).symm
  have hzero :
      ((toCartierDivisorSheaf X).hom.app (op U)).hom
        (((toRationalUnitSheaf X).hom.app (op U)).hom (Additive.ofMul f)) = 0 := by
    have hcomp :
        (toRationalUnitSheaf X).hom ≫ (toCartierDivisorSheaf X).hom = 0 :=
      congrArg (fun morphism => morphism.hom)
        (toRationalUnitSheaf_comp_toCartierDivisorSheaf X)
    have happ : (toRationalUnitSheaf X).hom.app (op U) ≫
        (toCartierDivisorSheaf X).hom.app (op U) = 0 := by
      simpa only [NatTrans.comp_app, CategoryTheory.NatTrans.app_zero] using
        congrArg (fun morphism => morphism.app (op U)) hcomp
    have hhom := congrArg AddCommGrpCat.Hom.hom happ
    rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_zero] at hhom
    exact DFunLike.congr_fun hhom (Additive.ofMul f)
  refine (congrArg (rationalUnitClass X U)
    (congrArg Additive.ofMul (regularUnitToFunctionField_apply X U f).symm)).trans ?_
  rw [rationalUnitClass_apply, hsymm]
  exact hzero

def principalCartierDivisorAddHom : Additive X.functionFieldˣ →+ CartierDivisor X :=
  rationalUnitClass X ⊤

def principalCartierDivisor (f : X.functionFieldˣ) : CartierDivisor X :=
  principalCartierDivisorAddHom X (Additive.ofMul f)

@[simp]
lemma principalCartierDivisor_one : principalCartierDivisor X 1 = 0 :=
  map_zero (principalCartierDivisorAddHom X)

@[simp]
lemma principalCartierDivisor_mul (f g : X.functionFieldˣ) :
    principalCartierDivisor X (f * g) =
      principalCartierDivisor X f + principalCartierDivisor X g :=
  map_add (principalCartierDivisorAddHom X) (Additive.ofMul f) (Additive.ofMul g)

@[simp]
lemma principalCartierDivisor_regularUnitToFunctionField
    (f : ((X.presheaf.obj (op (⊤ : X.Opens))) : Type u)ˣ) :
    principalCartierDivisor X
      (Units.map (X.germToFunctionField (⊤ : X.Opens)).hom f) = 0 :=
  rationalUnitClass_germToFunctionField_eq_zero X ⊤ f

@[simp]
lemma principalCartierDivisorAddHom_restrict (g : Additive X.functionFieldˣ) (U : X.Opens)
    [Nonempty U] :
    (principalCartierDivisorAddHom X g) |_ U = rationalUnitClass X U g :=
  rationalUnitClass_restrict X le_top g

@[simp]
lemma principalCartierDivisor_restrict (f : X.functionFieldˣ) (U : X.Opens) [Nonempty U] :
    (principalCartierDivisor X f) |_ U = rationalUnitClass X U (Additive.ofMul f) :=
  principalCartierDivisorAddHom_restrict X (Additive.ofMul f) U

end Scheme

end

end AlgebraicGeometry

end TauCeti
