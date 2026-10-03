module

public import BondalThomsen.Ports.TauCeti.Algebra.Category.ModuleCat.Sheaf.Submodule
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.LocalEquations
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X]

namespace CartierDivisor

def sections (D : CartierDivisor X) (U : X.Opens) :
    Submodule Γ(X, U) Γ(rationalFunctions X, U) where
  carrier := {s | ∀ (x : X) (hx : x ∈ U) (f : X.functionFieldˣ), D.IsLocalEquationAt x f →
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    (f : X.functionField) * rationalFunctionsEquiv U s ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range}
  zero_mem' := by
    intro x hx f _
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_zero, mul_zero]
    exact Subring.zero_mem _
  add_mem' := by
    intro s t hs ht x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_add, mul_add]
    exact Subring.add_mem _ (hs x hx f hf) (ht x hx f hf)
  smul_mem' := by
    intro r s hs x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_smul, ← germ_smul_functionField hx, Algebra.smul_def, mul_left_comm]
    exact Subring.mul_mem _ (RingHom.mem_range_self _ _) (hs x hx f hf)

lemma mem_sections {D : CartierDivisor X} {U : X.Opens} {s : Γ(rationalFunctions X, U)} :
    s ∈ D.sections U ↔ ∀ (x : X) (hx : x ∈ U) (f : X.functionFieldˣ),
      D.IsLocalEquationAt x f →
        haveI : Nonempty U := ⟨⟨x, hx⟩⟩
        (f : X.functionField) * rationalFunctionsEquiv U s ∈
          (algebraMap (X.presheaf.stalk x) X.functionField).range :=
  Iff.rfl

theorem mem_sections_iff_exists {D : CartierDivisor X} {U : X.Opens}
    {s : Γ(rationalFunctions X, U)} :
    s ∈ D.sections U ↔ ∀ (x : X) (hx : x ∈ U), ∃ f : X.functionFieldˣ,
      D.IsLocalEquationAt x f ∧
        haveI : Nonempty U := ⟨⟨x, hx⟩⟩
        (f : X.functionField) * rationalFunctionsEquiv U s ∈
          (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  constructor
  · intro hs x hx
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
    exact ⟨f, hf, hs x hx f hf⟩
  · intro hs x hx g hg
    obtain ⟨f, hf, hmem⟩ := hs x hx
    exact (hf.mul_mem_range_iff hg _).mp hmem

lemma sections_map {D : CartierDivisor X} {U V : X.Opens} (i : V ⟶ U)
    {s : Γ(rationalFunctions X, U)} (hs : s ∈ D.sections U) :
    (rationalFunctions X).presheaf.map i.op s ∈ D.sections V := by
  intro x hx f hf
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : Nonempty U := ⟨⟨x, i.le hx⟩⟩
  rw [rationalFunctionsEquiv_map]
  exact hs x (i.le hx) f hf

theorem mem_sections_iff_of_rationalUnitClass_eq {D : CartierDivisor X} {V W : X.Opens}
    [Nonempty V] [Nonempty W] (hWV : W ≤ V) {f : X.functionFieldˣ}
    (hf : rationalUnitClass X V (Additive.ofMul f) = D |_ V) {s : Γ(rationalFunctions X, W)} :
    s ∈ D.sections W ↔
      ∃ a : Γ(X, W), X.germToFunctionField W a = f * rationalFunctionsEquiv W s := by
  have hfW := rationalUnitClass_eq_of_le hWV hf
  constructor
  · intro hs
    exact exists_germToFunctionField_eq_of_forall_mem_range fun y hy ↦
      hs y hy f (isLocalEquationAt_of_rationalUnitClass_eq hfW hy)
  · rintro ⟨a, ha⟩
    refine mem_sections_iff_exists.mpr fun x hx ↦
      ⟨f, isLocalEquationAt_of_rationalUnitClass_eq hfW hx, ?_⟩
    rw [← ha, ← _root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hx]
    exact RingHom.mem_range_self _ _

lemma sections_congr {D E : CartierDivisor X} {V W : X.Opens} (h : D |_ V = E |_ V)
    (hWV : W ≤ V) : D.sections W = E.sections W := by
  ext s
  simp only [mem_sections]
  exact forall_congr' fun x ↦ forall_congr' fun hx ↦ forall_congr' fun f ↦
    imp_congr_left (isLocalEquationAt_congr h (hWV hx) f)

def submodule (D : CartierDivisor X) : (rationalFunctions X).Submodule where
  obj U := D.sections U.unop
  map i := fun {_} hs ↦ sections_map i.unop hs
  isSheaf {U} s hs := by
    intro x hx f hf
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U.unop := ⟨⟨x, hx⟩⟩
    have hi' : (rationalFunctions X).presheaf.map i.op s ∈ D.sections V := hi
    rw [← rationalFunctionsEquiv_map i s]
    exact hi' x hxV f hf

@[simp]
lemma submodule_obj (D : CartierDivisor X) (U : (Opens X)ᵒᵖ) :
    D.submodule.toSubmodule.obj U = D.sections U.unop := by
  induction U using Opposite.rec
  rfl

def sheaf (D : CartierDivisor X) : X.Modules :=
  D.submodule.toSheafOfModules

def sheafι (D : CartierDivisor X) : D.sheaf ⟶ rationalFunctions X :=
  D.submodule.ι

def sectionMk {D : CartierDivisor X} {U : X.Opens} (s : Γ(rationalFunctions X, U))
    (hs : s ∈ D.sections U) : Γ(D.sheaf, U) :=
  ⟨s, hs⟩

lemma sheafι_app_injective (D : CartierDivisor X) (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app D.sheafι U) :=
  TauCeti.SheafOfModules.ι_val_app_injective D.submodule (op U)

@[simp]
lemma sheafι_app_sectionMk {D : CartierDivisor X} {U : X.Opens}
    (s : Γ(rationalFunctions X, U)) (hs : s ∈ D.sections U) :
    Scheme.Modules.Hom.app D.sheafι U (sectionMk s hs) = s :=
  (rfl)

lemma sheafι_app_mem (D : CartierDivisor X) (U : X.Opens) (t : Γ(D.sheaf, U)) :
    Scheme.Modules.Hom.app D.sheafι U t ∈ D.sections U :=
  TauCeti.SheafOfModules.ι_val_app_mem D.submodule (op U) t

instance (D : CartierDivisor X) : Mono D.sheafι :=
  SheafOfModules.Submodule.instMonoι D.submodule

instance (D : CartierDivisor X) (V : X.Opens) : Mono (D.sheafι.over V) :=
  SheafOfModules.Submodule.instMonoιOver D.submodule V

def sheafLift {M : X.Modules} (D : CartierDivisor X) (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U) :
    M ⟶ D.sheaf :=
  TauCeti.SheafOfModules.liftToSubmodule D.submodule φ fun U s ↦ hφ U.unop s

@[reassoc (attr := simp)]
lemma sheafLift_ι {M : X.Modules} (D : CartierDivisor X) (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U) :
    D.sheafLift φ hφ ≫ D.sheafι = φ :=
  TauCeti.SheafOfModules.liftToSubmodule_ι _ _ _

@[simp]
lemma sheafι_app_sheafLift {M : X.Modules} (D : CartierDivisor X)
    (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U)
    (U : X.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app D.sheafι U (Scheme.Modules.Hom.app (D.sheafLift φ hφ) U s) =
      Scheme.Modules.Hom.app φ U s :=
  TauCeti.SheafOfModules.liftToSubmodule_val_app_coe D.submodule φ
    (fun V t ↦ hφ V.unop t) (op U) s

theorem isIso_sheafLift {M : X.Modules} (D : CartierDivisor X) (φ : M ⟶ rationalFunctions X)
    (hφ : ∀ (U : X.Opens) (s : Γ(M, U)), Scheme.Modules.Hom.app φ U s ∈ D.sections U)
    (hinj : ∀ U : X.Opens, Function.Injective (Scheme.Modules.Hom.app φ U))
    (hsurj : ∀ (U : X.Opens) (s : Γ(rationalFunctions X, U)),
      s ∈ D.sections U → ∃ t, Scheme.Modules.Hom.app φ U t = s) :
    IsIso (D.sheafLift φ hφ) :=
  TauCeti.SheafOfModules.isIso_liftToSubmodule _ _ _ (fun U ↦ hinj U.unop)
    fun U s hs ↦ hsurj U.unop s ((D.submodule_obj U) ▸ hs)

def sheafOverIsoOfRestrictEq (D E : CartierDivisor X) (V : X.Opens) (h : D |_ V = E |_ V) :
    D.sheaf.over V ≅ E.sheaf.over V :=
  D.submodule.overIsoOfEq E.submodule V fun W i ↦
    (D.submodule_obj (op W)).trans ((sections_congr h i.le).trans (E.submodule_obj (op W)).symm)

@[reassoc (attr := simp)]
lemma sheafOverIsoOfRestrictEq_hom_ι (D E : CartierDivisor X) (V : X.Opens)
    (h : D |_ V = E |_ V) :
    (sheafOverIsoOfRestrictEq D E V h).hom ≫ E.sheafι.over V = D.sheafι.over V :=
  SheafOfModules.Submodule.overIsoOfEq_hom_ι _ _ _ _

lemma rationalFunctionsMul_inv_toRationalFunctions_app_mem_sections (f : X.functionFieldˣ)
    (U : X.Opens) (a : Γ(X, U)) :
    Scheme.Modules.Hom.app (rationalFunctionsMul X ((f⁻¹ : X.functionFieldˣ) : X.functionField))
        U (Scheme.Modules.Hom.app (toRationalFunctions X) U a) ∈
      (principalCartierDivisor X f).sections U := by
  rcases isEmpty_or_nonempty U with hU | hU
  ·
    exact mem_sections.mpr fun x hx ↦ hU.elim ⟨x, hx⟩
  · refine (mem_sections_iff_of_rationalUnitClass_eq le_rfl
      (principalCartierDivisor_restrict X f U).symm).mpr ⟨a, ?_⟩
    rw [rationalFunctionsEquiv_rationalFunctionsMul_app,
      rationalFunctionsEquiv_toRationalFunctions_app, ← mul_assoc, Units.mul_inv, one_mul]

variable (X) in

def unitToSheafPrincipalCartierDivisor (f : X.functionFieldˣ) :
    @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf)
      (principalCartierDivisor X f).sheaf :=
  (principalCartierDivisor X f).sheafLift
    (toRationalFunctions X ≫ rationalFunctionsMul X ((f⁻¹ : X.functionFieldˣ) : X.functionField))
    fun U a ↦ rationalFunctionsMul_inv_toRationalFunctions_app_mem_sections f U a

@[simp, reassoc]
lemma unitToSheafPrincipalCartierDivisor_ι (f : X.functionFieldˣ) :
    unitToSheafPrincipalCartierDivisor X f ≫ (principalCartierDivisor X f).sheafι =
      toRationalFunctions X ≫
        rationalFunctionsMul X ((f⁻¹ : X.functionFieldˣ) : X.functionField) :=
  sheafLift_ι _ _ _

@[simp]
lemma unitToSheafPrincipalCartierDivisor_app (f : X.functionFieldˣ)
    (U : X.Opens) (a : Γ(SheafOfModules.unit X.ringCatSheaf, U)) :
    Scheme.Modules.Hom.app (principalCartierDivisor X f).sheafι U
        (Scheme.Modules.Hom.app (unitToSheafPrincipalCartierDivisor X f) U a) =
      Scheme.Modules.Hom.app (rationalFunctionsMul X
        ((f⁻¹ : X.functionFieldˣ) : X.functionField)) U
        (Scheme.Modules.Hom.app (toRationalFunctions X) U a) := by
  unfold unitToSheafPrincipalCartierDivisor
  simpa only [Scheme.Modules.Hom.comp_app (M := SheafOfModules.unit X.ringCatSheaf),
    ConcreteCategory.comp_apply] using
    sheafι_app_sheafLift (principalCartierDivisor X f)
      (toRationalFunctions X ≫ rationalFunctionsMul X
        ((f⁻¹ : X.functionFieldˣ) : X.functionField))
      (fun V b ↦ rationalFunctionsMul_inv_toRationalFunctions_app_mem_sections f V b) U a

instance isIso_unitToSheafPrincipalCartierDivisor (f : X.functionFieldˣ) :
    IsIso (unitToSheafPrincipalCartierDivisor X f) := by
  refine TauCeti.SheafOfModules.isIso_liftToSubmodule _ _ _ (fun U a b hab ↦ ?_)
    fun U t ht ↦ ?_
  ·
    refine toRationalFunctions_app_injective U.unop ?_
    rw [← rationalFunctionsMul_app_rationalFunctionsMul_inv_app f U.unop
        (Scheme.Modules.Hom.app (toRationalFunctions X) U.unop a),
      ← rationalFunctionsMul_app_rationalFunctionsMul_inv_app f U.unop
        (Scheme.Modules.Hom.app (toRationalFunctions X) U.unop b)]
    exact congrArg _ hab
  · induction U using Opposite.rec with | op U => ?_
    rw [submodule_obj] at ht
    rcases isEmpty_or_nonempty U with hU | hU
    · have hbot : U = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU)
      have := subsingleton_rationalFunctions U hbot
      exact ⟨0, @Subsingleton.elim _ this _ _⟩
    · obtain ⟨a, ha⟩ := (mem_sections_iff_of_rationalUnitClass_eq le_rfl
        (principalCartierDivisor_restrict X f U).symm).mp ht
      refine ⟨a, (rationalFunctionsEquiv U).injective ?_⟩
      change rationalFunctionsEquiv U (Scheme.Modules.Hom.app (rationalFunctionsMul X
        ((f⁻¹ : X.functionFieldˣ) : X.functionField)) U
        (Scheme.Modules.Hom.app (toRationalFunctions X) U a)) = _
      rw [rationalFunctionsEquiv_rationalFunctionsMul_app,
        rationalFunctionsEquiv_toRationalFunctions_app, ha, ← mul_assoc, Units.inv_mul,
        one_mul]

variable (X) in

def unitIsoSheafPrincipalCartierDivisor (f : X.functionFieldˣ) :
    @Iso X.Modules _ (SheafOfModules.unit X.ringCatSheaf) (principalCartierDivisor X f).sheaf :=
  asIso (unitToSheafPrincipalCartierDivisor X f)

@[simp]
lemma unitIsoSheafPrincipalCartierDivisor_hom (f : X.functionFieldˣ) :
    (unitIsoSheafPrincipalCartierDivisor X f).hom = unitToSheafPrincipalCartierDivisor X f :=
  (rfl)

def localTrivializations (D : CartierDivisor X) :
    TauCeti.SheafOfModules.LocalTrivializations.{u, u, u} D.sheaf := by
  choose f hf using D.exists_isLocalEquationAt
  choose V hx hV using fun x ↦ isLocalEquationAt_iff.mp (hf x)
  exact SheafOfModules.LocalTrivializations.ofForallMem X V hx fun x ↦
    haveI : Nonempty (V x) := ⟨⟨x, hx x⟩⟩
    (SheafOfModules.overFunctor X.ringCatSheaf (V x)).mapIso
      (unitIsoSheafPrincipalCartierDivisor X (f x)) ≪≫
      sheafOverIsoOfRestrictEq _ D (V x)
        ((principalCartierDivisor_restrict X (f x) (V x)).trans (hV x))

theorem isInvertible_sheaf (D : CartierDivisor X) : SheafOfModules.isInvertible X D.sheaf :=
  D.localTrivializations.isInvertible

def toInvertibleSheaf (D : CartierDivisor X) : InvertibleSheaf X :=
  ⟨D.sheaf, D.isInvertible_sheaf⟩

@[simp]
lemma toInvertibleSheaf_obj (D : CartierDivisor X) : D.toInvertibleSheaf.obj = D.sheaf :=
  (rfl)

end CartierDivisor

end Scheme

end

end AlgebraicGeometry

end TauCeti
