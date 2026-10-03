module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.CartierDivisor.Sheaf
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.TensorProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TensorProduct TopologicalSpace

namespace TauCeti
namespace AlgebraicGeometry
namespace Scheme.CartierDivisor

universe u

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

theorem rationalFunctionsMulBilin_mem_sections {D E : CartierDivisor X} {U : X.Opens}
    {s t : Γ(Scheme.rationalFunctions X, U)}
    (hs : s ∈ D.sections U) (ht : t ∈ E.sections U) :
    Scheme.rationalFunctionsMulBilin X U s t ∈ (D + E).sections U := by
  refine mem_sections_iff_exists.mpr fun x hx ↦ ?_
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  obtain ⟨g, hg⟩ := E.exists_isLocalEquationAt x
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  refine ⟨f * g, hf.mul hg, ?_⟩
  have hfs := (mem_sections.mp hs) x hx f hf
  have hgt := (mem_sections.mp ht) x hx g hg
  rw [Scheme.rationalFunctionsEquiv_mulBilin]
  convert Subring.mul_mem (algebraMap (X.presheaf.stalk x) X.functionField).range hfs hgt using 1
  simp only [Units.val_mul]
  ac_rfl

variable (D E : CartierDivisor X) (U : X.Opens)

def sectionsMul (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) : Γ((D + E).sheaf, U) :=
  sectionMk _ (rationalFunctionsMulBilin_mem_sections (sheafι_app_mem D U s)
    (sheafι_app_mem E U t))

@[simp]
lemma sheafι_app_sectionsMul (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    Scheme.Modules.Hom.app (sheafι (D + E)) U (sectionsMul D E U s t) =
      Scheme.rationalFunctionsMulBilin X U
        (Scheme.Modules.Hom.app (sheafι D) U s)
        (Scheme.Modules.Hom.app (sheafι E) U t) :=
  sheafι_app_sectionMk _ _

variable {D E U}

@[simp]
lemma sectionsMul_add_left (s s' : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    sectionsMul D E U (s + s') t = sectionsMul D E U s t + sectionsMul D E U s' t :=
  sheafι_app_injective _ U (by simp)

@[simp]
lemma sectionsMul_add_right (s : Γ(D.sheaf, U)) (t t' : Γ(E.sheaf, U)) :
    sectionsMul D E U s (t + t') = sectionsMul D E U s t + sectionsMul D E U s t' :=
  sheafι_app_injective _ U (by simp)

@[simp]
lemma sectionsMul_smul_left (r : Γ(X, U)) (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    sectionsMul D E U (r • s) t = r • sectionsMul D E U s t :=
  sheafι_app_injective _ U (by simp)

@[simp]
lemma sectionsMul_smul_right (r : Γ(X, U)) (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    sectionsMul D E U s (r • t) = r • sectionsMul D E U s t :=
  sheafι_app_injective _ U (by simp)

@[simp]
lemma sectionsMul_map {V : X.Opens} (i : V ⟶ U) (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    sectionsMul D E V (D.sheaf.presheaf.map i.op s) (E.sheaf.presheaf.map i.op t) =
      (D + E).sheaf.presheaf.map i.op (sectionsMul D E U s t) := by
  refine sheafι_app_injective _ V ?_
  have h {F : CartierDivisor X} (s : Γ(F.sheaf, U)) :=
    NatTrans.naturality_apply (sheafι F).mapPresheaf i.op s
  simp only [Scheme.Modules.mapPresheaf_app] at h
  rw [h, sheafι_app_sectionsMul, sheafι_app_sectionsMul, h, h,
    Scheme.rationalFunctionsMulBilin_map]

variable (D E U)

def sectionsMulLift :
    TensorProduct Γ(X, U) Γ(D.sheaf, U) Γ(E.sheaf, U) →ₗ[Γ(X, U)] Γ((D + E).sheaf, U) :=
  TensorProduct.lift <| LinearMap.mk₂ Γ(X, U) (sectionsMul D E U)
    (fun s s' t ↦ sectionsMul_add_left s s' t)
    (fun r s t ↦ sectionsMul_smul_left r s t)
    (fun s t t' ↦ sectionsMul_add_right s t t')
    (fun r s t ↦ sectionsMul_smul_right r s t)

@[simp]
lemma sectionsMulLift_tmul (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    sectionsMulLift D E U (s ⊗ₜ t) = sectionsMul D E U s t :=
  (rfl)

def tensorPresheafHom :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj) D.sheaf.val
      E.sheaf.val ⟶ (D + E).sheaf.val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun s t ↦ sectionsMul D E U.unop s t)
    (fun s s' t ↦ sectionsMul_add_left s s' t)
    (fun r s t ↦ sectionsMul_smul_left r s t)
    (fun s t t' ↦ sectionsMul_add_right s t t')
    (fun r s t ↦ sectionsMul_smul_right r s t)
  naturality f := ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ sectionsMul_map f.unop s t

section LocalEquation

variable {E : CartierDivisor X} {V : X.Opens} [Nonempty V] {g : X.functionFieldˣ}
  (hg : Scheme.rationalUnitClass X V (Additive.ofMul g) = E |_ V)

include hg

lemma inv_localEquation_mem_sections :
    (Scheme.rationalFunctionsEquiv V).symm (g⁻¹ : X.functionField) ∈ E.sections V := by
  refine (mem_sections_iff_of_rationalUnitClass_eq le_rfl hg).mpr ⟨1, ?_⟩
  simp

lemma localEquation_mem_sections_neg :
    (Scheme.rationalFunctionsEquiv V).symm (g : X.functionField) ∈ (-E).sections V := by
  have hneg : Scheme.rationalUnitClass X V (Additive.ofMul g⁻¹) = (-E) |_ V := by
    rw [ofMul_inv, map_neg, hg]
    simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_neg]
  refine (mem_sections_iff_of_rationalUnitClass_eq le_rfl hneg).mpr ⟨1, ?_⟩
  simp

variable (D : CartierDivisor X)

lemma mul_localEquation_mem_sections (s : Γ((D + E).sheaf, V)) :
    Scheme.rationalFunctionsMulBilin X V
      (Scheme.Modules.Hom.app (sheafι (D + E)) V s)
      ((Scheme.rationalFunctionsEquiv V).symm (g : X.functionField)) ∈ D.sections V := by
  simpa only [add_assoc, add_neg_cancel, add_zero] using
    rationalFunctionsMulBilin_mem_sections (sheafι_app_mem (D + E) V s)
      (localEquation_mem_sections_neg hg)

theorem exists_sectionsMul_eq (s : Γ((D + E).sheaf, V)) :
    ∃ (a : Γ(D.sheaf, V)) (b : Γ(E.sheaf, V)), sectionsMul D E V a b = s := by
  refine ⟨sectionMk _ (mul_localEquation_mem_sections hg D s),
    sectionMk _ (inv_localEquation_mem_sections hg), ?_⟩
  refine sheafι_app_injective _ V ((Scheme.rationalFunctionsEquiv V).injective ?_)
  simp

def sectionsMulRetraction :
    Γ((D + E).sheaf, V) →ₗ[Γ(X, V)]
      TensorProduct Γ(X, V) Γ(D.sheaf, V) Γ(E.sheaf, V) where
  toFun s := sectionMk _ (mul_localEquation_mem_sections hg D s) ⊗ₜ
    sectionMk _ (inv_localEquation_mem_sections hg)
  map_add' s s' := by
    rw [← TensorProduct.add_tmul]
    congr 1
    exact sheafι_app_injective D V (by simp)
  map_smul' r s := by
    rw [RingHom.id_apply, TensorProduct.smul_tmul']
    congr 1
    exact sheafι_app_injective D V (by simp)

theorem sectionsMulRetraction_sectionsMul (a : Γ(D.sheaf, V)) (b : Γ(E.sheaf, V)) :
    sectionsMulRetraction hg D (sectionsMul D E V a b) = a ⊗ₜ b := by
  obtain ⟨r, hr⟩ : ∃ r : Γ(X, V), Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) V r =
      Scheme.rationalFunctionsMulBilin X V (Scheme.Modules.Hom.app (sheafι E) V b)
        ((Scheme.rationalFunctionsEquiv V).symm (g : X.functionField)) := by
    have hzero : Scheme.rationalUnitClass X V (Additive.ofMul (1 : X.functionFieldˣ)) =
        (0 : CartierDivisor X) |_ V := by
      simp only [ofMul_one, map_zero, TopCat.Presheaf.restrictOpen,
        TopCat.Presheaf.restrict]
    have hmem : Scheme.rationalFunctionsMulBilin X V
        (Scheme.Modules.Hom.app (sheafι E) V b)
        ((Scheme.rationalFunctionsEquiv V).symm (g : X.functionField)) ∈
        (0 : CartierDivisor X).sections V := by
      simpa only [add_neg_cancel] using
        rationalFunctionsMulBilin_mem_sections (sheafι_app_mem E V b)
          (localEquation_mem_sections_neg hg)
    obtain ⟨r, hr⟩ :=
      (mem_sections_iff_of_rationalUnitClass_eq le_rfl hzero).mp hmem
    simp only [Units.val_one, one_mul] at hr
    exact ⟨r, (Scheme.rationalFunctionsEquiv V).injective
      (by rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app]; exact hr)⟩
  have h1 : sectionMk _ (mul_localEquation_mem_sections hg D (sectionsMul D E V a b)) =
      r • a := by
    refine sheafι_app_injective D V ?_
    rw [sheafι_app_sectionMk, Scheme.Modules.Hom.app_smul,
      ← Scheme.rationalFunctionsMulBilin_toRationalFunctions_app, hr, sheafι_app_sectionsMul]
    refine (Scheme.rationalFunctionsEquiv V).injective ?_
    simp
    ring
  have h2 : r • sectionMk _ (inv_localEquation_mem_sections hg) = b := by
    refine sheafι_app_injective E V ?_
    rw [Scheme.Modules.Hom.app_smul,
      ← Scheme.rationalFunctionsMulBilin_toRationalFunctions_app, hr, sheafι_app_sectionMk]
    exact (Scheme.rationalFunctionsEquiv V).injective (by simp)
  change sectionMk _ (mul_localEquation_mem_sections hg D (sectionsMul D E V a b)) ⊗ₜ
    sectionMk _ (inv_localEquation_mem_sections hg) = a ⊗ₜ b
  rw [h1, TensorProduct.smul_tmul, h2]

theorem sectionsMulLift_injective : Function.Injective (sectionsMulLift D E V) := by
  have key : Function.LeftInverse (sectionsMulRetraction hg D) (sectionsMulLift D E V) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
      rw [sectionsMulLift_tmul]
      exact sectionsMulRetraction_sectionsMul hg D a b
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  exact key.injective

end LocalEquation

section TensorProduct

variable (D E : CartierDivisor X)

theorem isLocallySurjective_tensorPresheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (tensorPresheafHom D E)) where
  imageSieve_mem {U} s x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_localEquation_le E U hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    obtain ⟨a, b, hab⟩ := exists_sectionsMul_eq hg D
      ((D + E).sheaf.presheaf.map (homOfLE hVU).op s)
    exact ⟨V, homOfLE hVU, ⟨a ⊗ₜ b, hab⟩, hxV⟩

theorem isLocallyInjective_tensorPresheafHom :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (tensorPresheafHom D E)) where
  equalizerSieve_mem {U} z z' h x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_localEquation_le E U.unop hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    refine ⟨V, homOfLE hVU, sectionsMulLift_injective hg D ?_, hxV⟩
    exact (PresheafOfModules.naturality_apply (tensorPresheafHom D E) (homOfLE hVU).op z).trans
      ((congrArg ((D + E).sheaf.val.map (homOfLE hVU).op) h).trans
        (PresheafOfModules.naturality_apply (tensorPresheafHom D E) (homOfLE hVU).op z').symm)

theorem isIso_sheafification_map_tensorPresheafHom :
    IsIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map (tensorPresheafHom D E)) := by
  have := isLocallySurjective_tensorPresheafHom D E
  have := isLocallyInjective_tensorPresheafHom D E
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (tensorPresheafHom D E)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact (Opens.grothendieckTopology X).W_of_isLocallyBijective _

def tensorProductSheafIso :
    TauCeti.SheafOfModules.tensorProduct X.sheaf D.sheaf E.sheaf ≅ (D + E).sheaf :=
  TauCeti.SheafOfModules.tensorProductIso X.sheaf D.sheaf E.sheaf ≪≫
    @asIso _ _ _ _ _ (isIso_sheafification_map_tensorPresheafHom D E) ≪≫
    TauCeti.SheafOfModules.sheafificationIso X.ringCatSheaf (D + E).sheaf

end TensorProduct

end
end CartierDivisor
end Scheme
end AlgebraicGeometry
end TauCeti
