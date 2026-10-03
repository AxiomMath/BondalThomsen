module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Germ
public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.Modules.RationalFunctions

@[expose] public section

open CategoryTheory Opposite Set TopologicalSpace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IrreducibleSpace X]

def rationalFunction (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] :
    Γ(M, V) →+ X.functionField := by
  let W : X.Opens := V ⊓ U
  let _ : Nonempty W := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  let A : Over U := Over.mk (homOfLE (show W ≤ U from inf_le_right))
  exact (X.germToFunctionField W).hom.toAddMonoidHom.comp
    (((trivializationCoordinateIso M e).hom.val.app (op A)).hom.toAddMonoidHom.comp
      (M.presheaf.map (homOfLE inf_le_left).op).hom)

lemma rationalFunction_apply (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] [Nonempty (V ⊓ U : X.Opens)]
    (s : Γ(M, V)) :
    rationalFunction M e hU V s = X.germToFunctionField (V ⊓ U)
      (trivializationCoordinate M e (homOfLE (inf_le_right : V ⊓ U ≤ U))
        (M.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s)) := by
  rw [trivializationCoordinate_apply]
  rfl

@[simp]
theorem rationalFunction_smul (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] (r : Γ(X, V)) (s : Γ(M, V)) :
    rationalFunction M e hU V (r • s) =
      X.germToFunctionField V r * rationalFunction M e hU V s := by
  have : Nonempty (V ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  let i : V ⊓ U ⟶ V := homOfLE inf_le_left
  rw [rationalFunction_apply, rationalFunction_apply, M.map_smul, LinearEquiv.map_smul,
    smul_eq_mul, map_mul, X.presheaf.germ_res_apply i (genericPoint X)]

@[simp]
theorem rationalFunction_map (M : X.Modules) {U V T : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (i : V ⟶ T) [Nonempty V] [Nonempty T] (s : Γ(M, T)) :
    rationalFunction M e hU V (M.presheaf.map i.op s) = rationalFunction M e hU T s := by
  have : Nonempty (T ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty T T.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  have : Nonempty (V ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  let j : V ⊓ U ⟶ T ⊓ U := homOfLE (inf_le_inf i.le le_rfl)
  have hM : M.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op (M.presheaf.map i.op s) =
      M.presheaf.map j.op (M.presheaf.map (homOfLE (inf_le_left : T ⊓ U ≤ T)).op s) := by
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  have hj : (homOfLE (inf_le_right : V ⊓ U ≤ U)) = j ≫ homOfLE inf_le_right :=
    Subsingleton.elim _ _
  rw [rationalFunction_apply, rationalFunction_apply, hM, hj, trivializationCoordinate_map]
  exact X.presheaf.germ_res_apply j (genericPoint X) (Scheme.genericPoint_mem _) _

def rationalApp (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] :
    M.val.obj (op V) ⟶ (Scheme.rationalFunctions X).val.obj (op V) :=
  ModuleCat.ofHom (R := Γ(X, V))
    (X := Γ(M, V)) (Y := Γ(Scheme.rationalFunctions X, V))
    { toFun := fun s ↦ (Scheme.rationalFunctionsEquiv V).symm (rationalFunction M e hU V s)
      map_add' := fun s t ↦ by
        calc
          _ = (Scheme.rationalFunctionsEquiv V).symm
              (rationalFunction M e hU V s + rationalFunction M e hU V t) :=
            congrArg _ (map_add (rationalFunction M e hU V) s t)
          _ = _ := map_add _ _ _
      map_smul' := fun r s ↦ by
        have hs := rationalFunction_smul M e hU V (id r : Γ(X, V)) (id s : Γ(M, V))
        calc
          _ = (Scheme.rationalFunctionsEquiv V).symm
              (X.germToFunctionField V (id r : Γ(X, V)) * rationalFunction M e hU V s) :=
            congrArg _ hs
          _ = (Scheme.rationalFunctionsEquiv V).symm
              ((id r : Γ(X, V)) • rationalFunction M e hU V s) := by
            rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
          _ = _ := _root_.map_smul _ _ _ }

lemma rationalApp_naturality (M : X.Modules) {U V T : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (i : V ⟶ T) [Nonempty V] [Nonempty T]
    (s : Γ(M, T)) :
    rationalApp M e hU V (M.presheaf.map i.op s) =
      (Scheme.rationalFunctions X).presheaf.map i.op (rationalApp M e hU T s) := by
  apply (Scheme.rationalFunctionsEquiv V).injective
  calc
    _ = rationalFunction M e hU V (M.presheaf.map i.op s) :=
      (Scheme.rationalFunctionsEquiv V).apply_symm_apply _
    _ = rationalFunction M e hU T s := rationalFunction_map M e hU i s
    _ = Scheme.rationalFunctionsEquiv T (rationalApp M e hU T s) :=
      ((Scheme.rationalFunctionsEquiv T).apply_symm_apply _).symm
    _ = _ := (Scheme.rationalFunctionsEquiv_map i (rationalApp M e hU T s)).symm

def rationalTrivializationHom (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) : M ⟶ Scheme.rationalFunctions X := by
  classical
  exact
    { val :=
      { app := fun V ↦ if hV : Nonempty V.unop then
          letI := hV
          rationalApp M e hU V.unop
        else 0
        naturality := fun {V T} i ↦ by
          by_cases hT : Nonempty T.unop
          · let _ : Nonempty T.unop := hT
            let x : T.unop := Classical.choice hT
            have hV : Nonempty V.unop := ⟨⟨x.1, i.unop.le x.2⟩⟩
            let _ : Nonempty V.unop := hV
            simp only [dite_eq_left hT, dite_eq_left hV]
            ext s
            exact rationalApp_naturality M e hU i.unop s
          · have hbot : T.unop = ⊥ := (Opens.not_nonempty_iff_eq_bot T.unop).mp
              (fun ⟨x, hx⟩ ↦ hT ⟨⟨x, hx⟩⟩)
            let _ : Subsingleton
                ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
                  ((Scheme.rationalFunctions X).val.obj T)) :=
              ⟨fun a b ↦ (Scheme.subsingleton_rationalFunctions T.unop hbot).elim a b⟩
            ext s
            exact Subsingleton.elim _ _ } }

@[simp]
theorem rationalFunctionsEquiv_rationalTrivializationHom_app (M : X.Modules)
    {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] (s : Γ(M, V)) :
    Scheme.rationalFunctionsEquiv V
        (Scheme.Modules.Hom.app (rationalTrivializationHom M e hU) V s) =
      rationalFunction M e hU V s := by
  simp only [rationalTrivializationHom, Scheme.Modules.Hom.app, dite_eq_left
    (inferInstance : Nonempty V)]
  exact (Scheme.rationalFunctionsEquiv V).apply_symm_apply _

theorem rationalFunction_injective [IsIntegral X] (M : X.Modules)
    [SheafOfModules.isInvertible X M] {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] :
    Function.Injective (rationalFunction M e hU V) := by
  have : Nonempty (V ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  intro s t h
  rw [rationalFunction_apply, rationalFunction_apply] at h
  exact InvertibleSheaf.map_injective_of_isIntegral ⟨M, ‹_›⟩ (homOfLE inf_le_left)
    ((trivializationCoordinate M e _).injective (X.germToFunctionField_injective (V ⊓ U) h))

theorem rationalTrivializationHom_app_injective [IsIntegral X] (M : X.Modules)
    [SheafOfModules.isInvertible X M] {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app (rationalTrivializationHom M e hU) V) := by
  intro s t h
  by_cases hV : Nonempty V
  · apply rationalFunction_injective M e hU V
    rw [← rationalFunctionsEquiv_rationalTrivializationHom_app,
      ← rationalFunctionsEquiv_rationalTrivializationHom_app, h]
  · exact TopCat.Presheaf.section_ext ⟨M.presheaf, M.isSheaf⟩ V s t
      fun x hx ↦ (hV ⟨⟨x, hx⟩⟩).elim

instance mono_rationalTrivializationHom [IsIntegral X] (M : X.Modules)
    [SheafOfModules.isInvertible X M] {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) : Mono (rationalTrivializationHom M e hU) :=
  (SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective fun V ↦
      rationalTrivializationHom_app_injective M e hU V.unop)

theorem range_rationalFunction (M : X.Modules) {U V W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V)
    [Nonempty W] :
    Set.range (rationalFunction M e hU W) =
      {q | ∃ r : Γ(X, W), q = X.germToFunctionField W r *
        rationalFunction M e hU W (M.presheaf.map i.op (trivializationGenerator M t))} := by
  ext q
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨r, rfl, -⟩ := existsUnique_eq_smul_map_trivializationGenerator M t i s
    exact ⟨r, rationalFunction_smul M e hU W r _⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r • M.presheaf.map i.op (trivializationGenerator M t),
      rationalFunction_smul M e hU W r _⟩

theorem isUnit_rationalFunction_trivializationGenerator (M : X.Modules) {U V : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    [Nonempty V] :
    IsUnit (rationalFunction M e hU V (trivializationGenerator M t)) := by
  have : Nonempty (V ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  obtain ⟨u, hu, -⟩ := existsUnique_map_trivializationGenerator_eq_smul M t e
    (homOfLE inf_le_left) (homOfLE inf_le_right)
  rw [rationalFunction_apply, hu, LinearEquiv.map_smul,
    trivializationCoordinate_map_trivializationGenerator, smul_eq_mul, mul_one]
  exact u.isUnit.map _

def trivializationGeneratorRationalUnit (M : X.Modules) {U V : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    [Nonempty V] : X.functionFieldˣ :=
  (isUnit_rationalFunction_trivializationGenerator M e hU t).unit

@[simp]
theorem coe_trivializationGeneratorRationalUnit (M : X.Modules) {U V : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    [Nonempty V] :
    (trivializationGeneratorRationalUnit M e hU t : X.functionField) =
      rationalFunction M e hU V (trivializationGenerator M t) :=
  IsUnit.unit_spec _

theorem exists_rationalFunction_eq_mul (M : X.Modules) {U V W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) [Nonempty V] [Nonempty W]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V)
    (s : Γ(M, W)) :
    ∃ r : Γ(X, W), rationalFunction M e hU W s =
      X.germToFunctionField W r * (trivializationGeneratorRationalUnit M e hU t : _) := by
  have hs : rationalFunction M e hU W s ∈ Set.range (rationalFunction M e hU W) := ⟨s, rfl⟩
  rw [range_rationalFunction M e hU t i] at hs
  obtain ⟨r, hr⟩ := hs
  exact ⟨r, by rw [hr, rationalFunction_map, coe_trivializationGeneratorRationalUnit]⟩

theorem exists_rationalFunction_trivializationGenerator_eq_mul (M : X.Modules)
    {U V₁ V₂ W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t₁ : SheafOfModules.free (R := X.ringCatSheaf.over V₁) PUnit ≅ M.over V₁)
    (t₂ : SheafOfModules.free (R := X.ringCatSheaf.over V₂) PUnit ≅ M.over V₂)
    (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂) [Nonempty W] :
    ∃ r : Γ(X, W)ˣ,
      rationalFunction M e hU W (M.presheaf.map i₁.op (trivializationGenerator M t₁)) =
        X.germToFunctionField W (r : Γ(X, W)) *
          rationalFunction M e hU W (M.presheaf.map i₂.op (trivializationGenerator M t₂)) := by
  obtain ⟨r, hr, -⟩ := existsUnique_map_trivializationGenerator_eq_smul M t₁ t₂ i₁ i₂
  exact ⟨r, by rw [hr, rationalFunction_smul]⟩

end AlgebraicGeometry.Scheme.Modules

end
