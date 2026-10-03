module

public import BondalThomsen.Cohomology.FiniteAffineCechHigherComparison

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open BondalThomsen.FiniteAffineCechHigherComparison
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace BondalThomsen.FiniteAffineCechDerivedIso

universe u

noncomputable section

variable {scheme : Scheme.{u}} {Index : Type u}

theorem cechIntersection_zero (opens : Index → scheme.Opens) (tuple : Fin 1 → Index) :
    cechIntersection opens 0 tuple = opens (tuple 0) := by
  rw [cechIntersection, productOpens_eq_iInf]
  exact iInf_unique (fun index : Fin 1 => opens (tuple index))

theorem cechIntersection_one (opens : Index → scheme.Opens) (tuple : Fin 2 → Index) :
    cechIntersection opens 1 tuple = opens (tuple 0) ⊓ opens (tuple 1) := by
  rw [cechIntersection, productOpens_eq_iInf]
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · apply le_iInf
    intro index
    fin_cases index
    · exact inf_le_left
    · exact inf_le_right

def cechAugmentation (opens : Index → scheme.Opens) (coefficient : scheme.Modules) :
    coefficient.presheaf.obj (op (iSup opens)) ⟶ (schemeCechComplex opens coefficient).X 0 :=
  Limits.Pi.lift (fun tuple : Fin 1 → Index =>
    coefficient.presheaf.map (homOfLE (show cechIntersection opens 0 tuple ≤ iSup opens from
      (by rw [cechIntersection_zero]; exact le_iSup opens (tuple 0)))).op)

theorem cechAugmentation_component (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (tuple : Fin 1 → Index) :
    cechAugmentation opens coefficient ≫
        Limits.Pi.π (fun tuple : Fin 1 → Index =>
          coefficient.presheaf.obj (op (cechIntersection opens 0 tuple))) tuple =
      coefficient.presheaf.map (homOfLE (show cechIntersection opens 0 tuple ≤ iSup opens from
        (by rw [cechIntersection_zero]; exact le_iSup opens (tuple 0)))).op :=
  Limits.Pi.lift_comp_π _ tuple

theorem cechAugmentation_d (opens : Index → scheme.Opens) (coefficient : scheme.Modules) :
    cechAugmentation opens coefficient ≫ (schemeCechComplex opens coefficient).d 0 1 = 0 := by
  apply Limits.Pi.hom_ext _ _
  intro tuple
  change (cechAugmentation opens coefficient ≫
    (schemeCechComplex opens coefficient).d 0 1) ≫
      Limits.Pi.π (fun tuple : Fin 2 → Index =>
        coefficient.presheaf.obj (op (cechIntersection opens 1 tuple))) tuple = 0 ≫ _
  rw [Category.assoc, schemeCechComplex_d_zero_component]
  simp only [Preadditive.comp_sub, ← Category.assoc, cechAugmentation_component,
    ← coefficient.presheaf.map_comp, ← op_comp]
  rw [zero_comp]
  apply sub_eq_zero.mpr
  congr 1

def cechZeroCoordinate (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    (cochain : (schemeCechComplex opens coefficient).X 0) (index : Index) :
    coefficient.presheaf.obj (op (opens index)) :=
  coefficient.presheaf.map (eqToHom
    (cechIntersection_zero opens (fun _ => index)).symm).op
      (Limits.Pi.π (fun tuple : Fin 1 → Index =>
        coefficient.presheaf.obj (op (cechIntersection opens 0 tuple))) (fun _ => index) cochain)

theorem cechZeroCoordinate_augmentation (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (section_value : coefficient.presheaf.obj (op (iSup opens)))
    (index : Index) :
    cechZeroCoordinate opens coefficient (cechAugmentation opens coefficient section_value) index =
      coefficient.presheaf.map (Opens.leSupr opens index).op section_value := by
  dsimp only [cechZeroCoordinate]
  have component := ConcreteCategory.congr_hom
    (cechAugmentation_component opens coefficient (fun _ => index)) section_value
  change Limits.Pi.π (fun tuple : Fin 1 → Index =>
      coefficient.presheaf.obj (op (cechIntersection opens 0 tuple))) (fun _ => index)
      (cechAugmentation opens coefficient section_value) = _ at component
  rw [component, ← ConcreteCategory.comp_apply, ← coefficient.presheaf.map_comp]
  rfl

theorem cechZeroCoordinate_ext (opens : Index → scheme.Opens) (coefficient : scheme.Modules)
    {first second : (schemeCechComplex opens coefficient).X 0}
    (same_coordinates : ∀ index,
      cechZeroCoordinate opens coefficient first index =
        cechZeroCoordinate opens coefficient second index) : first = second := by
  apply (productElementsEquiv (fun tuple : Fin 1 → Index =>
    coefficient.presheaf.obj (op (cechIntersection opens 0 tuple)))).injective
  funext tuple
  have tuple_constant : tuple = fun _ => tuple 0 := by funext index; fin_cases index; rfl
  rw [tuple_constant]
  rw [productElementsEquiv_apply, productElementsEquiv_apply]
  apply (ConcreteCategory.bijective_of_isIso
    (coefficient.presheaf.map (eqToHom
      (cechIntersection_zero opens (fun _ => tuple 0)).symm).op)).injective
  exact same_coordinates (tuple 0)

theorem cechAugmentation_injective (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) : Function.Injective (cechAugmentation opens coefficient) := by
  intro first second equality
  apply TopCat.Sheaf.eq_of_locally_eq (⟨coefficient.presheaf, coefficient.isSheaf⟩ :
    TopCat.Sheaf AddCommGrpCat.{u} scheme) opens first second
  intro index
  simpa only [cechZeroCoordinate_augmentation] using
    congrArg (fun cochain => cechZeroCoordinate opens coefficient cochain index) equality

theorem cechZeroCoordinate_restriction (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (cochain : (schemeCechComplex opens coefficient).X 0)
    (tuple : Fin 1 → Index) (smaller : scheme.Opens)
    (to_intersection : smaller ⟶ cechIntersection opens 0 tuple)
    (to_open : smaller ⟶ opens (tuple 0)) :
    coefficient.presheaf.map to_intersection.op
        (Limits.Pi.π (fun tuple : Fin 1 → Index =>
          coefficient.presheaf.obj (op (cechIntersection opens 0 tuple))) tuple cochain) =
      coefficient.presheaf.map to_open.op
        (cechZeroCoordinate opens coefficient cochain (tuple 0)) := by
  obtain ⟨index, tuple_eq⟩ : ∃ index, tuple = fun _ => index := by
    refine ⟨tuple 0, ?_⟩
    funext entry
    fin_cases entry
    rfl
  subst tuple
  dsimp only [cechZeroCoordinate]
  have same_map : coefficient.presheaf.map to_intersection.op =
      coefficient.presheaf.map (eqToHom
        (cechIntersection_zero opens (fun _ => index)).symm).op ≫
          coefficient.presheaf.map to_open.op := by
    rw [← coefficient.presheaf.map_comp]
    rfl
  rw [same_map]
  rfl

theorem cechZeroCoordinate_compatible (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) (cochain : (schemeCechComplex opens coefficient).X 0)
    (cycle : (schemeCechComplex opens coefficient).d 0 1 cochain = 0) :
    TopCat.Presheaf.IsCompatible coefficient.presheaf opens
      (cechZeroCoordinate opens coefficient cochain) := by
  intro first second
  let tuple : Fin 2 → Index := ![first, second]
  have difference := ConcreteCategory.congr_hom
    (schemeCechComplex_d_zero_component opens coefficient tuple) cochain
  have local_zero := congrArg (fun value =>
    Limits.Pi.π (fun tuple : Fin 2 → Index =>
      coefficient.presheaf.obj (op (cechIntersection opens 1 tuple))) tuple value) cycle
  rw [map_zero] at local_zero
  change Limits.Pi.π (fun tuple : Fin 2 → Index =>
      coefficient.presheaf.obj (op (cechIntersection opens 1 tuple))) tuple
        ((schemeCechComplex opens coefficient).d 0 1 cochain) = 0
    at local_zero
  change Limits.Pi.π (fun tuple : Fin 2 → Index =>
      coefficient.presheaf.obj (op (cechIntersection opens 1 tuple))) tuple
        ((schemeCechComplex opens coefficient).d 0 1 cochain) =
    coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin 1 =>
      Limits.Pi.π (opens ∘ tuple) ((0 : Fin 2).succAbove index))).op
        (Limits.Pi.π (fun tuple : Fin 1 → Index =>
          coefficient.presheaf.obj (op (cechIntersection opens 0 tuple)))
            (tuple ∘ (0 : Fin 2).succAbove) cochain) -
    coefficient.presheaf.map (Limits.Pi.lift (fun index : Fin 1 =>
      Limits.Pi.π (opens ∘ tuple) ((1 : Fin 2).succAbove index))).op
        (Limits.Pi.π (fun tuple : Fin 1 → Index =>
          coefficient.presheaf.obj (op (cechIntersection opens 0 tuple)))
            (tuple ∘ (1 : Fin 2).succAbove) cochain) at difference
  have restriction_zero := cechZeroCoordinate_restriction opens coefficient cochain
    (tuple ∘ (0 : Fin 2).succAbove) (cechIntersection opens 1 tuple)
    (Limits.Pi.lift (fun index : Fin 1 =>
      Limits.Pi.π (opens ∘ tuple) ((0 : Fin 2).succAbove index)))
    (homOfLE (by rw [cechIntersection_one]; exact inf_le_right))
  have restriction_one := cechZeroCoordinate_restriction opens coefficient cochain
    (tuple ∘ (1 : Fin 2).succAbove) (cechIntersection opens 1 tuple)
    (Limits.Pi.lift (fun index : Fin 1 =>
      Limits.Pi.π (opens ∘ tuple) ((1 : Fin 2).succAbove index)))
    (homOfLE (by rw [cechIntersection_one]; exact inf_le_left))
  have compatible := sub_eq_zero.mp (difference.symm.trans local_zero)
  have coordinate_compatible := restriction_zero.symm.trans (compatible.trans restriction_one)
  have face_zero : (tuple ∘ (0 : Fin 2).succAbove) 0 = second := rfl
  have face_one : (tuple ∘ (1 : Fin 2).succAbove) 0 = first := by
    rw [Function.comp_apply, Fin.succAbove_of_castSucc_lt _ _ (by decide)]
    rfl
  simp only at coordinate_compatible
  symm at coordinate_compatible
  change coefficient.presheaf.map (homOfLE (show cechIntersection opens 1 tuple ≤
      opens first from by rw [cechIntersection_one]; exact inf_le_left)).op
      (cechZeroCoordinate opens coefficient cochain first) =
    coefficient.presheaf.map (homOfLE (show cechIntersection opens 1 tuple ≤
      opens second from by rw [cechIntersection_one]; exact inf_le_right)).op
      (cechZeroCoordinate opens coefficient cochain second) at coordinate_compatible
  have transported' := congrArg (fun value => coefficient.presheaf.map
    (eqToHom (cechIntersection_one opens tuple).symm).op value) coordinate_compatible
  simp only [← ConcreteCategory.comp_apply, ← coefficient.presheaf.map_comp,
    ← op_comp] at transported'
  exact transported'

theorem cechAugmentation_exact (opens : Index → scheme.Opens) (coefficient : scheme.Modules) :
    (ShortComplex.mk (cechAugmentation opens coefficient)
      ((schemeCechComplex opens coefficient).d 0 1)
      (cechAugmentation_d opens coefficient)).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro cochain cycle
  obtain ⟨section_value, glued, unique⟩ := TopCat.Sheaf.existsUnique_gluing
    (⟨coefficient.presheaf, coefficient.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} scheme)
    opens (cechZeroCoordinate opens coefficient cochain)
    (cechZeroCoordinate_compatible opens coefficient cochain cycle)
  refine ⟨section_value, ?_⟩
  apply cechZeroCoordinate_ext opens coefficient
  intro index
  rw [cechZeroCoordinate_augmentation]
  exact glued index

def cechAugmentationCycles (opens : Index → scheme.Opens) (coefficient : scheme.Modules) :
    coefficient.presheaf.obj (op (iSup opens)) ⟶ (schemeCechComplex opens coefficient).cycles 0 :=
  (schemeCechComplex opens coefficient).liftCycles (cechAugmentation opens coefficient) 1 (by simp)
    (cechAugmentation_d opens coefficient)

instance cechAugmentationCycles_isIso (opens : Index → scheme.Opens)
    (coefficient : scheme.Modules) : IsIso (cechAugmentationCycles opens coefficient) := by
  apply (CochainComplex.isIso_liftCycles_iff _ _ (cechAugmentation_d opens coefficient)).mpr
  exact ⟨cechAugmentation_exact opens coefficient,
    (AddCommGrpCat.mono_iff_injective _).mpr (cechAugmentation_injective opens coefficient)⟩

def cechZeroSectionsIso (opens : Index → scheme.Opens) (coefficient : scheme.Modules) :
    coefficient.presheaf.obj (op (iSup opens)) ≅ (schemeCechComplex opens coefficient).homology 0 :=
  asIso (cechAugmentationCycles opens coefficient) ≪≫
    (schemeCechComplex opens coefficient).isoHomologyπ₀

theorem cechZeroSectionsIso_hom (opens : Index → scheme.Opens) (coefficient : scheme.Modules) :
    (cechZeroSectionsIso opens coefficient).hom =
      cechAugmentationCycles opens coefficient ≫ (schemeCechComplex opens coefficient).homologyπ 0 :=
  rfl

def cechZeroSchemeCohomologyEquiv (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (coefficient : scheme.Modules) :
    Cohomology coefficient 0 ≃+ (schemeCechComplex opens coefficient).homology 0 :=
  (cohomologyZeroEquiv coefficient).trans
    ((coefficient.presheaf.mapIso (eqToIso (congrArg op cover).symm)).addCommGroupIsoToAddEquiv.trans
      (cechZeroSectionsIso opens coefficient).addCommGroupIsoToAddEquiv)

theorem cechAugmentation_naturality (opens : Index → scheme.Opens)
    {first second : scheme.Modules} (coefficient_map : first ⟶ second) :
    coefficient_map.app (iSup opens) ≫ cechAugmentation opens second =
      cechAugmentation opens first ≫ ((schemeCechComplexFunctor opens).map coefficient_map).f 0 := by
  apply Limits.Pi.hom_ext _ _
  intro tuple
  change (coefficient_map.app (iSup opens) ≫ cechAugmentation opens second) ≫
      Limits.Pi.π (fun tuple : Fin 1 → Index =>
        second.presheaf.obj (op (cechIntersection opens 0 tuple))) tuple =
    (cechAugmentation opens first ≫ Limits.Pi.map
      (fun tuple : Fin 1 → Index => coefficient_map.app (cechIntersection opens 0 tuple))) ≫
        Limits.Pi.π (fun tuple : Fin 1 → Index =>
          second.presheaf.obj (op (cechIntersection opens 0 tuple))) tuple
  rw [Category.assoc, cechAugmentation_component, Category.assoc, Limits.Pi.map_π]
  change coefficient_map.app (iSup opens) ≫ second.presheaf.map
      (homOfLE (show cechIntersection opens 0 tuple ≤ iSup opens from
        by rw [cechIntersection_zero]; exact le_iSup opens (tuple 0))).op =
    cechAugmentation opens first ≫
      Limits.Pi.π (fun tuple : Fin 1 → Index =>
        first.presheaf.obj (op (cechIntersection opens 0 tuple))) tuple ≫
          coefficient_map.app (cechIntersection opens 0 tuple)
  rw [← Category.assoc, cechAugmentation_component]
  exact ((PresheafOfModules.toPresheaf.{u} scheme.ringCatSheaf.obj).map
    coefficient_map.val).naturality _ |>.symm

theorem cechZeroSectionsIso_naturality (opens : Index → scheme.Opens)
    {first second : scheme.Modules} (coefficient_map : first ⟶ second) :
    coefficient_map.app (iSup opens) ≫ (cechZeroSectionsIso opens second).hom =
      (cechZeroSectionsIso opens first).hom ≫
        HomologicalComplex.homologyMap ((schemeCechComplexFunctor opens).map coefficient_map) 0 := by
  rw [cechZeroSectionsIso_hom, cechZeroSectionsIso_hom]
  simp only [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (fun arrow => arrow ≫ (schemeCechComplex opens second).homologyπ 0)
  dsimp only [cechAugmentationCycles]
  rw [HomologicalComplex.comp_liftCycles, HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 1
  exact cechAugmentation_naturality opens coefficient_map

def cechZeroSchemeCohomologyIso (opens : Index → scheme.Opens) (cover : iSup opens = ⊤)
    (coefficient : scheme.Modules) :
    AddCommGrpCat.of (Cohomology coefficient 0) ≅
      (schemeCechComplex opens coefficient).homology 0 :=
  (cechZeroSchemeCohomologyEquiv opens cover coefficient).toAddCommGrpIso

end

end BondalThomsen.FiniteAffineCechDerivedIso
