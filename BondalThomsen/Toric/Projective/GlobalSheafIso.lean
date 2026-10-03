module

public import BondalThomsen.Toric.Projective.PullbackSheafIso

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable section

theorem modulePullbackSectionHom_transpose {source target : Scheme}
    (map : source ⟶ target) {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf) :
    section_map ≫ (Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf =
      SheafOfModules.unitToPushforwardObjUnit map.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward map).map (modulePullbackSectionHom map section_map) := by
  have transpose := (Scheme.Modules.pullbackPushforwardAdjunction map).homEquiv_naturality_right
    (Scheme.Modules.pullbackObjUnitIso map).hom (modulePullbackSectionHom map section_map)
  rw [Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom] at transpose
  have cancellation : (Scheme.Modules.pullbackObjUnitIso map).hom ≫
      modulePullbackSectionHom map section_map = (Scheme.Modules.pullback map).map section_map := by
    simp only [modulePullbackSectionHom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [cancellation, Adjunction.homEquiv_unit] at transpose
  exact ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.naturality section_map).trans transpose

theorem modulePullbackSectionHom_app_one {source target : Scheme}
    (map : source ⟶ target) {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf)
    (open_set : target.Opens) :
    Scheme.Modules.Hom.app (modulePullbackSectionHom map section_map) (map ⁻¹ᵁ open_set)
        (1 : Γ(source, map ⁻¹ᵁ open_set)) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf)
        open_set (Scheme.Modules.Hom.app section_map open_set (1 : Γ(target, open_set))) := by
  have transpose := congrArg (fun morphism : SheafOfModules.unit target.ringCatSheaf ⟶
      (Scheme.Modules.pushforward map).obj ((Scheme.Modules.pullback map).obj sheaf) =>
    Scheme.Modules.Hom.app morphism open_set
    (1 : Γ(target, open_set))) (modulePullbackSectionHom_transpose map section_map)
  change Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf)
      open_set (Scheme.Modules.Hom.app section_map open_set (1 : Γ(target, open_set))) =
    Scheme.Modules.Hom.app (modulePullbackSectionHom map section_map) (map ⁻¹ᵁ open_set)
      (map.app open_set (1 : Γ(target, open_set))) at transpose
  have mapped_one : map.app open_set (1 : Γ(target, open_set)) = 1 := map_one _
  rw [mapped_one] at transpose
  exact transpose.symm

theorem modulePullbackSectionHom_appLE_one {source target : Scheme}
    (map : source ⟶ target) {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf)
    (target_open : target.Opens) (source_open : source.Opens)
    (contained : source_open ≤ map ⁻¹ᵁ target_open) :
    Scheme.Modules.Hom.app (modulePullbackSectionHom map section_map) source_open
        (1 : Γ(source, source_open)) =
      ((Scheme.Modules.pullback map).obj sheaf).presheaf.map (homOfLE contained).op
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf)
          target_open (Scheme.Modules.Hom.app section_map target_open (1 : Γ(target, target_open)))) := by
  have naturality := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf source).map (modulePullbackSectionHom map section_map)).naturality
      (homOfLE contained).op) (1 : Γ(source, map ⁻¹ᵁ target_open))
  change Scheme.Modules.Hom.app (modulePullbackSectionHom map section_map) source_open
      (source.presheaf.map (homOfLE contained).op 1) =
    ((Scheme.Modules.pullback map).obj sheaf).presheaf.map (homOfLE contained).op
      (Scheme.Modules.Hom.app (modulePullbackSectionHom map section_map) (map ⁻¹ᵁ target_open)
        (1 : Γ(source, map ⁻¹ᵁ target_open))) at naturality
  have mapped_one : source.presheaf.map (homOfLE contained).op
      (1 : Γ(source, map ⁻¹ᵁ target_open)) = 1 := map_one _
  rw [mapped_one, modulePullbackSectionHom_app_one] at naturality
  exact naturality

theorem modulePullbackSectionHom_coefficient {source target : Scheme}
    (map : source ⟶ target) {sheaf : target.Modules}
    (first second : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf)
    (target_open : target.Opens) (source_open : source.Opens)
    (contained : source_open ≤ map ⁻¹ᵁ target_open) (scalar : Γ(target, target_open))
    (relation : Scheme.Modules.Hom.app second target_open (1 : Γ(target, target_open)) =
      scalar • Scheme.Modules.Hom.app first target_open (1 : Γ(target, target_open))) :
    Scheme.Modules.Hom.app (modulePullbackSectionHom map second) source_open
        (1 : Γ(source, source_open)) =
      map.appLE target_open source_open contained scalar •
        Scheme.Modules.Hom.app (modulePullbackSectionHom map first) source_open
          (1 : Γ(source, source_open)) := by
  rw [modulePullbackSectionHom_appLE_one map second target_open source_open contained, relation,
    modulePullbackSectionHom_appLE_one map first target_open source_open contained]
  rw [Scheme.Modules.Hom.app_smul]
  let section_value : Γ((Scheme.Modules.pullback map).obj sheaf, map ⁻¹ᵁ target_open) :=
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction map).unit.app sheaf)
      target_open (Scheme.Modules.Hom.app first target_open (1 : Γ(target, target_open)))
  change ((Scheme.Modules.pullback map).obj sheaf).presheaf.map (homOfLE contained).op
      (map.app target_open scalar • section_value) = _
  rw [Scheme.Modules.map_smul]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomialProjDegreeOneCoordinateHom_coefficient (Index : Type)
    (chart coordinate : Index) :
    Scheme.Modules.Hom.app (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)
        (polynomialDegreeOneCoordinateOpen 𝕜 Index chart)
          (1 : Γ(polynomialDegreeOneProj 𝕜 Index, polynomialDegreeOneCoordinateOpen 𝕜 Index chart)) =
      polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl •
        Scheme.Modules.Hom.app (polynomialProjDegreeOneCoordinateHom 𝕜 Index chart)
          (polynomialDegreeOneCoordinateOpen 𝕜 Index chart)
            (1 : Γ(polynomialDegreeOneProj 𝕜 Index, polynomialDegreeOneCoordinateOpen 𝕜 Index chart)) := by
  simp only [polynomialProjDegreeOneCoordinateHom, moduleGlobalSectionHom_app, one_smul]
  rw [polynomialProjDegreeOneGlobalCoordinate_restrict,
    polynomialProjDegreeOneGlobalCoordinate_restrict]
  rw [← polynomialDegreeOneChartRatio_frame 𝕜 Index chart coordinate le_rfl]
  change (polynomialDegreeOneChartSectionsLinearEquiv 𝕜 Index chart le_rfl)
      (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl) =
    polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl •
      (polynomialDegreeOneChartSectionsLinearEquiv 𝕜 Index chart le_rfl) 1
  simpa only [smul_eq_mul, mul_one] using
    (polynomialDegreeOneChartSectionsLinearEquiv 𝕜 Index chart le_rfl).map_smul
      (polynomialDegreeOneChartRatio 𝕜 Index chart coordinate le_rfl) 1

theorem moduleSectionHom_coefficient_restrict {scheme : Scheme} {sheaf : scheme.Modules}
    (first second : SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf)
    (larger smaller : scheme.Opens) (contained : smaller ≤ larger) (scalar : Γ(scheme, larger))
    (relation : Scheme.Modules.Hom.app second larger (1 : Γ(scheme, larger)) =
      scalar • Scheme.Modules.Hom.app first larger (1 : Γ(scheme, larger))) :
    Scheme.Modules.Hom.app second smaller (1 : Γ(scheme, smaller)) =
      scheme.presheaf.map (homOfLE contained).op scalar •
        Scheme.Modules.Hom.app first smaller (1 : Γ(scheme, smaller)) := by
  have first_natural := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf scheme).map first).naturality (homOfLE contained).op)
      (1 : Γ(scheme, larger))
  have second_natural := ConcreteCategory.congr_hom
    (((Scheme.Modules.toPresheaf scheme).map second).naturality (homOfLE contained).op)
      (1 : Γ(scheme, larger))
  change Scheme.Modules.Hom.app first smaller (scheme.presheaf.map (homOfLE contained).op 1) =
    sheaf.presheaf.map (homOfLE contained).op (Scheme.Modules.Hom.app first larger
      (1 : Γ(scheme, larger))) at first_natural
  change Scheme.Modules.Hom.app second smaller (scheme.presheaf.map (homOfLE contained).op 1) =
    sheaf.presheaf.map (homOfLE contained).op (Scheme.Modules.Hom.app second larger
      (1 : Γ(scheme, larger))) at second_natural
  have mapped_one : scheme.presheaf.map (homOfLE contained).op
      (1 : Γ(scheme, larger)) = 1 := map_one _
  rw [mapped_one] at first_natural second_natural
  rw [second_natural, relation, Scheme.Modules.map_smul, ← first_natural]

theorem restrictLocalModuleHom_isIso {scheme : Scheme} {first second : scheme.Modules}
    {smaller larger : scheme.Opens} (contained : smaller ≤ larger)
    (morphism : first.over larger ⟶ second.over larger) [IsIso morphism] :
    IsIso (restrictLocalModuleHom contained morphism) := by
  unfold restrictLocalModuleHom
  infer_instance

attribute [local instance] restrictLocalModuleHom_isIso

theorem restrictLocalModuleHom_inverse {scheme : Scheme} {first second : scheme.Modules}
    {smaller larger : scheme.Opens} (contained : smaller ≤ larger)
    (comparison : first.over larger ≅ second.over larger) :
    restrictLocalModuleHom contained comparison.inv =
      inv (restrictLocalModuleHom contained comparison.hom) := by
  let := restrictLocalModuleHom_isIso contained comparison.hom
  apply (cancel_epi (restrictLocalModuleHom contained comparison.hom)).mp
  rw [← restrictLocalModuleHom_map_comp, Iso.hom_inv_id, IsIso.hom_inv_id]
  rfl

theorem polynomialProjAwayToSection_comp_chartApp (Index : Type) (chart : Index) :
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart) ≫
      (Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
        (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)).appLE
          (polynomialDegreeOneCoordinateOpen 𝕜 Index chart) ⊤
            (by
              intro point _member
              change _ ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
              rw [← Proj.opensRange_awayι _ _ (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)]
              exact ⟨point, rfl⟩) =
      (Scheme.ΓSpecIso _).inv := by
  let chart_iso := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule Index 𝕜)
    (MvPolynomial.X chart) (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)
  have target_contains : ⊤ ≤
      (Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
        (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)) ⁻¹ᵁ
          (polynomialDegreeOneCoordinateOpen 𝕜) Index chart := by
    intro point member
    change _ ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
    rw [← Proj.opensRange_awayι _ _ (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)]
    exact ⟨point, rfl⟩
  have composition := Scheme.Hom.appLE_comp_appLE chart_iso.hom
    (Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
      (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide))
        (polynomialDegreeOneCoordinateOpen 𝕜 Index chart) ⊤ ⊤ target_contains (by simp)
  have chart_composite : chart_iso.hom ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
        (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide) =
      (polynomialDegreeOneCoordinateOpen 𝕜 Index chart).ι := by
    change chart_iso.hom ≫ (chart_iso.inv ≫ _) = _
    simp
  simp only [chart_composite] at composition
  have chart_app : chart_iso.hom.appLE ⊤ ⊤ (by simp) = chart_iso.hom.appTop := by
    exact chart_iso.hom.appLE_eq_app
  rw [chart_app] at composition
  have open_app : (polynomialDegreeOneCoordinateOpen 𝕜 Index chart).ι.appLE
      (polynomialDegreeOneCoordinateOpen 𝕜 Index chart) ⊤ (by simp) =
      (polynomialDegreeOneCoordinateOpen 𝕜 Index chart).topIso.inv := rfl
  rw [open_app] at composition
  change _ ≫ chart_iso.hom.appTop = _ at composition
  rw [Proj.basicOpenIsoSpec_hom] at composition
  change _ ≫ (Proj.basicOpenToSpec (MvPolynomial.homogeneousSubmodule Index 𝕜)
    (MvPolynomial.X chart)).app ⊤ = _ at composition
  rw [Proj.basicOpenToSpec_app_top] at composition
  have shortened :
      (Proj.awayι (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
        (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)).appLE
          (polynomialDegreeOneCoordinateOpen 𝕜 Index chart) ⊤ target_contains ≫
        (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection
          (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart) = 𝟙 _ := by
    apply (cancel_mono (polynomialDegreeOneCoordinateOpen 𝕜 Index chart).topIso.inv).mp
    simpa only [Category.assoc, Category.id_comp] using composition
  let : IsIso (Proj.awayToSection (MvPolynomial.homogeneousSubmodule Index 𝕜)
      (MvPolynomial.X chart)) := inferInstanceAs (IsIso ((Proj.basicOpenIsoAway
        (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart)
          (MvPolynomial.isHomogeneous_X 𝕜 chart) (by decide)).hom))
  apply (cancel_mono (Scheme.ΓSpecIso _).hom).mp
  apply (cancel_mono (Proj.awayToSection
    (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart))).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp] using
    congrArg (fun morphism => Proj.awayToSection
      (MvPolynomial.homogeneousSubmodule Index 𝕜) (MvPolynomial.X chart) ≫ morphism) shortened

end

end BondalThomsen

namespace TauCeti.Toric.Fan

attribute [local instance] MvPolynomial.gradedAlgebra

end TauCeti.Toric.Fan
