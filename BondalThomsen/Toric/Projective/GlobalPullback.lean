module

public import BondalThomsen.Toric.Projective.DegreeOneDescent

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen

noncomputable section

def moduleGlobalSectionHom {scheme : Scheme} (sheaf : scheme.Modules)
    (section_value : Γ(sheaf, ⊤)) :
    SheafOfModules.unit scheme.ringCatSheaf ⟶ sheaf :=
  sheaf.unitHomEquiv.symm <| sheaf.val.sectionsMk
    (fun open_set => sheaf.presheaf.map (homOfLE le_top).op section_value)
    (by
      intro larger smaller inclusion
      change sheaf.presheaf.map inclusion
        (sheaf.presheaf.map (homOfLE le_top).op section_value) = _
      rw [← ConcreteCategory.comp_apply, ← sheaf.presheaf.map_comp]
      rfl)

theorem moduleGlobalSectionHom_app {scheme : Scheme} (sheaf : scheme.Modules)
    (section_value : Γ(sheaf, ⊤)) (open_set : scheme.Opens)
    (coefficient : Γ(scheme, open_set)) :
    Scheme.Modules.Hom.app (moduleGlobalSectionHom sheaf section_value) open_set coefficient =
      coefficient • sheaf.presheaf.map (homOfLE le_top).op section_value := by
  rfl

def modulePullbackSectionHom {source target : Scheme} (map : source ⟶ target)
    {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf) :
    SheafOfModules.unit source.ringCatSheaf ⟶ (Scheme.Modules.pullback map).obj sheaf :=
  (Scheme.Modules.pullbackObjUnitIso map).inv ≫ (Scheme.Modules.pullback map).map section_map

theorem modulePullbackSectionHom_comp {source middle target : Scheme}
    (first : source ⟶ middle) (second : middle ⟶ target) {sheaf : target.Modules}
    (section_map : SheafOfModules.unit target.ringCatSheaf ⟶ sheaf) :
    modulePullbackSectionHom first (modulePullbackSectionHom second section_map) ≫
        (Scheme.Modules.pullbackComp first second).hom.app sheaf =
      modulePullbackSectionHom (first ≫ second) section_map := by
  have unit_compatibility := Scheme.Modules.pullbackObjUnitIso_comp first second
  have inverse_compatibility :
      (Scheme.Modules.pullbackObjUnitIso first).inv ≫
        (Scheme.Modules.pullback first).map (Scheme.Modules.pullbackObjUnitIso second).inv ≫
          (Scheme.Modules.pullbackComp first second).hom.app
            (SheafOfModules.unit target.ringCatSheaf) =
      (Scheme.Modules.pullbackObjUnitIso (first ≫ second)).inv := by
    have iso_compatibility :
        (Scheme.Modules.pullbackComp first second).symm.app
            (SheafOfModules.unit target.ringCatSheaf) ≪≫
          (Scheme.Modules.pullback first).mapIso (Scheme.Modules.pullbackObjUnitIso second) ≪≫
            Scheme.Modules.pullbackObjUnitIso first =
        Scheme.Modules.pullbackObjUnitIso (first ≫ second) := Iso.ext unit_compatibility
    exact congrArg Iso.inv iso_compatibility
  have naturality := (Scheme.Modules.pullbackComp first second).hom.naturality section_map
  dsimp only [Functor.comp_map] at naturality
  unfold modulePullbackSectionHom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [naturality]
  simpa only [Category.assoc] using congrArg
    (fun comparison => comparison ≫ (Scheme.Modules.pullback (first ≫ second)).map section_map)
      inverse_compatibility

theorem modulePullback_isInvertible {source target : Scheme} (map : source ⟶ target)
    (sheaf : target.Modules) [TauCeti.SheafOfModules.IsInvertible sheaf] :
    TauCeti.SheafOfModules.IsInvertible ((Scheme.Modules.pullback map).obj sheaf) := by
  obtain ⟨generators, rank_one⟩ :=
    TauCeti.SheafOfModules.IsInvertible.exists_isInvertible (M := sheaf)
  let := rank_one.isLocallyFreeData
  refine ⟨generators.pullback map, ⟨inferInstance, ?_, ?_⟩⟩
  · intro chart
    change Nonempty (generators.generators chart).I
    exact rank_one.basisNonempty chart
  · intro chart
    change Subsingleton (generators.generators chart).I
    exact rank_one.basisSubsingleton chart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (Index : Type)

def polynomialProjDegreeOneCoordinateHom (coordinate : Index) :
    SheafOfModules.unit (polynomialDegreeOneProj 𝕜 Index).ringCatSheaf ⟶
      polynomialProjDegreeOneSheaf 𝕜 Index :=
  moduleGlobalSectionHom _ (polynomialProjDegreeOneGlobalCoordinate 𝕜 Index coordinate)

theorem polynomialProjDegreeOneCoordinateHom_over (coordinate : Index) :
    (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate).over
        (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate) =
      (polynomialDegreeOneCoordinateOpenSheafFrame 𝕜 Index coordinate).hom := by
  apply SheafOfModules.hom_ext
  ext local_open : 2
  apply (LinearMap.ringLmapEquivSelf _ ℤ _).injective
  change ((polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate).over
      (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)).val.app local_open
        (1 : Γ(polynomialDegreeOneProj 𝕜 Index, local_open.unop.left)) = _
  change (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate).val.app
    (op local_open.unop.left)
      (1 : Γ(polynomialDegreeOneProj 𝕜 Index, local_open.unop.left)) = _
  rw [← SheafOfModules.unitHomEquiv_apply_coe]
  simp only [polynomialProjDegreeOneCoordinateHom, moduleGlobalSectionHom,
    Equiv.apply_symm_apply]
  apply Subtype.ext
  funext point
  dsimp [polynomialDegreeOneCoordinateOpenSheafFrame, polynomialDegreeOneChartSectionsLinearEquiv,
    polynomialProjDegreeOneGlobalCoordinate, polynomialDegreeOneChartFrame]
  rfl

theorem polynomialProjDegreeOneCoordinateHom_over_isIso (coordinate : Index) :
    IsIso ((polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate).over
      (polynomialDegreeOneCoordinateOpen 𝕜 Index coordinate)) := by
  rw [polynomialProjDegreeOneCoordinateHom_over]
  infer_instance

def polynomialProjDegreeOnePullbackSheaf {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) : source.Modules :=
  (Scheme.Modules.pullback map).obj (polynomialProjDegreeOneSheaf 𝕜 Index)

theorem polynomialProjDegreeOnePullbackSheaf_isInvertible {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) :
    TauCeti.SheafOfModules.IsInvertible (polynomialProjDegreeOnePullbackSheaf 𝕜 Index map) :=
  modulePullback_isInvertible map _

def polynomialProjDegreeOnePullbackCoordinateHom {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) (coordinate : Index) :
    SheafOfModules.unit source.ringCatSheaf ⟶ polynomialProjDegreeOnePullbackSheaf 𝕜 Index map :=
  modulePullbackSectionHom map (polynomialProjDegreeOneCoordinateHom 𝕜 Index coordinate)

theorem polynomialProjDegreeOnePullbackCoordinateOpen_cover {source : Scheme}
    (map : source ⟶ polynomialDegreeOneProj 𝕜 Index) :
    IsOpenCover (fun coordinate => map ⁻¹ᵁ (polynomialDegreeOneCoordinateOpen 𝕜) Index coordinate) := by
  apply IsOpenCover.mk
  rw [← Scheme.Hom.preimage_iSup,
    (polynomialDegreeOneCoordinateOpen_cover 𝕜 Index).iSup_eq_top, Scheme.Hom.preimage_top]

end

end BondalThomsen

namespace TauCeti.Toric.Fan

attribute [local instance] MvPolynomial.gradedAlgebra

variable {Lattice Ambient : Type} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

variable (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (divisor : fan.InvariantRayDivisor) (support : fan.HasRaySupportInequalities divisor)

theorem divisorProjectiveDegreeOneSourceChart_cover :
    IsOpenCover (fun chart : Fin (Nat.card fan.cones) =>
      (fan.affineToricChartι 𝕜 regular (fan.divisorLocalCone 𝕜 complete regular chart)).opensRange) := by
  change IsOpenCover (fun chart =>
    (fan.affineToricChartι 𝕜 regular
      ((fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).cone chart)).opensRange)
  exact (fan.invariantDivisorCharacterAtlas 𝕜 complete regular 0).covers

end TauCeti.Toric.Fan
