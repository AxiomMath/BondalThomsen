module

public import BondalThomsen.Toric.Canonical.ExteriorTildeDescent

@[expose] public section

open AlgebraicGeometry CategoryTheory Module Opposite TopologicalSpace

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

variable (𝕜 : Type) [Field 𝕜]

namespace BondalThomsen.CanonicalFanChart

variable {Chart SchemeModel : Scheme}
    (inclusion : Chart ⟶ SchemeModel) [IsOpenImmersion inclusion]

noncomputable def cotangentPullbackIso {Base : Scheme}
    (structureMap : SchemeModel ⟶ Base) :
    (Scheme.Modules.pullback inclusion).obj (cotangentSheaf structureMap) ≅
      cotangentSheaf (inclusion ≫ structureMap) :=
  ((Scheme.Modules.restrictFunctorIsoPullback inclusion).app
    (cotangentSheaf structureMap)).symm ≪≫
      CanonicalChart.cotangentSheafRestrictionIso inclusion structureMap

noncomputable def exteriorRestrictionSectionIso
    (modules : SchemeModel.PresheafOfModules) (degree : ℕ) (domain : Chart.Opensᵒᵖ) :
    (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := Chart.presheaf)
      ((CanonicalChart.presheafRestriction inclusion).obj modules) degree).obj domain ≅
    ((CanonicalChart.presheafRestriction inclusion).obj
      (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := SchemeModel.presheaf)
        modules degree)).obj domain := by
  let Source := Chart.presheaf.obj domain
  let Target := SchemeModel.presheaf.obj (inclusion.opensFunctor.op.obj domain)
  let Native : ModuleCat.{0} Target := modules.obj (inclusion.opensFunctor.op.obj domain)
  let coordinates : Source ≅ Target := (inclusion.appIso domain.unop).symm
  exact CanonicalChart.exteriorModuleCoefficientIso.{0, 0} coordinates Native degree

theorem exteriorRestrictionSectionIso_wedge
    (modules : SchemeModel.PresheafOfModules) (degree : ℕ) (domain : Chart.Opensᵒᵖ)
    (vectors : Fin degree → ((CanonicalChart.presheafRestriction inclusion).obj modules).obj domain) :
    (exteriorRestrictionSectionIso inclusion modules degree domain).hom
        (exteriorPower.ιMulti (Chart.presheaf.obj domain) degree vectors) =
      exteriorPower.ιMulti
        (M := modules.obj (inclusion.opensFunctor.op.obj domain))
        (SchemeModel.presheaf.obj (inclusion.opensFunctor.op.obj domain)) degree
        (fun index => (vectors index : modules.obj (inclusion.opensFunctor.op.obj domain))) :=
  CanonicalChart.exteriorModuleCoefficientIso_wedge _ _ _ _

noncomputable def exteriorPresheafRestrictionIso
    (modules : SchemeModel.PresheafOfModules) (degree : ℕ) :
    exteriorPresheaf.{0, 0, 0, 0} (Coefficients := Chart.presheaf)
        ((CanonicalChart.presheafRestriction inclusion).obj modules) degree ≅
      (CanonicalChart.presheafRestriction inclusion).obj
        (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := SchemeModel.presheaf) modules degree) := by
  refine PresheafOfModules.isoMk (exteriorRestrictionSectionIso inclusion modules degree) ?_
  intro domain smaller restriction
  apply ModuleCat.hom_ext
  apply exteriorLinear_ext (Coefficient := Chart.presheaf.obj domain)
    (Source := ((CanonicalChart.presheafRestriction inclusion).obj modules).obj domain)
    (degree := degree)
  intro vectors
  change (exteriorRestrictionSectionIso inclusion modules degree smaller).hom
      ((exteriorPresheaf.{0, 0, 0, 0} (Coefficients := Chart.presheaf)
        ((CanonicalChart.presheafRestriction inclusion).obj modules) degree).map restriction
          (exteriorPower.ιMulti (Chart.presheaf.obj domain) degree vectors)) =
    (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := SchemeModel.presheaf) modules degree).map
      (inclusion.opensFunctor.op.map restriction)
        ((exteriorRestrictionSectionIso inclusion modules degree domain).hom
          (exteriorPower.ιMulti (Chart.presheaf.obj domain) degree vectors))
  rw [exteriorPresheaf_map_wedge, exteriorRestrictionSectionIso_wedge,
    exteriorRestrictionSectionIso_wedge, exteriorPresheaf_map_wedge]
  rfl

noncomputable def exteriorSheafRestrictionIso (modules : SchemeModel.Modules) (degree : ℕ) :
    (exteriorSheaf modules degree).restrict inclusion ≅
      exteriorSheaf (modules.restrict inclusion) degree :=
  CanonicalChart.restrictionSheafificationIso inclusion
      (exteriorPresheaf.{0, 0, 0, 0} (Coefficients := SchemeModel.presheaf) modules.val degree) ≪≫
    (PresheafOfModules.sheafification (𝟙 Chart.ringCatSheaf.obj)).mapIso
      (exteriorPresheafRestrictionIso inclusion modules.val degree).symm

noncomputable def canonicalExteriorRestrictionIso {Base : Scheme}
    (structureMap : SchemeModel ⟶ Base) (degree : ℕ) :
    (canonicalExteriorSheaf structureMap degree).restrict inclusion ≅
      canonicalExteriorSheaf (inclusion ≫ structureMap) degree :=
  exteriorSheafRestrictionIso inclusion (cotangentSheaf structureMap) degree ≪≫
    CanonicalTopExterior.exteriorSheafIso
      (CanonicalChart.cotangentSheafRestrictionIso inclusion structureMap) degree

end BondalThomsen.CanonicalFanChart

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def affineToricChartCotangentPullbackIso (fan : Fan embedding)
    (regular : fan.IsRegular) (cone : fan.cones) :
    (Scheme.Modules.pullback (fan.affineToricChartι 𝕜 regular cone)).obj
        (BondalThomsen.cotangentSheaf (fan.structureMap 𝕜 regular)) ≅
      BondalThomsen.cotangentSheaf (Spec.map (CommRingCat.ofHom
        (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val)))) := by
  let comparison := BondalThomsen.CanonicalFanChart.cotangentPullbackIso
    (fan.affineToricChartι 𝕜 regular cone) (fan.structureMap 𝕜 regular)
  rw [fan.chartι_comp_structureMap 𝕜 regular cone] at comparison
  exact comparison

noncomputable def affineToricChartCanonicalRestrictionIso (fan : Fan embedding)
    (regular : fan.IsRegular) (cone : fan.cones) (dimension : ℕ) :
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).restrict
        (fan.affineToricChartι 𝕜 regular cone) ≅
      BondalThomsen.canonicalExteriorSheaf (Spec.map (CommRingCat.ofHom
        (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val)))) dimension := by
  let comparison := BondalThomsen.CanonicalFanChart.canonicalExteriorRestrictionIso
    (fan.affineToricChartι 𝕜 regular cone) (fan.structureMap 𝕜 regular) dimension
  rw [fan.chartι_comp_structureMap 𝕜 regular cone] at comparison
  exact comparison

variable {dimension : ℕ}

noncomputable def basisConeCanonicalRestrictionTildeIso (fan : Fan embedding)
    (regular : fan.IsRegular) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_mem : PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones) :
    let cone : fan.cones :=
      ⟨PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))), cone_mem⟩
    let CoordinateRing := CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice cone.val)
    (fan.toricCanonicalExteriorSheaf 𝕜 regular dimension).restrict
        (fan.affineToricChartι 𝕜 regular cone) ≅
      tilde (BondalThomsen.CanonicalExteriorDescent.topExteriorModule CoordinateRing
        (BondalThomsen.CanonicalAffine.differentialModule (CommRingCat.of 𝕜) CoordinateRing)
        (dimension := dimension)) :=
  fan.affineToricChartCanonicalRestrictionIso 𝕜 regular
      ⟨PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))), cone_mem⟩ dimension ≪≫
    fan.basisConeCanonicalExteriorTildeIso 𝕜 basis

end TauCeti.Toric.Fan
