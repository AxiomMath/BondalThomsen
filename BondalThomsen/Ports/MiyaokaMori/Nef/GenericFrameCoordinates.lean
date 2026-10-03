module

public import BondalThomsen.Ports.MiyaokaMori.LineBundleNonvanishingLocus
public import BondalThomsen.Ports.MiyaokaMori.Nef.FrameCoordinates

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped Classical

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.IsFrame

variable {scheme : Scheme.{u}} [IsIntegral scheme]
  {bundle : scheme.Modules} {region : scheme.Opens} {generator : Γ(bundle, region)}

theorem genericPoint_mem_region (region : scheme.Opens) [Nonempty region] :
    genericPoint scheme ∈ region := by
  obtain ⟨point, contains⟩ := (inferInstance : Nonempty region)
  exact (genericPoint_specializes point).mem_open region.isOpen contains

def genericGenerator (_frame : IsFrame bundle region generator) [Nonempty region] :
    bundle.presheaf.stalk (genericPoint scheme) :=
  bundle.presheaf.germ region (genericPoint scheme) (genericPoint_mem_region region) generator

theorem genericGenerator_ne_zero (frame : IsFrame bundle region generator) [Nonempty region] :
    frame.genericGenerator ≠ 0 := by
  intro zero
  apply frame.germ_notMem_maximalIdeal_smul (genericPoint_mem_region region)
  change frame.genericGenerator ∈ _
  rw [zero]
  exact Submodule.zero_mem _

def genericCoordinate (frame : IsFrame bundle region generator) [Nonempty region] :
    bundle.presheaf.stalk (genericPoint scheme) ≃ₗ[scheme.functionField] scheme.functionField := by
  refine (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton scheme.functionField _ frame.genericGenerator) ⟨?_, ?_⟩).symm
  · intro first second equality
    have zero : (first - second) • frame.genericGenerator = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr equality
    exact sub_eq_zero.mp ((smul_eq_zero.mp zero).resolve_right frame.genericGenerator_ne_zero)
  · intro rationalSection
    have member : rationalSection ∈ Submodule.span scheme.functionField
        ({frame.genericGenerator} : Set (bundle.presheaf.stalk (genericPoint scheme))) := by
      rw [show Submodule.span scheme.functionField {frame.genericGenerator} = ⊤ from
        frame.span_germ_eq_top (genericPoint_mem_region region)]
      trivial
    exact Submodule.mem_span_singleton.mp member

theorem genericCoordinate_smul_generator (frame : IsFrame bundle region generator)
    [Nonempty region] (rationalSection : bundle.presheaf.stalk (genericPoint scheme)) :
    frame.genericCoordinate rationalSection • frame.genericGenerator = rationalSection :=
  (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton scheme.functionField _ frame.genericGenerator)
    (by
      change Function.Bijective frame.genericCoordinate.symm
      exact frame.genericCoordinate.symm.bijective)).apply_symm_apply rationalSection

theorem genericCoordinate_germ (frame : IsFrame bundle region generator) [Nonempty region]
    {smaller : scheme.Opens} (subset : smaller ≤ region) [Nonempty smaller]
    (sectionValue : Γ(bundle, smaller)) :
    frame.genericCoordinate
        (bundle.presheaf.germ smaller (genericPoint scheme) (genericPoint_mem_region smaller) sectionValue) =
      scheme.germToFunctionField smaller (frame.coord subset sectionValue) := by
  apply frame.genericCoordinate.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change bundle.presheaf.germ smaller (genericPoint scheme) _ sectionValue =
    scheme.germToFunctionField smaller (frame.coord subset sectionValue) • frame.genericGenerator
  have representation := congrArg
    (bundle.presheaf.germ smaller (genericPoint scheme) (genericPoint_mem_region smaller))
    (frame.coord_smul_frame subset sectionValue)
  rw [germ_smul', TopCat.Presheaf.germ_res_apply] at representation
  exact representation.symm

theorem genericCoordinate_ne_zero (frame : IsFrame bundle region generator) [Nonempty region]
    (rationalSection : bundle.presheaf.stalk (genericPoint scheme)) (nonzero : rationalSection ≠ 0) :
    frame.genericCoordinate rationalSection ≠ 0 :=
  fun zero => nonzero (frame.genericCoordinate.map_eq_zero_iff.mp zero)

theorem genericCoordinate_unique (frame : IsFrame bundle region generator) [Nonempty region]
    (rationalSection : bundle.presheaf.stalk (genericPoint scheme)) (scalar : scheme.functionField)
    (representation : scalar • frame.genericGenerator = rationalSection) :
    frame.genericCoordinate rationalSection = scalar := by
  apply frame.genericCoordinate.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact representation.symm

theorem genericCoordinate_restrict (frame : IsFrame bundle region generator) [Nonempty region]
    {smaller : scheme.Opens} (subset : smaller ≤ region) [Nonempty smaller]
    (rationalSection : bundle.presheaf.stalk (genericPoint scheme)) :
    (frame.restrict subset).genericCoordinate rationalSection = frame.genericCoordinate rationalSection := by
  apply (frame.restrict subset).genericCoordinate_unique
  change frame.genericCoordinate rationalSection •
    bundle.presheaf.germ smaller (genericPoint scheme) _ (bundle.res subset generator) = rationalSection
  rw [TopCat.Presheaf.germ_res_apply]
  exact frame.genericCoordinate_smul_generator rationalSection

theorem genericCoordinate_transition {secondRegion : scheme.Opens}
    {secondGenerator : Γ(bundle, secondRegion)}
    (firstFrame : IsFrame bundle region generator)
    (secondFrame : IsFrame bundle secondRegion secondGenerator)
    [Nonempty region] [Nonempty secondRegion] [Nonempty ↑(region ⊓ secondRegion)] :
    ∃ unit : Γ(scheme, region ⊓ secondRegion)ˣ,
      ∀ rationalSection : bundle.presheaf.stalk (genericPoint scheme),
        firstFrame.genericCoordinate rationalSection =
          scheme.germToFunctionField (region ⊓ secondRegion) unit *
            secondFrame.genericCoordinate rationalSection := by
  let overlap := region ⊓ secondRegion
  let firstOverlap := firstFrame.restrict (inf_le_left : overlap ≤ region)
  let secondOverlap := secondFrame.restrict (inf_le_right : overlap ≤ secondRegion)
  obtain ⟨unit, generatorEquation⟩ := firstOverlap.unit_transition secondOverlap
  have genericEquation : scheme.germToFunctionField overlap unit • firstOverlap.genericGenerator =
      secondOverlap.genericGenerator := by
    have equation := congrArg
      (bundle.presheaf.germ overlap (genericPoint scheme) (genericPoint_mem_region overlap))
      generatorEquation
    rw [germ_smul'] at equation
    exact equation
  refine ⟨unit, fun rationalSection => ?_⟩
  rw [← firstFrame.genericCoordinate_restrict (inf_le_left : overlap ≤ region) rationalSection,
    ← secondFrame.genericCoordinate_restrict (inf_le_right : overlap ≤ secondRegion) rationalSection]
  apply firstOverlap.genericCoordinate_unique
  rw [mul_comm, mul_smul, genericEquation]
  exact secondOverlap.genericCoordinate_smul_generator rationalSection

end AlgebraicGeometry.Scheme.Modules.IsFrame

namespace AlgebraicGeometry.Scheme.Modules

theorem exists_nonzero_genericSection {scheme : Scheme.{u}} [IsIntegral scheme]
    (bundle : scheme.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible scheme bundle] :
    ∃ rationalSection : bundle.presheaf.stalk (genericPoint scheme), rationalSection ≠ 0 := by
  obtain ⟨region, contains, generator, frame⟩ := exists_frame bundle (genericPoint scheme)
  let : Nonempty region := ⟨⟨genericPoint scheme, contains⟩⟩
  exact ⟨frame.genericGenerator, frame.genericGenerator_ne_zero⟩

end AlgebraicGeometry.Scheme.Modules
