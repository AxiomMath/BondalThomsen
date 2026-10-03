module

public import BondalThomsen.Fan.CompleteFanCharacters
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import Mathlib.AlgebraicGeometry.Cover.Open

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Multiplicative

variable (𝕜 : Type) [Field 𝕜]

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def toricChartOpenCover (fan : Fan embedding) (regular : fan.IsRegular) :
    (fan.algebraicRealization 𝕜 regular).OpenCover where
  I₀ := fan.cones
  X := fan.affineToricChart 𝕜
  f := fan.affineToricChartι 𝕜 regular
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun point => fan.exists_affineToricChartι_apply_eq 𝕜 regular point, inferInstance⟩

noncomputable def chartGlobalSections (fan : Fan embedding) (regular : fan.IsRegular)
    (cone : fan.cones) :
    Γ(fan.algebraicRealization 𝕜 regular, ⊤) →+* affineCoordinateRing 𝕜 fan.lattice cone.val :=
  (Scheme.ΓSpecIso (CommRingCat.of (affineCoordinateRing 𝕜 fan.lattice cone.val))).hom.hom.comp
    (fan.affineToricChartι 𝕜 regular cone).appTop.hom

noncomputable def torusLaurentSections (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) :
    Γ(fan.algebraicRealization 𝕜 regular, ⊤) →+* fan.LaurentCharacterAlgebra 𝕜 :=
  (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).toRingHom.comp
    (fan.chartGlobalSections 𝕜 regular (fan.botCone nonempty))

theorem denseTorusCoordinateRingEquiv_faceMap (fan : Fan embedding) (cone : fan.cones) :
    (denseTorusCoordinateRingEquiv 𝕜 fan.lattice).toAlgHom.comp
      (faceAffineCoordinateRingMap 𝕜 fan.lattice
        ((fan.isToricCone cone.property).salient.bot_isFaceOf)) =
      fan.coneLaurentMap 𝕜 cone.val := by
  apply MonoidAlgebra.algHom_ext
  · intro character
    change (denseTorusCoordinateRingEquiv 𝕜 fan.lattice)
      (faceAffineCoordinateRingMap 𝕜 fan.lattice
        ((fan.isToricCone cone.property).salient.bot_isFaceOf)
        (MonoidAlgebra.single (ofAdd (toAdd character)) 1)) = _
    rw [faceAffineCoordinateRingMap_single, denseTorusCoordinateRingEquiv_single]
    simp [coneLaurentMap]
  · exact Subsingleton.elim _ _

theorem torusLaurentSections_eq_chart (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (section_value : Γ(fan.algebraicRealization 𝕜 regular, ⊤)) :
    fan.torusLaurentSections 𝕜 regular nonempty section_value =
      fan.coneLaurentMap 𝕜 cone.val (fan.chartGlobalSections 𝕜 regular cone section_value) := by
  have chart_factor := fan.denseTorusι_face 𝕜 regular cone
  have same_inclusion := fan.denseTorusι_eq 𝕜 regular nonempty (Nonempty.intro cone)
  have factor := congrArg Scheme.Hom.appTop (same_inclusion.trans chart_factor)
  rw [Scheme.Hom.comp_appTop] at factor
  have naturality := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (faceAffineCoordinateRingMap 𝕜 fan.lattice
      ((fan.isToricCone cone.property).salient.bot_isFaceOf)).toRingHom)
  change (denseTorusCoordinateRingEquiv 𝕜 fan.lattice)
    ((Scheme.ΓSpecIso _).hom ((fan.denseTorusι 𝕜 regular nonempty).appTop section_value)) = _
  rw [factor]
  simp only [ConcreteCategory.comp_apply]
  have naturality_value := ConcreteCategory.congr_hom naturality
    ((fan.affineToricChartι 𝕜 regular cone).appTop section_value)
  change (Scheme.ΓSpecIso _).hom
    ((faceAffineToricSchemeMap 𝕜 fan.lattice
      ((fan.isToricCone cone.property).salient.bot_isFaceOf)).appTop
      ((fan.affineToricChartι 𝕜 regular cone).appTop section_value)) = _ at naturality_value
  rw [naturality_value]
  exact DFunLike.congr_fun
    (fan.denseTorusCoordinateRingEquiv_faceMap 𝕜 cone)
    (fan.chartGlobalSections 𝕜 regular cone section_value)

theorem torusLaurentSections_injective (fan : Fan embedding) (regular : fan.IsRegular)
    (nonempty : Nonempty fan.cones) :
    Function.Injective (fan.torusLaurentSections 𝕜 regular nonempty) := by
  intro first second same
  apply (fan.toricChartOpenCover 𝕜 regular).ext_elem first second
  intro cone
  have local_same := (fan.coneLaurentMap_injective 𝕜 cone.val)
    ((fan.torusLaurentSections_eq_chart 𝕜 regular nonempty cone first).symm.trans
      (same.trans (fan.torusLaurentSections_eq_chart 𝕜 regular nonempty cone second)))
  exact (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective local_same

theorem torusLaurentSections_eq_constant (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones)
    (section_value : Γ(fan.algebraicRealization 𝕜 regular, ⊤)) :
    fan.torusLaurentSections 𝕜 regular nonempty section_value =
      MonoidAlgebra.single 1
        ((fan.torusLaurentSections 𝕜 regular nonempty section_value).coeff 1) := by
  apply fan.laurent_eq_constant_of_all_cone_images 𝕜 complete
  intro cone member
  exact ⟨fan.chartGlobalSections 𝕜 regular ⟨cone, member⟩ section_value,
    (fan.torusLaurentSections_eq_chart 𝕜 regular nonempty ⟨cone, member⟩ section_value).symm⟩

noncomputable def structureCocone (fan : Fan embedding) :
    Cocone (fan.affineToricDiagram 𝕜) where
  pt := Spec (CommRingCat.of 𝕜)
  ι := {
    app := fun cone => Spec.map
      (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val)))
    naturality := by
      intro first second inclusion
      change faceAffineToricSchemeMap 𝕜 fan.lattice
        (fan.isFaceOf_of_le second.property first.property (leOfHom inclusion)) ≫
          Spec.map _ = _ ≫ 𝟙 _
      rw [Category.comp_id, faceAffineToricSchemeMap_def, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro coefficient
      exact (faceAffineCoordinateRingMap 𝕜 fan.lattice
        (fan.isFaceOf_of_le second.property first.property (leOfHom inclusion))).commutes coefficient }

noncomputable def structureMap (fan : Fan embedding) (regular : fan.IsRegular) :
    fan.algebraicRealization 𝕜 regular ⟶ Spec (CommRingCat.of 𝕜) :=
  (fan.isColimitAffineToricCocone 𝕜 regular).desc (fan.structureCocone 𝕜)

theorem chartι_comp_structureMap (fan : Fan embedding) (regular : fan.IsRegular)
    (cone : fan.cones) :
    fan.affineToricChartι 𝕜 regular cone ≫ fan.structureMap 𝕜 regular =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val))) :=
  (fan.isColimitAffineToricCocone 𝕜 regular).fac (fan.structureCocone 𝕜) cone

noncomputable def scalarGlobalSections (fan : Fan embedding) (regular : fan.IsRegular) :
    𝕜 →+* Γ(fan.algebraicRealization 𝕜 regular, ⊤) :=
  (fan.structureMap 𝕜 regular).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv.hom

theorem chartGlobalSections_scalarGlobalSections (fan : Fan embedding)
    (regular : fan.IsRegular) (cone : fan.cones) (coefficient : 𝕜) :
    fan.chartGlobalSections 𝕜 regular cone (fan.scalarGlobalSections 𝕜 regular coefficient) =
      algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val) coefficient := by
  have factor := congrArg Scheme.Hom.appTop
    (fan.chartι_comp_structureMap 𝕜 regular cone)
  rw [Scheme.Hom.comp_appTop] at factor
  have naturality := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val)))
  change (Scheme.ΓSpecIso _).hom
    ((fan.affineToricChartι 𝕜 regular cone).appTop
      ((fan.structureMap 𝕜 regular).appTop ((Scheme.ΓSpecIso _).inv coefficient))) = _
  have factor_value := ConcreteCategory.congr_hom factor
    ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv coefficient)
  simp only [ConcreteCategory.comp_apply] at factor_value
  rw [factor_value]
  have naturality_value := ConcreteCategory.congr_hom naturality
    ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv coefficient)
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at naturality_value
  change _ = algebraMap 𝕜 (affineCoordinateRing 𝕜 fan.lattice cone.val) coefficient at naturality_value
  exact naturality_value

theorem torusLaurentSections_scalarGlobalSections (fan : Fan embedding)
    (regular : fan.IsRegular) (nonempty : Nonempty fan.cones) (coefficient : 𝕜) :
    fan.torusLaurentSections 𝕜 regular nonempty (fan.scalarGlobalSections 𝕜 regular coefficient) =
      MonoidAlgebra.single 1 coefficient := by
  rw [fan.torusLaurentSections_eq_chart 𝕜 regular nonempty nonempty.some,
    fan.chartGlobalSections_scalarGlobalSections 𝕜]
  exact (fan.coneLaurentMap 𝕜 nonempty.some.val).commutes coefficient

theorem scalarGlobalSections_bijective (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) : Function.Bijective (fan.scalarGlobalSections 𝕜 regular) := by
  obtain ⟨cone, member, _⟩ := fan.isComplete_iff.mp complete 0
  let nonempty : Nonempty fan.cones := ⟨⟨cone, member⟩⟩
  constructor
  · intro first second same
    have polynomial_same := congrArg (fan.torusLaurentSections 𝕜 regular nonempty) same
    rw [fan.torusLaurentSections_scalarGlobalSections 𝕜,
      fan.torusLaurentSections_scalarGlobalSections 𝕜] at polynomial_same
    have coefficient_same := congrArg (fun polynomial : fan.LaurentCharacterAlgebra 𝕜 =>
      polynomial.coeff 1) polynomial_same
    simpa using coefficient_same
  · intro section_value
    refine ⟨(fan.torusLaurentSections 𝕜 regular nonempty section_value).coeff 1, ?_⟩
    apply fan.torusLaurentSections_injective 𝕜 regular nonempty
    rw [fan.torusLaurentSections_scalarGlobalSections 𝕜]
    exact (fan.torusLaurentSections_eq_constant 𝕜 complete regular nonempty section_value).symm

noncomputable def scalarGlobalFunctionsEquiv (fan : Fan embedding) (complete : fan.IsComplete)
    (regular : fan.IsRegular) : 𝕜 ≃+* Γ(fan.algebraicRealization 𝕜 regular, ⊤) :=
  RingEquiv.ofBijective (fan.scalarGlobalSections 𝕜 regular)
    (fan.scalarGlobalSections_bijective 𝕜 complete regular)

end TauCeti.Toric.Fan
