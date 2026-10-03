module

public import BondalThomsen.Collection.BondalThomsenSummandRegrouping
public import BondalThomsen.Toric.Divisor.DivisorExtCohomology
public import BondalThomsen.DeepFan.CriterionForward

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory

variable (𝕜 : Type) [Field 𝕜]
open TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped Classical

namespace BondalThomsen

local instance bondalThomsenModulesFiniteBiproducts (scheme : Scheme) :
    HasFiniteBiproducts scheme.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

noncomputable def repeatedBiproductExtEquiv
    {Category : Type*} [CategoryTheory.Category Category] [Abelian Category]
    [HasExt Category] [HasFiniteBiproducts Category]
    {Index : Type} [Fintype Index] (source : Category)
    (objects : Index → Category) (multiplicity : Index → ℕ) (degree : ℕ) :
    Abelian.Ext source
        (⨁ fun index : Index => ⨁ fun _ : Fin (multiplicity index) => objects index) degree ≃+
      (∀ index, Fin (multiplicity index) → Abelian.Ext source (objects index) degree) :=
  (Abelian.Ext.addEquivBiproduct source
      (biproduct.isBilimit (fun index : Index =>
        ⨁ fun _ : Fin (multiplicity index) => objects index)) degree).trans
    (AddEquiv.piCongrRight (fun index => Abelian.Ext.addEquivBiproduct source
      (biproduct.isBilimit (fun _ : Fin (multiplicity index) => objects index)) degree))

noncomputable def internalHomCohomologyRepeatedExtEquiv
    {scheme : Scheme} [IsIntegral scheme]
    {Index : Type} [Fintype Index]
    (source : TauCeti.AlgebraicGeometry.InvertibleSheaf scheme)
    (target : scheme.Modules) (objects : Index → scheme.Modules)
    (multiplicity : Index → ℕ)
    (decomposition : target ≅
      (⨁ fun index : Index => ⨁ fun _ : Fin (multiplicity index) => objects index))
    (degree : ℕ) :
    Cohomology ((ihom source.obj).obj target) degree ≃+
      (∀ index, Fin (multiplicity index) → Abelian.Ext source.obj (objects index) degree) := by
  exact (SheafExtCohomologyDimensionShift.invertibleSheafExtCohomologyEquiv
      source target degree).symm.trans
    ((((Abelian.extFunctor degree).obj (Opposite.op source.obj)).mapIso
      decomposition).addCommGroupIsoToAddEquiv.trans
        (repeatedBiproductExtEquiv source.obj objects multiplicity degree))

end BondalThomsen

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem toricMultiplicationPushforward_internalHom_cohomology_decomposition
    [Module.Free ℤ Lattice] [Module.Finite ℤ Lattice]
    (fan : Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (thomsen : fan.ToricMultiplicationResidueDecomposition 𝕜 complete regular) :
    ∃ degree : ℕ, 0 < degree ∧ ∃ multiplicity : fan.BondalThomsenClass → ℕ,
      (∀ member, 0 < multiplicity member) ∧
      (∑ member, multiplicity member) = degree ^ Module.finrank ℤ Lattice ∧
      ∀ (source : TauCeti.AlgebraicGeometry.InvertibleSheaf
        (fan.algebraicRealization 𝕜 regular)) (cohomology_degree : ℕ),
        Nonempty (Cohomology ((ihom source.obj).obj
          (fan.toricMultiplicationPushforward 𝕜 regular degree)) cohomology_degree ≃+
          (∀ member, Fin (multiplicity member) →
            Abelian.Ext source.obj
              (fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val).obj
              cohomology_degree)) := by
  let := fan.algebraicRealization_isIntegral 𝕜 regular
    (fan.completeFan_nonemptyCones complete)
  obtain ⟨degree, positive, multiplicity, multiplicities_positive, total,
      ⟨decomposition⟩⟩ :=
    fan.toricMultiplicationPushforward_positive_collection_multiplicities 𝕜
      complete regular thomsen
  refine ⟨degree, positive, multiplicity, multiplicities_positive, total, ?_⟩
  intro source cohomology_degree
  exact ⟨BondalThomsen.internalHomCohomologyRepeatedExtEquiv source _
    (fun member : fan.BondalThomsenClass =>
      (fan.invariantClassInvertibleSheaf 𝕜 complete regular member.val).obj)
    multiplicity decomposition cohomology_degree⟩

end TauCeti.Toric.Fan
