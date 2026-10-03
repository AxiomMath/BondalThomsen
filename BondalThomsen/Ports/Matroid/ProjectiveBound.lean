module

public import BondalThomsen.Ports.Matroid.Simplification
public import BondalThomsen.Ports.Matroid.RepresentationRank
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Matroid

open Set Submodule

variable {Label Field Vector : Type*} [_root_.Field Field]
    [AddCommGroup Vector] [Module Field Vector] {matroid : Matroid Label}

def Rep.projFun [matroid.Simple] (representation : matroid.Rep Field Vector)
    (element : matroid.E) : Projectivization Field Vector :=
  Projectivization.mk Field (representation element)
    ((representation.ne_zero_iff_isNonloop element).mpr
      ((Simple.parallel_iff_eq element.property).mpr rfl).1)

theorem Rep.projFun_injective [matroid.Simple]
    (representation : matroid.Rep Field Vector) : Function.Injective representation.projFun := by
  intro first second equality
  have spans : span Field {representation first} = span Field {representation second} := by
    simpa only [Rep.projFun, Projectivization.submodule_mk] using
      congrArg Projectivization.submodule equality
  have parallel := (representation.parallel_iff_span_eq first second).mpr
    ⟨(representation.ne_zero_iff_isNonloop first).mpr
        ((Simple.parallel_iff_eq first.property).mpr rfl).1,
      (representation.ne_zero_iff_isNonloop second).mpr
        ((Simple.parallel_iff_eq second.property).mpr rfl).1, spans⟩
  exact Subtype.ext ((Simple.parallel_iff_eq first.property).mp parallel)

theorem Rep.ground_card_le_projective_sum [matroid.Simple] [Finite Field]
    [FiniteDimensional Field Vector] (representation : matroid.Rep Field Vector) :
    Nat.card matroid.E ≤
      ∑ index ∈ Finset.range (Module.finrank Field Vector), Nat.card Field ^ index := by
  let : Finite Vector := Module.finite_of_finite Field
  have bound := Nat.card_le_card_of_injective representation.projFun
    representation.projFun_injective
  rwa [Projectivization.card_of_finrank Field Vector rfl] at bound

theorem Rep.encard_le_of_simple [matroid.Simple] [matroid.RankFinite] [Finite Field]
    (representation : matroid.Rep Field Vector) :
    matroid.E.encard ≤
      ∑ index ∈ Finset.range matroid.eRank.toNat, (ENat.card Field) ^ index := by
  classical
  obtain ⟨basisSet, basis⟩ := matroid.exists_isBase
  let : Finite basisSet := basis.finite.to_subtype
  let : FiniteDimensional Field (span Field (Set.range representation)) :=
    (representation.isBasis_of_isBase basis).finiteDimensional_of_finite
  let : Finite (span Field (Set.range representation)) := Module.finite_of_finite Field
  let : Finite matroid.E := Finite.of_injective representation.restrictSpan.projFun
    representation.restrictSpan.projFun_injective
  have bound := representation.restrictSpan.ground_card_le_projective_sum
  rw [representation.finrank_span_range_eq_eRank_toNat] at bound
  change ENat.card matroid.E ≤ _
  simp only [ENat.card_eq_coe_natCard]
  exact_mod_cast bound

theorem Representable.encard_le_of_simple [matroid.Simple] [matroid.RankFinite] [Finite Field]
    (representable : matroid.Representable Field) :
    matroid.E.encard ≤
      ∑ index ∈ Finset.range matroid.eRank.toNat, (ENat.card Field) ^ index := by
  obtain ⟨representation⟩ := representable
  exact representation.encard_le_of_simple

end Matroid
