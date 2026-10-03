module

public import Mathlib.Tactic
public import Mathlib.Algebra.Module.Lattice
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

noncomputable section

namespace Submodule

section General

variable {baseRing : Type*} [CommRing baseRing] {ambient : Type*} [AddCommGroup ambient] [Module baseRing ambient]

def relLength (first second : Submodule baseRing ambient) : ℕ∞ :=
  Module.length baseRing (↥first ⧸ second.submoduleOf first)

lemma relLength_self (first : Submodule baseRing ambient) : relLength first first = 0 := by
  unfold relLength
  rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff]
  exact eq_top_iff.mpr fun element _ => element.2

theorem relLength_add {first second third : Submodule baseRing ambient} (hNM : second ≤ first) (hPN : third ≤ second) :
    relLength first third = relLength first second + relLength second third := by
  unfold relLength
  let inclusion : (↥second ⧸ third.submoduleOf second) →ₗ[baseRing] (↥first ⧸ third.submoduleOf first) :=
    Submodule.mapQ (third.submoduleOf second) (third.submoduleOf first) (Submodule.inclusion hNM)
      (fun element hx => hx)
  have hle : third.submoduleOf first ≤ second.submoduleOf first := fun element hx => hPN hx
  let quotientMap : (↥first ⧸ third.submoduleOf first) →ₗ[baseRing] (↥first ⧸ second.submoduleOf first) := Submodule.factor hle
  have hfmk : ∀ element : ↥second, inclusion (Submodule.Quotient.mk element) =
      Submodule.Quotient.mk (Submodule.inclusion hNM element) := fun _ => rfl
  have hgmk : ∀ otherElement : ↥first, quotientMap (Submodule.Quotient.mk otherElement) = Submodule.Quotient.mk otherElement := fun _ => rfl
  have hf : Function.Injective inclusion := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro element hx
    induction element using Submodule.Quotient.induction_on with
    | H element =>
      rw [hfmk, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact hx
  have hg : Function.Surjective quotientMap := Submodule.factor_surjective hle
  have hex : Function.Exact inclusion quotientMap := by
    intro otherElement
    constructor
    · intro hy
      induction otherElement using Submodule.Quotient.induction_on with
      | H otherElement =>
        rw [hgmk, Submodule.Quotient.mk_eq_zero] at hy
        exact ⟨Submodule.Quotient.mk ⟨(otherElement : ambient), hy⟩, by rw [hfmk]; rfl⟩
    · rintro ⟨element, rfl⟩
      induction element using Submodule.Quotient.induction_on with
      | H element =>
        rw [hfmk, hgmk, Submodule.Quotient.mk_eq_zero]
        exact element.2
  rw [Module.length_eq_add_of_exact inclusion quotientMap hf hg hex, add_comm]

theorem relLength_map {targetSpace : Type*} [AddCommGroup targetSpace] [Module baseRing targetSpace] (linearMap : ambient →ₗ[baseRing] targetSpace)
    (hφ : Function.Injective linearMap) (first second : Submodule baseRing ambient) :
    relLength (first.map linearMap) (second.map linearMap) = relLength first second := by
  unfold relLength
  symm
  refine (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective linearMap hφ first) ?_).length_eq
  ext ⟨otherElement, hy⟩
  simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, Subtype.exists]
  constructor
  · rintro ⟨element, hxM, hxN, hxy⟩
    have : linearMap element = otherElement := congrArg Subtype.val hxy
    exact ⟨element, hxN, this⟩
  · rintro ⟨element, hxN, rfl⟩
    obtain ⟨preimage, hx'M, hx'⟩ := hy
    have : preimage = element := hφ hx'
    subst this
    exact ⟨preimage, hx'M, hxN, rfl⟩

end General

section Lattice

variable {baseRing : Type*} [CommRing baseRing] [IsDomain baseRing] [IsNoetherianRing baseRing] [Ring.KrullDimLE 1 baseRing]
variable {baseField : Type*} [Field baseField] [Algebra baseRing baseField] [IsFractionRing baseRing baseField]
variable {ambient : Type*} [AddCommGroup ambient] [Module baseRing ambient] [Module baseField ambient] [IsScalarTower baseRing baseField ambient]

omit [IsNoetherianRing baseRing] [Ring.KrullDimLE 1 baseRing] in
theorem IsLattice.exists_smul_mem (second : Submodule baseRing ambient) [IsLattice baseField second] (vector : ambient) :
    ∃ denominator : baseRing, denominator ≠ 0 ∧ denominator • vector ∈ second := by
  have hv : vector ∈ span baseField (second : Set ambient) := by rw [IsLattice.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem element hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add element otherElement _ _ hx hy =>
    obtain ⟨denominator, ha, hax⟩ := hx
    obtain ⟨otherDenominator, hb, hby⟩ := hy
    refine ⟨denominator * otherDenominator, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine second.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact second.smul_mem otherDenominator hax
    · rw [mul_smul]; exact second.smul_mem denominator hby
  | smul scalar element _ hx =>
    obtain ⟨denominator, ha, hax⟩ := hx
    obtain ⟨numerator, scalarDenominator, hd, rfl⟩ := IsFractionRing.div_surjective (A := baseRing) scalar
    have hd0 : algebraMap baseRing baseField scalarDenominator ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective baseRing baseField)).mpr (nonZeroDivisors.ne_zero hd)
    refine ⟨scalarDenominator * denominator, mul_ne_zero (nonZeroDivisors.ne_zero hd) ha, ?_⟩
    have : (scalarDenominator * denominator) • ((algebraMap baseRing baseField numerator / algebraMap baseRing baseField scalarDenominator) • element) = numerator • (denominator • element) := by
      rw [← algebraMap_smul baseField (scalarDenominator * denominator), ← algebraMap_smul baseField numerator, ← algebraMap_smul baseField denominator, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact second.smul_mem numerator hax

omit [IsNoetherianRing baseRing] [Ring.KrullDimLE 1 baseRing] in

theorem IsLattice.exists_smul_le (first second : Submodule baseRing ambient) [IsLattice baseField first] [IsLattice baseField second] :
    ∃ denominator : baseRing, denominator ≠ 0 ∧ ∀ member ∈ first, denominator • member ∈ second := by
  obtain ⟨generators, hs⟩ := IsLattice.fg (A := baseField) (M := first)
  have key : ∀ finiteSet : Finset ambient, ∃ denominator : baseRing, denominator ≠ 0 ∧ ∀ member ∈ finiteSet, denominator • member ∈ second := by
    classical
    intro finiteSet
    induction finiteSet using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert element finiteSet _ ih =>
      obtain ⟨denominator, ha, hat⟩ := ih
      obtain ⟨otherDenominator, hb, hbx⟩ := IsLattice.exists_smul_mem (baseField := baseField) second element
      refine ⟨denominator * otherDenominator, mul_ne_zero ha hb, fun member hm => ?_⟩
      rcases Finset.mem_insert.mp hm with rfl | hm
      · rw [mul_smul]; exact second.smul_mem denominator hbx
      · rw [mul_comm, mul_smul]; exact second.smul_mem otherDenominator (hat member hm)
  obtain ⟨denominator, ha, has⟩ := key generators
  refine ⟨denominator, ha, fun member hm => ?_⟩
  rw [← hs] at hm
  induction hm using Submodule.span_induction with
  | mem element hx => exact has element hx
  | zero => simp
  | add element otherElement _ _ hx hy => rw [smul_add]; exact second.add_mem hx hy
  | smul numerator element _ hx => rw [smul_comm]; exact second.smul_mem numerator hx

theorem IsLattice.relLength_ne_top (first second : Submodule baseRing ambient) [IsLattice baseField first] [IsLattice baseField second] :
    relLength first second ≠ ⊤ := by
  obtain ⟨denominator, ha, haM⟩ := IsLattice.exists_smul_le (baseField := baseField) first second
  unfold relLength
  set Q := ↥first ⧸ second.submoduleOf first
  have htors : Module.IsTorsionBySet baseRing Q (Ideal.span {denominator} : Ideal baseRing) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    intro quotientElement
    induction quotientElement using Submodule.Quotient.induction_on with
    | H member =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact haM member member.2
  let _ := htors.module
  have hfl : IsFiniteLength baseRing (baseRing ⧸ Ideal.span {denominator}) :=
    isFiniteLength_quotient_span_singleton baseRing (mem_nonZeroDivisors_of_ne_zero ha)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  have : IsArtinianRing (baseRing ⧸ Ideal.span {denominator}) := isArtinian_of_tower baseRing hfl.2
  have : Module.Finite baseRing Q := inferInstance
  have : Module.Finite (baseRing ⧸ Ideal.span {denominator}) Q := Module.Finite.of_restrictScalars_finite baseRing _ Q
  rw [Module.length_eq_of_surjective (S := baseRing) (R := baseRing ⧸ Ideal.span {denominator}) (M := Q)
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end Lattice

end Submodule

end
