module

public import BondalThomsen.Ports.MiyaokaMori.Nef.LatticeRelativeLength

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

noncomputable section

namespace Submodule

variable {baseRing : Type*} [CommRing baseRing] [IsDomain baseRing] [IsNoetherianRing baseRing] [Ring.KrullDimLE 1 baseRing]
variable {baseField : Type*} [Field baseField] [Algebra baseRing baseField] [IsFractionRing baseRing baseField]
variable {ambient : Type*} [AddCommGroup ambient] [Module baseRing ambient] [Module baseField ambient] [IsScalarTower baseRing baseField ambient]
variable {targetSpace : Type*} [AddCommGroup targetSpace] [Module baseRing targetSpace] [Module baseField targetSpace] [IsScalarTower baseRing baseField targetSpace]

omit [Ring.KrullDimLE 1 baseRing] in

theorem IsLattice.inf' (first second : Submodule baseRing ambient) [IsLattice baseField first] [IsLattice baseField second] :
    IsLattice baseField (first ⊓ second) where
  fg := by
    have : IsNoetherian baseRing ↥(first ⊓ second) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  span_eq_top := by
    rw [eq_top_iff]
    intro vector _
    obtain ⟨denominator, ha, hav⟩ := IsLattice.exists_smul_mem (baseField := baseField) first vector
    obtain ⟨otherDenominator, hb, hbv⟩ := IsLattice.exists_smul_mem (baseField := baseField) second vector
    have hab : algebraMap baseRing baseField (denominator * otherDenominator) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective baseRing baseField)).mpr (mul_ne_zero ha hb)
    have hmem : (denominator * otherDenominator) • vector ∈ first ⊓ second := by
      refine ⟨?_, ?_⟩
      · rw [mul_comm, mul_smul]; exact first.smul_mem otherDenominator hav
      · rw [mul_smul]; exact second.smul_mem denominator hbv
    have : vector = (algebraMap baseRing baseField (denominator * otherDenominator))⁻¹ • ((denominator * otherDenominator) • vector) := by
      rw [← algebraMap_smul baseField (denominator * otherDenominator) vector, smul_smul, inv_mul_cancel₀ hab, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

omit [IsNoetherianRing baseRing] [Ring.KrullDimLE 1 baseRing] [IsDomain baseRing] [IsFractionRing baseRing baseField] in

theorem IsLattice.map' (linearMap : ambient →ₗ[baseField] targetSpace) (hφ : Function.Surjective linearMap) (first : Submodule baseRing ambient)
    [IsLattice baseField first] : IsLattice baseField (first.map (linearMap.restrictScalars baseRing)) where
  fg := (IsLattice.fg (A := baseField) (M := first)).map _
  span_eq_top := by
    have equality : ((first.map (linearMap.restrictScalars baseRing) : Submodule baseRing targetSpace) : Set targetSpace) = linearMap '' (first : Set ambient) := rfl
    rw [equality, Submodule.span_image, IsLattice.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr hφ]

def latDist (first otherFirst : Submodule baseRing ambient) : ℤ :=
  ((relLength first (first ⊓ otherFirst)).toNat : ℤ) - ((relLength otherFirst (first ⊓ otherFirst)).toNat : ℤ)

theorem latDist_eq_of_le (first otherFirst second : Submodule baseRing ambient) [IsLattice baseField first] [IsLattice baseField otherFirst]
    [IsLattice baseField second] (equality : second ≤ first) (otherEquality : second ≤ otherFirst) :
    latDist first otherFirst = ((relLength first second).toNat : ℤ) - ((relLength otherFirst second).toNat : ℤ) := by
  have : IsLattice baseField (first ⊓ otherFirst) := IsLattice.inf' first otherFirst
  have hN : second ≤ first ⊓ otherFirst := le_inf equality otherEquality
  unfold latDist
  rw [relLength_add (inf_le_left : first ⊓ otherFirst ≤ first) hN, relLength_add (inf_le_right : first ⊓ otherFirst ≤ otherFirst) hN,
    ENat.toNat_add (IsLattice.relLength_ne_top (baseField := baseField) _ _)
      (IsLattice.relLength_ne_top (baseField := baseField) _ _),
    ENat.toNat_add (IsLattice.relLength_ne_top (baseField := baseField) _ _)
      (IsLattice.relLength_ne_top (baseField := baseField) _ _)]
  push_cast
  ring

omit [IsDomain baseRing] [IsNoetherianRing baseRing] [Ring.KrullDimLE 1 baseRing] in
theorem latDist_self (first : Submodule baseRing ambient) : latDist first first = 0 := by
  simp [latDist]

omit [IsDomain baseRing] [IsNoetherianRing baseRing] [Ring.KrullDimLE 1 baseRing] in
theorem latDist_comm (first otherFirst : Submodule baseRing ambient) : latDist first otherFirst = - latDist otherFirst first := by
  unfold latDist
  rw [inf_comm]
  ring

omit [IsDomain baseRing] [IsNoetherianRing baseRing] [Ring.KrullDimLE 1 baseRing] in
theorem latDist_of_le {first second : Submodule baseRing ambient} (equality : second ≤ first) :
    latDist first second = ((relLength first second).toNat : ℤ) := by
  unfold latDist
  rw [inf_eq_right.mpr equality, relLength_self]
  simp

theorem latDist_triangle (first otherFirst thirdFirst : Submodule baseRing ambient) [IsLattice baseField first] [IsLattice baseField otherFirst]
    [IsLattice baseField thirdFirst] : latDist first thirdFirst = latDist first otherFirst + latDist otherFirst thirdFirst := by
  have h1 : IsLattice baseField (first ⊓ otherFirst) := IsLattice.inf' first otherFirst
  have h2 : IsLattice baseField (first ⊓ otherFirst ⊓ thirdFirst) := IsLattice.inf' (first ⊓ otherFirst) thirdFirst
  have hM : first ⊓ otherFirst ⊓ thirdFirst ≤ first := inf_le_left.trans inf_le_left
  have hM' : first ⊓ otherFirst ⊓ thirdFirst ≤ otherFirst := inf_le_left.trans inf_le_right
  have hM'' : first ⊓ otherFirst ⊓ thirdFirst ≤ thirdFirst := inf_le_right
  rw [latDist_eq_of_le (baseField := baseField) first thirdFirst _ hM hM'', latDist_eq_of_le (baseField := baseField) first otherFirst _ hM hM',
    latDist_eq_of_le (baseField := baseField) otherFirst thirdFirst _ hM' hM'']
  ring

omit [IsDomain baseRing] [IsNoetherianRing baseRing] [Ring.KrullDimLE 1 baseRing] [IsFractionRing baseRing baseField] in

theorem latDist_map (linearMap : ambient →ₗ[baseField] targetSpace) (hφ : Function.Injective linearMap) (first otherFirst : Submodule baseRing ambient) :
    latDist (first.map (linearMap.restrictScalars baseRing)) (otherFirst.map (linearMap.restrictScalars baseRing)) = latDist first otherFirst := by
  unfold latDist
  have hφ' : Function.Injective (linearMap.restrictScalars baseRing) := hφ
  rw [← Submodule.map_inf _ hφ', relLength_map _ hφ', relLength_map _ hφ']

theorem latDist_map_indep (linearMap : ambient →ₗ[baseField] ambient) (hφ : Function.Bijective linearMap) (first otherFirst : Submodule baseRing ambient)
    [IsLattice baseField first] [IsLattice baseField otherFirst] :
    latDist first (first.map (linearMap.restrictScalars baseRing)) = latDist otherFirst (otherFirst.map (linearMap.restrictScalars baseRing)) := by
  have h1 : IsLattice baseField (first.map (linearMap.restrictScalars baseRing)) := IsLattice.map' linearMap hφ.2 first
  have h2 : IsLattice baseField (otherFirst.map (linearMap.restrictScalars baseRing)) := IsLattice.map' linearMap hφ.2 otherFirst
  rw [latDist_triangle (baseField := baseField) first otherFirst (first.map (linearMap.restrictScalars baseRing)),
    latDist_triangle (baseField := baseField) otherFirst (otherFirst.map (linearMap.restrictScalars baseRing)) (first.map (linearMap.restrictScalars baseRing)),
    latDist_map linearMap hφ.1 otherFirst first, latDist_comm otherFirst first]
  ring

theorem latDist_map_comp (linearMap secondMap : ambient →ₗ[baseField] ambient) (hφ : Function.Bijective linearMap)
    (hψ : Function.Bijective secondMap) (first : Submodule baseRing ambient) [IsLattice baseField first] :
    latDist first (first.map ((linearMap ∘ₗ secondMap).restrictScalars baseRing)) =
      latDist first (first.map (linearMap.restrictScalars baseRing)) + latDist first (first.map (secondMap.restrictScalars baseRing)) := by
  have h1 : IsLattice baseField (first.map (linearMap.restrictScalars baseRing)) := IsLattice.map' linearMap hφ.2 first
  have h2 : IsLattice baseField (first.map (secondMap.restrictScalars baseRing)) := IsLattice.map' secondMap hψ.2 first
  have h3 : IsLattice baseField (first.map ((linearMap ∘ₗ secondMap).restrictScalars baseRing)) :=
    IsLattice.map' (linearMap ∘ₗ secondMap) (hφ.2.comp hψ.2) first
  have hcomp : first.map ((linearMap ∘ₗ secondMap).restrictScalars baseRing) =
      (first.map (secondMap.restrictScalars baseRing)).map (linearMap.restrictScalars baseRing) := by
    rw [← Submodule.map_comp]; rfl
  rw [latDist_triangle (baseField := baseField) first (first.map (linearMap.restrictScalars baseRing)) _, hcomp,
    latDist_map linearMap hφ.1 first (first.map (secondMap.restrictScalars baseRing))]

end Submodule

end
