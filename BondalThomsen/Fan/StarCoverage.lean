module

public import BondalThomsen.DeepFan.Theorems
public import BondalThomsen.Fan.StarCoordinates

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen Filter
open scoped Topology

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

abbrev StarAmbient (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :=
  Ambient ⧸ Submodule.span ℝ {embedding ray.val}

def starProjection (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    Ambient →ₗ[ℝ] fan.StarAmbient ray :=
  (Submodule.span ℝ {embedding ray.val}).mkQ

def starCones (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    Set (PointedCone ℝ (fan.StarAmbient ray)) :=
  PointedCone.map (fan.starProjection ray) ''
    {cone : PointedCone ℝ Ambient | cone ∈ fan.cones ∧ embedding ray.val ∈ cone}

omit [FiniteDimensional ℝ Ambient] in

theorem starCones_finite (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    (fan.starCones ray).Finite :=
  (fan.finite_cones.subset (fun _ member => member.1)).image _

omit [FiniteDimensional ℝ Ambient] in

@[simp] theorem starProjection_ray (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    fan.starProjection ray (embedding ray.val) = 0 := by
  change (Submodule.span ℝ {embedding ray.val}).mkQ (embedding ray.val) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Set.mem_singleton _)

theorem exists_coneBasis_ray_perturbation (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) (point : Ambient) :
    ∃ basis : Basis (Fin dimension) ℤ Lattice, fan.IsConeBasis basis ∧
      ∃ removed : Fin dimension, basis removed = ray.val ∧
        ∃ scalar : ℝ, 0 < scalar ∧ embedding ray.val + scalar • point ∈
          PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) := by
  classical
  have nearby := (locallyFinite_of_finite
    (fun cone : fan.cones => (cone.val : Set Ambient))).eventually_subset
      (fun cone => fan.cone_isClosed cone.val cone.property) (embedding ray.val)
  let perturbation := fun scalar : ℝ => embedding ray.val + scalar • point
  have continuous_perturbation : Continuous perturbation :=
    continuous_const.add (continuous_id.smul continuous_const)
  have converges : Tendsto perturbation (𝓝 0) (𝓝 (embedding ray.val)) := by
    simpa only [perturbation, zero_smul, add_zero] using continuous_perturbation.tendsto 0
  obtain ⟨scalar, scalar_positive, local_member⟩ := (converges.eventually nearby).exists_gt
  obtain ⟨size, basis, cone_basis, contains⟩ :=
    fan.exists_coneBasis_containing complete regular (perturbation scalar)
  have size_eq : size = dimension := by
    have ranks := (finrank_eq_card_basis basis).symm.trans (finrank_eq_card_basis reference)
    simpa only [Fintype.card_fin] using ranks
  subst size
  let cone := PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))
  have ray_member : embedding ray.val ∈ cone :=
    local_member (show (⟨cone, cone_basis⟩ : fan.cones) ∈
      {cone : fan.cones | perturbation scalar ∈ cone.val} from contains)
  let real_basis := fan.lattice.isBaseChange.basis basis
  have generators_eq : Set.range (fun index => embedding (basis index)) =
      Set.range real_basis := by
    apply congrArg Set.range
    funext index
    exact (fan.lattice.isBaseChange.basis_apply basis index).symm
  have real_nonnegative : ∀ index, 0 ≤ real_basis.repr (embedding ray.val) index := by
    apply (mem_basisCone_iff real_basis _).mp
    rwa [← generators_eq]
  have nonnegative : ∀ index, 0 ≤ basis.repr ray.val index := by
    intro index
    have bound := real_nonnegative index
    change 0 ≤ real_basis.repr (embedding.toIntLinearMap ray.val) index at bound
    rw [fan.lattice.isBaseChange.basis_repr_comp_apply] at bound
    change 0 ≤ (basis.repr ray.val index : ℝ) at bound
    exact_mod_cast bound
  have nonzero : (fun index => basis.repr ray.val index) ≠ 0 := by
    intro zero
    apply ray.property.1.ne_zero
    apply basis.repr.injective
    ext index
    simpa using congrFun zero index
  obtain ⟨removed, coordinates⟩ :=
    (deep basis cone_basis ray).eq_basis_vector_of_nonnegative nonnegative nonzero
  have generator_eq : basis removed = ray.val := by
    apply basis.repr.injective
    ext index
    simpa [Basis.repr_self_apply, Finsupp.single_apply, eq_comm] using (coordinates index).symm
  exact ⟨basis, cone_basis, removed, generator_eq, scalar, scalar_positive, contains⟩

theorem starCones_cover (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (complete : fan.IsComplete) (regular : fan.IsRegular) (deep : fan.IsDeep dimension)
    (reference : Basis (Fin dimension) ℤ Lattice) (ray : fan.Ray)
    (point : fan.StarAmbient ray) :
    ∃ cone ∈ fan.starCones ray, point ∈ cone := by
  obtain ⟨lifted, lifted_eq⟩ := (Submodule.span ℝ {embedding ray.val}).mkQ_surjective point
  obtain ⟨basis, cone_basis, removed, generator_eq, scalar, positive, contains⟩ :=
    fan.exists_coneBasis_ray_perturbation complete regular deep reference ray lifted
  let cone := PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))
  have ray_member : embedding ray.val ∈ cone := by
    rw [← generator_eq]
    exact PointedCone.subset_hull ⟨removed, rfl⟩
  refine ⟨PointedCone.map (fan.starProjection ray) cone,
    ⟨cone, ⟨cone_basis, ray_member⟩, rfl⟩, ?_⟩
  have projected : scalar • point ∈ PointedCone.map (fan.starProjection ray) cone := by
    apply PointedCone.mem_map.mpr
    refine ⟨embedding ray.val + scalar • lifted, contains, ?_⟩
    simp only [map_add, map_smul, fan.starProjection_ray, zero_add]
    change scalar • ((Submodule.span ℝ {embedding ray.val}).mkQ lifted) = scalar • point
    rw [lifted_eq]
  have scaled := PointedCone.smul_mem _ (inv_pos.mpr positive).le projected
  simpa only [inv_smul_smul₀ positive.ne'] using scaled

end TauCeti.Toric.Fan
