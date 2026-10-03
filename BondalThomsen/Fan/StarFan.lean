module

public import BondalThomsen.Fan.StarLattice
public import BondalThomsen.Fan.ConeRayQuotient
public import BondalThomsen.Fan.RegularBasisCone

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] {embedding : Lattice →+ Ambient}

theorem ray_isFaceOf_of_mem (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (member : cone ∈ fan.cones)
    (contains : embedding ray.val ∈ cone) :
    (PointedCone.hull ℝ {embedding ray.val}).IsFaceOf cone := by
  apply fan.isFaceOf_of_le member ray.property.2
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr contains)

theorem starCone_isToricCone (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray)
    (cone : PointedCone ℝ Ambient) (member : cone ∈ fan.cones)
    (contains : embedding ray.val ∈ cone) :
    TauCeti.Toric.IsToricCone (fan.starEmbedding ray)
      (PointedCone.map (fan.starProjection ray) cone) := by
  classical
  refine ⟨?_, rayQuotient_map_salient _ _ (fan.ray_isFaceOf_of_mem ray cone member contains)⟩
  obtain ⟨generators, cone_eq⟩ := (fan.isToricCone member).rational
  refine ⟨generators.image (Submodule.span ℤ {ray.val}).mkQ, ?_⟩
  rw [cone_eq, pointedCone_map_hull, Finset.coe_image, Set.image_image]
  apply congrArg (PointedCone.hull ℝ)
  ext point
  constructor
  · rintro ⟨lattice_vector, selected, rfl⟩
    exact ⟨(Submodule.span ℤ {ray.val}).mkQ lattice_vector,
      ⟨lattice_vector, selected, rfl⟩,
      (fan.starEmbedding_mkQ ray lattice_vector).symm⟩
  · rintro ⟨original, ⟨lattice_vector, selected, rfl⟩, rfl⟩
    exact ⟨lattice_vector, selected, fan.starEmbedding_mkQ ray lattice_vector⟩

theorem starCones_mem_of_isFaceOf (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray)
    {cone face : PointedCone ℝ (fan.StarAmbient ray)}
    (member : cone ∈ fan.starCones ray) (is_face : face.IsFaceOf cone) :
    face ∈ fan.starCones ray := by
  obtain ⟨original, ⟨original_member, contains⟩, rfl⟩ := member
  obtain ⟨lifted, lifted_face, lifted_contains, equality⟩ :=
    rayQuotient_face_lift (embedding ray.val) original contains face is_face
  exact ⟨lifted, ⟨fan.mem_of_isFaceOf original_member lifted_face, lifted_contains⟩, equality⟩

theorem starCones_inf_isFaceOf_left (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray)
    {first second : PointedCone ℝ (fan.StarAmbient ray)}
    (first_member : first ∈ fan.starCones ray) (second_member : second ∈ fan.starCones ray) :
    (first ⊓ second).IsFaceOf first := by
  obtain ⟨original_first, ⟨first_member, first_contains⟩, rfl⟩ := first_member
  obtain ⟨original_second, ⟨second_member, second_contains⟩, rfl⟩ := second_member
  change (PointedCone.map (Submodule.span ℝ {embedding ray.val}).mkQ original_first ⊓
    PointedCone.map (Submodule.span ℝ {embedding ray.val}).mkQ original_second).IsFaceOf _
  rw [← rayQuotient_map_inf _ _ _ first_contains second_contains]
  exact rayQuotient_map_isFaceOf _ (fan.inf_isFaceOf_left first_member second_member)
    ⟨first_contains, second_contains⟩

noncomputable def star (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    TauCeti.Toric.Fan (fan.starEmbedding ray) where
  lattice := fan.starEmbedding_isIntegralLattice_of_primitive ray
  cones := fan.starCones ray
  finite_cones := fan.starCones_finite ray
  isToricCone := by
    rintro _ ⟨original, ⟨member, contains⟩, rfl⟩
    exact fan.starCone_isToricCone ray original member contains
  mem_of_isFaceOf := by
    intro cone face member is_face
    exact fan.starCones_mem_of_isFaceOf ray member is_face
  inf_isFaceOf_left := by
    intro first second first_member second_member
    exact fan.starCones_inf_isFaceOf_left ray first_member second_member

@[simp] theorem star_cones (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    (fan.star ray).cones = fan.starCones ray := rfl

theorem star_isComplete [FiniteDimensional ℝ Ambient] (fan : TauCeti.Toric.Fan embedding)
    {dimension : ℕ} (complete : fan.IsComplete) (regular : fan.IsRegular)
    (deep : fan.IsDeep dimension) (reference : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) : (fan.star ray).IsComplete := by
  rw [TauCeti.Toric.Fan.isComplete_iff]
  intro point
  exact fan.starCones_cover complete regular deep reference ray point

theorem starConeBasis_isRegular (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice)
    (ray : fan.Ray) (removed : Fin dimension) (equality : basis removed = ray.val)
    (cone_basis : fan.IsConeBasis basis) :
    TauCeti.Toric.IsRegularCone (fan.starEmbedding ray)
      (PointedCone.map (fan.starProjection ray)
        (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))))) := by
  let real_basis := fan.lattice.isBaseChange.basis basis
  have real_equality : real_basis removed = embedding ray.val := by
    rw [fan.lattice.isBaseChange.basis_apply, equality]
    rfl
  have real_range : Set.range (fun index => embedding (basis index)) = Set.range real_basis := by
    apply congrArg Set.range
    funext index
    exact (fan.lattice.isBaseChange.basis_apply basis index).symm
  have contains : embedding ray.val ∈
      PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) := by
    rw [← equality]
    exact PointedCone.subset_hull ⟨removed, rfl⟩
  apply TauCeti.Toric.isRegularCone_of_basisHull (fan.star ray).lattice
    (basisVectorQuotient basis removed ray.val equality) _
    (fan.starCone_isToricCone ray _ cone_basis contains)
  change PointedCone.map (Submodule.span ℝ {embedding ray.val}).mkQ
    (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) = _
  rw [real_range, basisVectorQuotient_cone real_basis removed (embedding ray.val) real_equality]
  apply congrArg (PointedCone.hull ℝ)
  apply congrArg Set.range
  funext index
  simp only [basisVectorQuotient_apply, starEmbedding_mkQ]
  change (Submodule.span ℝ {embedding ray.val}).mkQ (real_basis index.val) =
    (Submodule.span ℝ {embedding ray.val}).mkQ (embedding (basis index.val))
  rw [fan.lattice.isBaseChange.basis_apply]
  rfl

theorem starConeBasis_eq_hull (fan : TauCeti.Toric.Fan embedding) {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (ray : fan.Ray)
    (removed : Fin dimension) (equality : basis removed = ray.val) :
    PointedCone.map (fan.starProjection ray)
      (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) =
      PointedCone.hull ℝ (Set.range (fun index => fan.starEmbedding ray
        (basisVectorQuotient basis removed ray.val equality index))) := by
  let real_basis := fan.lattice.isBaseChange.basis basis
  have real_equality : real_basis removed = embedding ray.val := by
    rw [fan.lattice.isBaseChange.basis_apply, equality]
    rfl
  have real_range : Set.range (fun index => embedding (basis index)) = Set.range real_basis := by
    apply congrArg Set.range
    funext index
    exact (fan.lattice.isBaseChange.basis_apply basis index).symm
  change PointedCone.map (Submodule.span ℝ {embedding ray.val}).mkQ
    (PointedCone.hull ℝ (Set.range (fun index => embedding (basis index)))) = _
  rw [real_range, basisVectorQuotient_cone real_basis removed (embedding ray.val) real_equality]
  apply congrArg (PointedCone.hull ℝ)
  apply congrArg Set.range
  funext index
  simp only [basisVectorQuotient_apply, starEmbedding_mkQ]
  change (Submodule.span ℝ {embedding ray.val}).mkQ (real_basis index.val) =
    (Submodule.span ℝ {embedding ray.val}).mkQ (embedding (basis index.val))
  rw [fan.lattice.isBaseChange.basis_apply]
  rfl

theorem exists_coneBasis_above_containing_ray [FiniteDimensional ℝ Ambient]
    (fan : TauCeti.Toric.Fan embedding) (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ray : fan.Ray) (original : PointedCone ℝ Ambient) (original_member : original ∈ fan.cones)
    (contains : embedding ray.val ∈ original) :
    ∃ size : ℕ, ∃ basis : Basis (Fin size) ℤ Lattice, fan.IsConeBasis basis ∧
      ∃ removed : Fin size, basis removed = ray.val ∧
        original.IsFaceOf (PointedCone.hull ℝ
          (Set.range (fun index => embedding (basis index)))) := by
  obtain ⟨size, basis, cone_basis, original_face⟩ :=
    fan.exists_coneBasis_above complete regular original original_member
  obtain ⟨removed, equality⟩ := TauCeti.Toric.primitive_eq_basis_of_ray_face fan.lattice
    basis ray.val ray.property.1
    ((fan.ray_isFaceOf_of_mem ray original original_member contains).trans original_face)
    (fan.isToricCone cone_basis).salient
  exact ⟨size, basis, cone_basis, removed, equality.symm, original_face⟩

theorem star_isRegular [FiniteDimensional ℝ Ambient] (fan : TauCeti.Toric.Fan embedding)
    (complete : fan.IsComplete) (regular : fan.IsRegular)
    (ray : fan.Ray) : (fan.star ray).IsRegular := by
  intro cone member
  obtain ⟨original, ⟨original_member, contains⟩, rfl⟩ := member
  obtain ⟨size, basis, cone_basis, removed, equality, original_face⟩ :=
    fan.exists_coneBasis_above_containing_ray complete regular ray original original_member contains
  exact (fan.starConeBasis_isRegular basis ray removed equality cone_basis).of_isFaceOf
    (rayQuotient_map_isFaceOf _ original_face contains)

end TauCeti.Toric.Fan
