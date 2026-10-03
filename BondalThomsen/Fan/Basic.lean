module

public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Regular
public import BondalThomsen.Ports.TauCeti.Geometry.Toric.Algebraic.Ray.Primitive
public import BondalThomsen.Ports.TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import BondalThomsen.Matroid.RayMatroid
public import BondalThomsen.DeepFan.Coordinates

@[expose] public section

open Set Module TauCeti.Toric BondalThomsen
open scoped TensorProduct

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

namespace TauCeti.Toric.Fan

variable (fan : TauCeti.Toric.Fan embedding)

def Ray := {vector : Lattice // TauCeti.IsPrimitive vector ∧
  PointedCone.hull ℝ {embedding vector} ∈ fan.cones}

theorem ray_hull_injective : Function.Injective
    (fun ray : fan.Ray => PointedCone.hull ℝ {embedding ray.val}) := by
  intro first second equality
  have image_nonzero : embedding first.val ≠ 0 := by
    simpa only [map_zero] using fan.lattice.injective.ne first.property.1.ne_zero
  let ray := ToricRay.hullSingleton image_nonzero
  have first_generator : IsPrimitiveGenerator embedding ray first.val :=
    ⟨PointedCone.subset_hull (Set.mem_singleton _), first.property.1⟩
  have second_generator : IsPrimitiveGenerator embedding ray second.val := by
    refine ⟨?_, second.property.1⟩
    exact Eq.mpr (congrArg (fun cone : PointedCone ℝ Ambient =>
      embedding second.val ∈ cone) equality)
      (PointedCone.subset_hull (Set.mem_singleton _))
  exact Subtype.ext (first_generator.unique fan.lattice
    (fan.isToricCone first.property.2).salient second_generator)

instance finiteRay : Finite fan.Ray :=
  Finite.of_injective
    (fun ray : fan.Ray =>
      (⟨PointedCone.hull ℝ {embedding ray.val}, ray.property.2⟩ : fan.cones))
    (fun _ _ equality => fan.ray_hull_injective (congrArg Subtype.val equality))

noncomputable def rayMatroid : Matroid fan.Ray :=
  BondalThomsen.rayMatroid (Field := ℚ)
    (fun ray : fan.Ray => (1 : ℚ) ⊗ₜ[ℤ] (ray.val : Lattice))

@[simp] theorem rayMatroid_indep_iff (rays : Set fan.Ray) :
    fan.rayMatroid.Indep rays ↔
      LinearIndepOn ℚ (fun ray : fan.Ray => (1 : ℚ) ⊗ₜ[ℤ] (ray.val : Lattice)) rays :=
  BondalThomsen.rayMatroid_indep_iff _ _

def IsConeBasis {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice) : Prop :=
  PointedCone.hull ℝ (Set.range (fun index => embedding (basis index))) ∈ fan.cones

def IsDeep (dimension : ℕ) : Prop :=
  ∀ basis : Basis (Fin dimension) ℤ Lattice, fan.IsConeBasis basis →
    ∀ ray : fan.Ray, DeepCoordinates (fun index => basis.repr ray.val index)

noncomputable def basisRay {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (index : Fin dimension) : fan.Ray := by
  refine ⟨basis index, basis.isPrimitive index, ?_⟩
  have independent : LinearIndependent ℝ (fun index => embedding (basis index)) := by
    convert (fan.lattice.isBaseChange.basis basis).linearIndependent using 1
    funext index
    exact (fan.lattice.isBaseChange.basis_apply basis index).symm
  have face := PointedCone.isFaceOf_hull_image independent rfl {index}
  exact fan.mem_of_isFaceOf cone_basis (by simpa using face)

@[simp] theorem basisRay_val {dimension : ℕ} (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (index : Fin dimension) :
    (fan.basisRay basis cone_basis index).val = basis index := rfl

@[simp] theorem basisRay_coordinates {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (row column : Fin dimension) :
    basis.repr (fan.basisRay basis cone_basis column).val row =
      if row = column then 1 else 0 := by
  classical
  simp [Finsupp.single_apply, eq_comm]

noncomputable def supportingCharacter {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) : Lattice →+ ℤ :=
  (basis.constr ℤ (fun _ => (1 : ℤ))).toAddMonoidHom

noncomputable def supportingFunctional {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) : Ambient →ₗ[ℝ] ℝ :=
  fan.lattice.realCharacter (supportingCharacter basis)

@[simp] theorem supportingFunctional_basis {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (index : Fin dimension) :
    fan.supportingFunctional basis (embedding (basis index)) = 1 := by
  simp [supportingFunctional, supportingCharacter]

theorem supportingFunctional_lattice {dimension : ℕ}
    (basis : Basis (Fin dimension) ℤ Lattice) (vector : Lattice) :
    fan.supportingFunctional basis (embedding vector) =
      ((∑ index, basis.repr vector index : ℤ) : ℝ) := by
  simp [supportingFunctional, supportingCharacter, Basis.constr_apply_fintype,
    Basis.equivFun_apply]

theorem supportingFunctional_ray_le_one {dimension : ℕ}
    (deep : fan.IsDeep dimension) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (ray : fan.Ray) :
    fan.supportingFunctional basis (embedding ray.val) ≤ 1 := by
  rw [supportingFunctional_lattice]
  exact_mod_cast (deep basis cone_basis ray).sum_le_one

theorem supportingFunctional_ray_eq_one_iff {dimension : ℕ}
    (deep : fan.IsDeep dimension) (basis : Basis (Fin dimension) ℤ Lattice)
    (cone_basis : fan.IsConeBasis basis) (ray : fan.Ray) :
    fan.supportingFunctional basis (embedding ray.val) = 1 ↔
      ∃ index, ray.val = basis index := by
  constructor
  · intro equality
    rw [supportingFunctional_lattice] at equality
    have integer_equality : ∑ index, basis.repr ray.val index = 1 := by
      exact_mod_cast equality
    obtain ⟨chosen, coordinates⟩ :=
      (deep basis cone_basis ray).eq_basis_vector_of_sum_eq_one integer_equality
    refine ⟨chosen, basis.repr.injective ?_⟩
    ext index
    simpa [Basis.repr_self_apply, Finsupp.single_apply, eq_comm] using coordinates index
  · rintro ⟨index, equality⟩
    rw [equality, supportingFunctional_basis]

theorem deep_ray_coordinate_trichotomy {dimension : ℕ}
    (deep : fan.IsDeep dimension)
    (adjacency : ∀ basis : Basis (Fin dimension) ℤ Lattice,
      fan.IsConeBasis basis → ∀ index, ∃ adjacent : Basis (Fin dimension) ℤ Lattice,
        fan.IsConeBasis adjacent ∧ ∀ vector : Lattice,
          adjacent.repr vector index = -basis.repr vector index)
    (basis : Basis (Fin dimension) ℤ Lattice) (cone_basis : fan.IsConeBasis basis)
    (ray : fan.Ray) (index : Fin dimension) :
    basis.repr ray.val index = -1 ∨ basis.repr ray.val index = 0 ∨
      basis.repr ray.val index = 1 := by
  obtain ⟨adjacent, adjacent_cone, sign⟩ := adjacency basis cone_basis index
  exact deep_coordinate_trichotomy (deep basis cone_basis ray)
    (deep adjacent adjacent_cone ray) index (sign ray.val)

end TauCeti.Toric.Fan
