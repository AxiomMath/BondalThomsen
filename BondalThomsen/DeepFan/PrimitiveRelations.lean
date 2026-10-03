module

public import BondalThomsen.Fan.PrimitiveCollectionBoundary

@[expose] public section

open Finset Module Classical

namespace TauCeti.Toric.Fan

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [AddCommGroup Ambient]
    [Module ℝ Ambient] {embedding : Lattice →+ Ambient}

structure PrimitiveLatticeRelation (fan : TauCeti.Toric.Fan embedding)
    (left right : Finset fan.Ray) where
  primitive_collection : fan.IsPrimitiveCollection left
  disjoint : Disjoint left right
  coefficients : right → ℕ
  positive : ∀ ray, 0 < coefficients ray
  right_cone : fan.finiteRayHull right ∈ fan.cones
  lattice_eq : (∑ ray : left, ray.val.val) =
    ∑ ray : right, (coefficients ray : ℤ) • ray.val.val

structure PrimitiveRelationConeBasis {fan : TauCeti.Toric.Fan embedding}
    {left right : Finset fan.Ray} (relation : PrimitiveLatticeRelation fan left right)
    (distinguished : left) (dimension : ℕ) where
  basis : Basis (Fin dimension) ℤ Lattice
  cone_basis : fan.IsConeBasis basis
  indices : {ray : left // ray ≠ distinguished} ⊕ right ↪ Fin dimension
  left_eq : ∀ ray : {ray : left // ray ≠ distinguished},
    basis (indices (Sum.inl ray)) = ray.val.val.val
  right_eq : ∀ ray : right, basis (indices (Sum.inr ray)) = ray.val.val

theorem PrimitiveRelationConeBasis.distinguished_eq
    {fan : TauCeti.Toric.Fan embedding} {left right : Finset fan.Ray}
    {relation : PrimitiveLatticeRelation fan left right} {distinguished : left}
    {dimension : ℕ} (cone_basis : PrimitiveRelationConeBasis relation distinguished dimension) :
    distinguished.val.val =
      (∑ ray : right, (relation.coefficients ray : ℤ) •
        cone_basis.basis (cone_basis.indices (Sum.inr ray))) -
          ∑ ray : {ray : left // ray ≠ distinguished},
            cone_basis.basis (cone_basis.indices (Sum.inl ray)) := by
  classical
  simp only [cone_basis.left_eq, cone_basis.right_eq]
  have relation_eq := relation.lattice_eq
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun ray : left => ray.val.val) distinguished] at relation_eq
  exact eq_sub_iff_add_eq.mpr relation_eq

end TauCeti.Toric.Fan
