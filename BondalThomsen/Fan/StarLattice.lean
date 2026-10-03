module

public import BondalThomsen.Fan.StarCoverage
public import BondalThomsen.Fan.QuotientBasis

@[expose] public section

namespace TauCeti.Toric.Fan

open Set Module BondalThomsen

variable {Lattice Ambient : Type*} [AddCommGroup Lattice] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient] [FiniteDimensional ℝ Ambient] {embedding : Lattice →+ Ambient}

abbrev StarLattice (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :=
  Lattice ⧸ Submodule.span ℤ {ray.val}

omit [FiniteDimensional ℝ Ambient] in

def starEmbedding (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray) :
    fan.StarLattice ray →+ fan.StarAmbient ray :=
  ((Submodule.span ℤ {ray.val}).liftQ
    (((fan.starProjection ray).restrictScalars ℤ).comp embedding.toIntLinearMap)
    (Submodule.span_le.mpr (by
      intro vector member
      rcases Set.mem_singleton_iff.mp member with rfl
      change fan.starProjection ray (embedding ray.val) = 0
      exact fan.starProjection_ray ray))).toAddMonoidHom

omit [FiniteDimensional ℝ Ambient] in

@[simp] theorem starEmbedding_mkQ (fan : TauCeti.Toric.Fan embedding) (ray : fan.Ray)
    (vector : Lattice) :
    fan.starEmbedding ray ((Submodule.span ℤ {ray.val}).mkQ vector) =
      fan.starProjection ray (embedding vector) := by
  rfl

omit [FiniteDimensional ℝ Ambient] in

theorem starEmbedding_isIntegralLattice_of_basis (fan : TauCeti.Toric.Fan embedding)
    {Index : Type*} [Finite Index] [DecidableEq Index] (basis : Basis Index ℤ Lattice)
    (removed : Index) (ray : fan.Ray) (equality : basis removed = ray.val) :
    TauCeti.Toric.IsIntegralLattice (fan.starEmbedding ray) := by
  let real_basis := fan.lattice.isBaseChange.basis basis
  have real_equality : real_basis removed = embedding ray.val := by
    rw [fan.lattice.isBaseChange.basis_apply, equality]
    rfl
  apply TauCeti.Toric.isIntegralLattice_of_basis
    (basisVectorQuotient basis removed ray.val equality)
    (basisVectorQuotient real_basis removed (embedding ray.val) real_equality)
  intro index
  simp only [basisVectorQuotient_apply, starEmbedding_mkQ]
  change (Submodule.span ℝ {embedding ray.val}).mkQ (embedding (basis index.val)) =
    (Submodule.span ℝ {embedding ray.val}).mkQ (real_basis index.val)
  rw [fan.lattice.isBaseChange.basis_apply]
  rfl

omit [FiniteDimensional ℝ Ambient] in

theorem starEmbedding_isIntegralLattice_of_primitive (fan : TauCeti.Toric.Fan embedding)
    (ray : fan.Ray) : TauCeti.Toric.IsIntegralLattice (fan.starEmbedding ray) := by
  let := fan.lattice.free
  let := fan.lattice.finite
  obtain ⟨size, basis, removed, equality⟩ := ray.property.1.exists_basis
  exact fan.starEmbedding_isIntegralLattice_of_basis basis removed ray equality

end TauCeti.Toric.Fan
