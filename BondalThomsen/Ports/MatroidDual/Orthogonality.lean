module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Tactic

@[expose] public section

open Set Submodule Matrix Module

namespace Matrix

variable {Field Coordinate : Type*} [_root_.Field Field] [Fintype Coordinate]

noncomputable def coordinateDotForm (Field Coordinate : Type*) [_root_.Field Field]
    [Fintype Coordinate] : LinearMap.BilinForm Field (Coordinate → Field) :=
  dotProductBilin Field Field

theorem coordinateDotForm_refl : (coordinateDotForm Field Coordinate).IsRefl := by
  intro first second orthogonal
  change dotProduct second first = 0
  change dotProduct first second = 0 at orthogonal
  rwa [dotProduct_comm]

theorem coordinateDotForm_nondegenerate : (coordinateDotForm Field Coordinate).Nondegenerate := by
  classical
  constructor
  · intro vector vanishes
    ext coordinate
    have zero := vanishes (Pi.single coordinate 1)
    simpa [coordinateDotForm, dotProductBilin] using zero
  · intro vector vanishes
    ext coordinate
    have zero := vanishes (Pi.single coordinate 1)
    simpa [coordinateDotForm, dotProductBilin] using zero

end Matrix

namespace Submodule

variable {Field Coordinate : Type*} [_root_.Field Field] [Fintype Coordinate]
    {first second : Submodule Field (Coordinate → Field)}

noncomputable def orthSpace (space : Submodule Field (Coordinate → Field)) :
    Submodule Field (Coordinate → Field) :=
  (Matrix.coordinateDotForm Field Coordinate).orthogonal space

theorem mem_orthSpace_iff {space : Submodule Field (Coordinate → Field)}
    {vector : Coordinate → Field} :
    vector ∈ space.orthSpace ↔ ∀ other ∈ space, dotProduct vector other = 0 := by
  rw [orthSpace, LinearMap.BilinForm.mem_orthogonal_iff]
  change (∀ other ∈ space, dotProduct other vector = 0) ↔
    ∀ other ∈ space, dotProduct vector other = 0
  simp only [dotProduct_comm]

theorem orthSpace_orthSpace (space : Submodule Field (Coordinate → Field)) :
    space.orthSpace.orthSpace = space :=
  LinearMap.BilinForm.orthogonal_orthogonal Matrix.coordinateDotForm_nondegenerate
    Matrix.coordinateDotForm_refl space

theorem eq_orthSpace_comm : first = second.orthSpace ↔ second = first.orthSpace := by
  constructor <;> intro equality <;> rw [equality, orthSpace_orthSpace]

theorem orthSpace_bot : (⊥ : Submodule Field (Coordinate → Field)).orthSpace = ⊤ := by
  apply top_unique
  intro vector member
  apply mem_orthSpace_iff.mpr
  intro other other_member
  have zero : other = 0 := other_member
  simp [zero]

theorem orthSpace_top : (⊤ : Submodule Field (Coordinate → Field)).orthSpace = ⊥ := by
  have double := orthSpace_orthSpace (⊥ : Submodule Field (Coordinate → Field))
  rwa [orthSpace_bot] at double

end Submodule
