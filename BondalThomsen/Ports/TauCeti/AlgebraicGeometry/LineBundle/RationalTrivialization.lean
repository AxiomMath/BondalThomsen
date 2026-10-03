module

public import BondalThomsen.Ports.TauCeti.AlgebraicGeometry.LineBundle.Basic
public import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section

open AlgebraicGeometry CategoryTheory Set TopologicalSpace

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

theorem exists_dense_open_trivialization {X : Scheme.{u}} [IrreducibleSpace X]
    (M : X.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M] :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ Dense (U : Set X) ∧
      Nonempty
        (_root_.SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) := by
  let t := SheafOfModules.LocalTrivializations.ofIsInvertible M
  have hcover : ⨆ i, t.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (X : Type u) t.X).mp t.coversTop
  have hgeneric : genericPoint X ∈ ⨆ i, t.X i := by
    rw [hcover]
    exact Opens.mem_top _
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hgeneric
  refine ⟨t.X i, hi, (t.X i).isOpen.dense ⟨genericPoint X, hi⟩, ⟨t.iso i⟩⟩

end SheafOfModules

end

end TauCeti
