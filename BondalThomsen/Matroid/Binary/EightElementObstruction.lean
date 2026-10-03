module

public import BondalThomsen.Matroid.Binary.SevenElementCoverage
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

namespace BondalThomsen

open Set Matrix

def binaryFourQuotientMatrix (pivot : Fin 4 → ZMod 2) (coordinate : Fin 4) :
    Matrix (Fin 3) (Fin 4) (ZMod 2) := fun row column =>
  (if column = coordinate.succAbove row then 1 else 0) +
    (if column = coordinate then pivot (coordinate.succAbove row) else 0)

def binaryFourQuotient (pivot : Fin 4 → ZMod 2) (coordinate : Fin 4) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  Matrix.toLin' (binaryFourQuotientMatrix pivot coordinate)

def binaryFourBasisPoint (coordinate : Fin 4) : Fin 4 → ZMod 2 :=
  fun index => if index = coordinate then 1 else 0

def binaryFourNonbasisPoint (index : Fin 11) : Fin 4 → ZMod 2 :=
  (![![1, 1, 0, 0], ![1, 0, 1, 0], ![1, 0, 0, 1],
    ![0, 1, 1, 0], ![0, 1, 0, 1], ![0, 0, 1, 1],
    ![1, 1, 1, 0], ![1, 1, 0, 1], ![1, 0, 1, 1],
    ![0, 1, 1, 1], ![1, 1, 1, 1]] : Fin 11 → Fin 4 → ZMod 2) index

def binaryFourNormalizedPoints (selected : Finset (Fin 11)) :
    Finset (Fin 4 → ZMod 2) :=
  Finset.univ.image binaryFourBasisPoint ∪ selected.image binaryFourNonbasisPoint

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem eight_normalized_binary_points_quotient_test :
    ∀ selected : Finset (Fin 11), selected.card = 4 →
      ∃ pivot ∈ binaryFourNormalizedPoints selected, ∃ coordinate : Fin 4,
        pivot coordinate = 1 ∧
        6 ≤ (((binaryFourNormalizedPoints selected).erase pivot).image
          (binaryFourQuotient pivot coordinate)).card := by
  decide +kernel

end BondalThomsen
