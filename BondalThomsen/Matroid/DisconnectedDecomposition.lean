module

public import BondalThomsen.Ports.Matroid.Connectedness
public import Mathlib.Data.Set.Card

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*}

inductive ConnectedDisjointSumDecomposition : Matroid Label → ℕ → Prop
  | empty (source : Matroid Label) (ground_empty : source.E = ∅) :
      ConnectedDisjointSumDecomposition source 0
  | connected (source : Matroid Label) (property : source.Connected) :
      ConnectedDisjointSumDecomposition source 1
  | sum {left right : Matroid Label} (disjoint : Disjoint left.E right.E)
      {left_count right_count : ℕ}
      (left_trace : ConnectedDisjointSumDecomposition left left_count)
      (right_trace : ConnectedDisjointSumDecomposition right right_count) :
      ConnectedDisjointSumDecomposition (left.disjointSum right disjoint)
        (left_count + right_count)

end Matroid
