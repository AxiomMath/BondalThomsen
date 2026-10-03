module

public import BondalThomsen.Matroid.Binary.RankThreeCoverage
public import BondalThomsen.Matroid.Binary.MarkedLeafReduction

@[expose] public section

namespace Matroid

open Set

variable {Label : Type*} {source : Matroid Label} {marked : Label}

inductive MarkedConnectedReductionTrace (marked : Label) :
    Matroid Label → Matroid Label → ℕ → Prop
  | nil (source : Matroid Label) (connected : source.Connected)
      (nonloop : source.IsNonloop marked) (not_coloop : ¬source.IsColoop marked) :
      MarkedConnectedReductionTrace marked source source 0
  | cons {source intermediate target : Matroid Label} {length : ℕ}
      (connected : source.Connected) (nonloop : source.IsNonloop marked)
      (not_coloop : ¬source.IsColoop marked)
      (reduction : ElementarySeriesParallelReduction source intermediate)
      (remaining : MarkedConnectedReductionTrace marked intermediate target length) :
      MarkedConnectedReductionTrace marked source target (length + 1)

theorem MarkedConnectedReductionTrace.toSeriesParallelReductionTrace
    {target : Matroid Label} {length : ℕ}
    (trace : MarkedConnectedReductionTrace marked source target length) :
    SeriesParallelReductionTrace source target length := by
  induction trace with
  | nil source connected nonloop not_coloop => exact .nil source
  | cons connected nonloop not_coloop reduction remaining induction =>
    exact .cons reduction induction

theorem MarkedConnectedReductionTrace.isMinor
    {target : Matroid Label} {length : ℕ}
    (trace : MarkedConnectedReductionTrace marked source target length) : target ≤m source :=
  trace.toSeriesParallelReductionTrace.isMinor

theorem MarkedConnectedReductionTrace.ground_ncard [source.Finite]
    {target : Matroid Label} {length : ℕ}
    (trace : MarkedConnectedReductionTrace marked source target length) :
    length + target.E.ncard = source.E.ncard :=
  trace.toSeriesParallelReductionTrace.ground_ncard

end Matroid
