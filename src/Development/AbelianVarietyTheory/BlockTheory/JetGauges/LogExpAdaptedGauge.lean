module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

@[expose] public section

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge

section Chart

variable {k : Type} [CommRing k] {d : ℕ}

def linMap (U : Matrix (Fin d) (Fin d) k) : Pt k 1 d :=
  fun i => ∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)

end Chart

end GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge
