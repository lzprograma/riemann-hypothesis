module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace PI.FglPhSplit

open Classical

def expMv {K : Type*} [Field K] {σ : Type*} (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : K)

structure Dat (K : Type*) [Field K] where
  l : PowerSeries K
  ex : PowerSeries K
  ph : PowerSeries K

end PI.FglPhSplit

end
