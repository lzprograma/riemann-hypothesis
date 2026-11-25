module

public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open Classical

namespace Formalism.BasicNotions

def JetTdeg {σ : Type*} (m : σ →₀ ℕ) : ℕ := m.sum (fun _ k => k)

def jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} (v : ZMod d × β) : MvPowerSeries (ZMod d × β) ℂ_[l] :=
  fun m => ∑ e ∈ Finset.range (JetTdeg m + 1),
    if m = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((l ^ 2) ^ e) then (((l : ℂ_[l]) ^ e)⁻¹) else 0

structure JetLoc where

  l : ℕ
  [hl : Fact l.Prime]

  five_le_l : 5 ≤ l

  d : ℕ
  [hd : NeZero d]
  d_even : Even d
  two_le_d : 2 ≤ d

  N0 : ℕ
  N1 : ℕ

  Th : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]

attribute [instance] JetLoc.hl JetLoc.hd

structure JetLoc1 where
  l : ℕ
  [hl : Fact l.Prime]

  five_le_l : 5 ≤ l
  N0 : ℕ
  N1 : ℕ

  Th : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[l]

attribute [instance] JetLoc1.hl

structure ThetaJet (R : Ranks) (_host : Host R) : Type 1 where
  Sit : Type
  loc : Sit → JetLoc
  jOf : Sit → ℕ
  Sit1 : Type
  loc1 : Sit1 → JetLoc1
  j1Of : Sit1 → ℕ

end Formalism.BasicNotions

end
