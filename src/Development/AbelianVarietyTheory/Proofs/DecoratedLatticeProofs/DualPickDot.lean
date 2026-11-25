module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.FinPl.LineAct

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def iota (p : SplitPt D k) : D.host.E →+* k := p.pr.comp (incA D)

def dualPick {m : Type} [DecidableEq m] (g : m → k) : m → k := by
  classical
  exact if h : ∃ i, g i ≠ 0 then Pi.single h.choose (g h.choose)⁻¹ else 0

theorem dualPick_dot {m : Type} [Fintype m] [DecidableEq m] (g : m → k) (hg : g ≠ 0) : dualPick g ⬝ᵥ g = 1 := by
  classical
  have h : ∃ i, g i ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hg (funext h')
  unfold dualPick
  rw [dite_eq_left h]
  simp only [single_dotProduct]
  exact inv_mul_cancel₀ h.choose_spec

variable {n : Type} [Fintype n] [DecidableEq n]

def wRow (p : SplitPt D k) {W₀ L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (β : Frame p W₀ n) (t : n → k) : WO W₀ L' :=
  Matrix.of fun i j => p.sec (iota p (ζ' i) * (t ᵥ* β.b') j)

def wCol (p : SplitPt D k) {W₀ L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (β : Frame p W₀ n) (t : n → k) : WO W₀ L' :=
  Matrix.of fun i j => cA D (p.sec (dualPick ((L'.gram.map (iota p)) *ᵥ fun i => iota p (ζ' i)) i *
    ((iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) j)))

end GlobalTheory.FinPl.LineAct

end
