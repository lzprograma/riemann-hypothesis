module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
noncomputable section

namespace GlobalTheory.TiltUnique

theorem tilt_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {j : ℕ} (_ : j < D.R.m)
    (δ δ' : GA D (G.V (.grid D.R.m j))), IsTilt G j δ → IsTilt G j δ' → δ = δ' := by
  intro D T L sc G j hj δ δ' h h'
  rcases Nat.even_or_odd j with he | ho
  · rw [h.2.1 he, h'.2.1 he]
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := ho
    have h₂ : D.R.m - 1 - j = 2 * ((D.R.m - 1 - j) / 2) := by omega
    obtain ⟨x1, x2, x3⟩ := h.2.2 _ hj h₂
    obtain ⟨y1, y2, y3⟩ := h'.2.2 _ hj h₂
    have k := (rowJac G j hj _ h₂).sum_eq_one
    have e0 : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).j0 = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).j0 := x1.trans y1.symm
    have eX : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jX = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jX := x2.trans y2.symm
    have eY : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jY = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jY := x3.trans y3.symm
    have hm : mt _ δ = mt _ δ' := by
      rw [← Matrix.mul_one (mt _ δ), ← Matrix.mul_one (mt _ δ')]
      rw [← k]
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, e0, eX, eY]
    exact Subtype.ext (Units.ext hm)

end GlobalTheory.TiltUnique
