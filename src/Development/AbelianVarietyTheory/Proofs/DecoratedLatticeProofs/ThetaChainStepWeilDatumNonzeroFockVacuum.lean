module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.ChainOnto.StepExp

variable {D : D7}

theorem chrStep_exp' {c : Com D} (hc : c.Is) (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (c.chS ((k : ℕ) + 1)) τ (expS D k τ) ∧ HasInfExp D (c.chT ((k : ℕ) + 1)) τ (expT D k τ) := by
  have h1 : HasInfExp D (c.μ ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := hc.exp k τ
  have h2 : HasInfExp D c.η τ (1 / 2) := hc.chars.2.2.2.1 τ
  have h3 := GlobalTheory.Chain.StepVac.hasInfExp_mul h1 (GlobalTheory.Chain.StepVac.hasInfExp_inv h2)
  unfold Com.chS Com.chT Lift.chrStep expS expT
  by_cases hk : Even (k : ℕ)
  · rw [ite_eq_left hk.add_one, ite_eq_left hk, ite_eq_left hk, sub_zero, sub_eq_add_neg]
    exact ⟨h3, h1⟩
  · rw [ite_eq_right (by rwa [Nat.odd_add_one, Nat.not_odd_iff_even]), ite_eq_right hk, ite_eq_right hk, sub_zero, sub_eq_add_neg]
    exact ⟨h1, h3⟩

theorem stepExpVac : ∀ D : D7, GlobalTheory.ChainOnto.ForStep D fun c k s s' p => ∀ hk : k < D.R.m,
    IsWeilExp c.ψ s.V s'.V (expS D ⟨k, hk⟩) (expT D ⟨k, hk⟩) p.ω ∧ IsVacVec c.ψ c.θ s.M s'.M p.f := by
  intro D _ c hc k _ s s' hs hs' p hp hk
  refine ⟨⟨c.chS (k + 1), c.chT (k + 1), hp.weil, fun τ => chrStep_exp' hc ⟨k, hk⟩ τ⟩, ?_⟩
  obtain ⟨ξ, f₀, hv⟩ := hp.vec
  have hr : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  obtain ⟨a, b, d⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hs.selfDual hs'.selfDual hr hv
  exact ⟨a, b, d⟩

end GlobalTheory.ChainOnto.StepExp

end
