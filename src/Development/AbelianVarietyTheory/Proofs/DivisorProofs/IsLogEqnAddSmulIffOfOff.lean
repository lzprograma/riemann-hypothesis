module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

noncomputable section

namespace GlobalTheory.PairStep

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

theorem isLogEqn_add_smul_iff_of_off {p : X ⟶ Sp k} {n : ℕ} {Γ B : X → ℚ} (c : ℚ) {x : X}
    (hB : Off B x) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ) :
    IsLogEqn p (Γ + c • B) η x m g ↔ IsLogEqn p Γ η x m g := by
  refine forall_congr' fun z => forall_congr' fun hz => ?_
  have : (Γ + c • B) z = Γ z := by simp [hB z hz]
  rw [this]

theorem off_add_smul (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ)
    (n : ℕ) (Γ B : X → ℚ) (c : ℚ) (x : X) (hB : Off B x) :
    (KltAt p n (Γ + c • B) x ↔ KltAt p n Γ x) ∧ (LcAt p n (Γ + c • B) x ↔ LcAt p n Γ x) ∧
      (IsNkltCentre p n (Γ + c • B) x ↔ IsNkltCentre p n Γ x) ∧ ∀ z, z ⤳ x → Off B z := by
  have e := isLogEqn_add_smul_iff_of_off (p := p) (n := n) (Γ := Γ) c hB
  refine ⟨?_, ?_, ?_, fun z hz w hw => hB w (hw.trans hz)⟩
  · unfold KltAt
    simp only [e]
  · unfold LcAt
    simp only [e]
  · unfold IsNkltCentre
    simp only [e]

end GlobalTheory.PairStep
