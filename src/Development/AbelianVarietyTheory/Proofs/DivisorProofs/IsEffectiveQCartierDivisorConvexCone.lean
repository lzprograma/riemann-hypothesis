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
import Mathlib.Tactic.Basify
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
namespace GlobalTheory.QCartCone

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem mult_zero' (z : X) : (0 : CartierDiv X).mult z = 0 := by
  have := CartierDiv.mult_add (0 : CartierDiv X) 0 z
  rw [add_zero] at this
  omega

theorem mult_nsmul' (D : CartierDiv X) (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero']; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul' {D : CartierDiv X} (h : D.Eff) (n : ℕ) : (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem isQCart_cone : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (D B : X → ℚ) (c : ℚ),
    IsQCart D → IsQCart B → 0 ≤ c → IsQCart (D + B) ∧ IsQCart (c • D) ∧ IsQCart (0 : X → ℚ) := by
  intro X _ _ D B c hD hB hc
  obtain ⟨m, D₀, hm, hD₀, rfl⟩ := hD
  obtain ⟨n, B₀, hn, hB₀, rfl⟩ := hB
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨m * n, n • D₀ + m • B₀, Nat.mul_pos hm hn, (eff_nsmul' hD₀ n).add (eff_nsmul' hB₀ m), ?_⟩,
    ⟨c.den * m, c.num.toNat • D₀, Nat.mul_pos c.den_pos hm, eff_nsmul' hD₀ _, ?_⟩,
    ⟨1, 0, one_pos, CartierDiv.eff_zero, ?_⟩⟩
  · funext z
    simp only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul']
    push_cast
    field_simp
  · funext z
    have hnum : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by
      have h1 : ((c.num.toNat : ℤ) : ℚ) = (c.num : ℚ) := by
        rw [Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)]
      exact_mod_cast h1
    have hden : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
    simp only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul']
    push_cast
    rw [hnum]
    conv_lhs => rw [← Rat.num_div_den c]
    field_simp
  · funext z
    simp [qWeil, mult_zero']

end GlobalTheory.QCartCone
