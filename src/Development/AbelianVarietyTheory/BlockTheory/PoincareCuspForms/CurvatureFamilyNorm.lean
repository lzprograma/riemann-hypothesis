module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def de2 (X : Data E r) : Wt X.Ψ r := fun _ i => if (i : ℕ) < X.p0 then -1 else 1

def IsGap (X : Data E r) (i j : Fin r) : Prop := (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ X.p0

def rd (X : Data E r) : ℝ := |(discr E : ℝ)| ^ (1 / (2 * (X.Ψ.card : ℝ)))

def RR (X : Data E r) : ℝ := rd X ^ 7

def g0half (r : ℕ) : ℕ := 5 ^ 4 * r

def g0 (r : ℕ) : ℕ := 2 * g0half r

def a1 (X : Data E r) : ℝ := (X.Ψ.card : ℝ) / (5 ^ 4 * rd X ^ 2)

def bb (X : Data E r) : ℝ := 5 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2

def Crh (X : Data E r) : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ)

structure Shape (X : Data E r) : Prop where
  p0_pos : 0 < X.p0
  witt : 2 * X.p0 ≤ r
  r_ge : 8 ≤ r
  D_ge : 2 ≤ nd X

structure Weights (X : Data E r) where
  shape : Shape X
  T : ℕ
  i : ℕ
  c : ℝ
  hW : ℕ
  hF : ℕ
  aK : Wt X.Ψ r
  aW : Wt X.Ψ r
  i_pos : 0 < i
  c_pos : 0 < c
  T_cols : (nd X + 2) * (2 * hW) + 2 * r ≤ T
  T_forty : 40 * (nd X + 2) ≤ T
  T_sq : 11 * nd X ^ 2 ≤ T
  cols_lo : 8 * X.Ψ.card * r + 4 ≤ 2 * hF
  cols_hi : 2 * hF ≤ 2 * hW
  Tcg : (T : ℝ) * c * g0 r ≤ 1
  cRR : (g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X ^ 2 * c ≤ 1
  b_cut : bb X < 3.8 * T - 2 * T
  b_onto : bb X ^ 2 * Crh X + bb X < 1.9 * ((nd X : ℝ) + 2) * T
  gap_big : ∀ τ a b, IsGap X a b →
    ((T : ℤ) + nd X + 2) * ((T : ℤ) + nd X + 2 + 2 * r) ≤ aK τ a - aK τ b + 2
  plus_big : ∀ τ (a : Fin r), (a : ℕ) + 1 = r → 2 * (T : ℤ) ^ 2 ≤ aK τ a
  minus_big : ∀ τ (a : Fin r), (a : ℕ) = 0 → 2 * (T : ℤ) ^ 2 ≤ -aK τ a
  gap_div : ∀ τ a b, IsGap X a b →
    aK τ a - aK τ b + 2 - ((T : ℤ) + nd X + 2) * (aW τ a - aW τ b) ∈ Set.Ico (0 : ℤ) (T + nd X + 2)
  plus_div : ∀ τ (a : Fin r), (a : ℕ) + 1 = r →
    aK τ a - ((T : ℤ) + nd X + 2) * aW τ a - ((nd X : ℤ) + 2) * (2 * hW) - 2 * r ∈
      Set.Ico (0 : ℤ) (T + nd X + 2)
  minus_div : ∀ τ (a : Fin r), (a : ℕ) = 0 →
    -aK τ a - ((T : ℤ) + nd X + 2) * (-aW τ a) ∈ Set.Ico (0 : ℤ) (T + nd X + 2)

def lev (X : Data E r) (x0 : Frame X.Ψ r) (u : Frame X.Ψ r → ℝ) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((u (cpt X x0 y) : ℝ) : ℂ)) z ξ).re

def curv (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  lev X x0 (phla X la) z ξ

def curvDe (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  curv X x0 (de2 X) z ξ / 2

def omRh (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z ξ).re

def IsInv (X : Data E r) (u : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (rmul x b) = u x) ∧ ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, u (lact γ x) = u x

def famNorm (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm la (w j) x ^ 2)

end

end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
