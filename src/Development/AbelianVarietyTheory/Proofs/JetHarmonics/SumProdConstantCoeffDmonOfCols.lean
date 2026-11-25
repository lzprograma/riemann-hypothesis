module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.SymbolCols

theorem colM_apply {ι : Type} [Finite ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) (b : Fin n) (l : ι) :
    colM m b l = m (l, b) := by
  simp [colM]

theorem sum_degree_colM {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    ∑ b, (colM m b).degree = m.degree := by
  simp only [Finsupp.degree_eq_sum, colM_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem coeff_mul_congr {k σ : Type} [CommRing k] (N : ℕ) (f g E : MvPowerSeries σ k)
    (h : ∀ mo : σ →₀ ℕ, mo.degree ≤ N → coeff mo f = coeff mo g)
    (mo : σ →₀ ℕ) (hmo : mo.degree ≤ N) : coeff mo (f * E) = coeff mo (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add (f := _)]
  rw [h p.1 (by omega)]

theorem exists_col {ι : Type} [Fintype ι] {n : ℕ} (m a : ι × Fin n →₀ ℕ)
    (hdeg : m.degree = a.degree) (hne : m ≠ a) :
    ∃ b, (colM m b).degree ≤ (colM a b).degree ∧ colM m b ≠ colM a b := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ b, (colM a b).degree ≤ (colM m b).degree := fun b => by
    by_contra h
    have := hcon b (by omega)
    rw [this] at h
    exact h le_rfl
  have hs : ∑ b, (colM a b).degree = ∑ b, (colM m b).degree := by
    rw [sum_degree_colM, sum_degree_colM, hdeg]
  have heq := (Finset.sum_eq_sum_iff_of_le fun b _ => hle b).1 hs
  refine hne (Finsupp.ext fun ⟨l, b⟩ => ?_)
  rw [← colM_apply, ← colM_apply, hcon b (heq b (Finset.mem_univ b)).ge]

end GlobalTheory.SymbolCols
