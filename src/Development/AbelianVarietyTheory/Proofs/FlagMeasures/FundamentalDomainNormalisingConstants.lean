module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubMemDifferentIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom

noncomputable section

namespace GlobalTheory.CovDom.NormConst

theorem abs_discr_F (D : D7) : |(NumberField.discr D.host.F : ℝ)| = (2 * D.host.v) ^ D.R.f := by
  have h2v : 2 * D.host.v = D.host.rdE := by show 2 * (D.host.rdE / 2) = D.host.rdE; ring
  rw [h2v]
  obtain ⟨h1, -⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hn := GlobalTheory.RealPlaces.finrank_E D
  have hpos : Module.finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  have key : D.host.rdE ^ (2 * D.R.f) = |(NumberField.discr D.host.F : ℝ)| ^ 2 := by
    rw [← hn]
    unfold Formalism.BasicNotions.Host.rdE
    rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
    have h3 : |(NumberField.discr D.host.E : ℝ)| = (NumberField.discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
    rw [h3, sq_abs]
  have hr0 : 0 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.rdE; positivity
  rw [mul_comm, pow_mul] at key
  exact ((pow_left_inj₀ (pow_nonneg hr0 _) (abs_nonneg _) two_ne_zero).1 key).symm

end GlobalTheory.CovDom.NormConst

namespace GlobalTheory.CovDom

end GlobalTheory.CovDom
