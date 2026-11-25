module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Formalism.PeriodIntegrals.UpqRep
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Filter Topology
open scoped Formalism.DoubleCosetMeasures

noncomputable section

namespace GlobalTheory.KFinAvg

instance borelMat (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))

def IsHaarKH (k r : ℕ) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ μ (GlobalTheory.ThA.KH k r)ᶜ = 0 ∧
    (∀ a ∈ GlobalTheory.ThA.KH k r, μ.map (fun g => a * g) = μ) ∧
    ∀ U : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), IsOpen U → 1 ∈ U → 0 < μ U

def peak (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := (1 + (Matrix.trace g).re / n) / 2

def peakN {n : ℕ} (μ : Measure (Matrix (Fin n) (Fin n) ℂ)) (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((peak n g ^ m / ∫ h, peak n h ^ m ∂μ : ℝ) : ℂ)

end GlobalTheory.KFinAvg

namespace GlobalTheory.KFinAvg
open Matrix

theorem isCompact_KH (k r : ℕ) : IsCompact (GlobalTheory.ThA.KH k r) := by
  have hc : IsClosed (PI.UpqRep.UH (PI.UpqRep.Hpk k r)) := by
    show IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  exact (GlobalTheory.isCompact_unitaryGroup (Fin (2 * r + k + 1)) ℂ).inter_left hc

end GlobalTheory.KFinAvg
