module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

open scoped ContDiff

namespace GlobalTheory.CxForm.FormMul

theorem isForm_mul : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld),
    A.IsForm α → A.IsForm β → A.IsForm (α * β) := by
  intro M _ n A α β hα hβ
  refine ⟨fun i S => ?_, fun x x' h => ?_⟩
  · have e : (fun v => (bas n).repr (A.loc (α * β) i v) S) = fun v => ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
        (bas n).repr (A.loc α i v) p.1 * (bas n).repr (A.loc β i v) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
      funext fun v => by rw [loc_mul, repr_mul]
    rw [e]
    exact ContDiffOn.sum fun p _ => ((hα.smooth i p.1).mul (hβ.smooth i p.2)).mul contDiffOn_const
  · show α x * β x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (α x' * β x')
    rw [map_mul, ← hα.compat x x' h, ← hβ.compat x x' h]

end GlobalTheory.CxForm.FormMul
